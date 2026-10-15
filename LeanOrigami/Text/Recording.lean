import LeanOrigami.Scalar
import LeanOrigami.Construction.Checker
import LeanOrigami.Construction.Midpoint
import LeanOrigami.Solvers.Candidates

/-!
# Arithmetic provenance for exact construction export

Recording reuses the ordinary geometric formulas with an instrumented scalar
field. Its operations return exactly the usual scalars; a private runtime log
also remembers how they were calculated. Only newly selected root parameters
become atoms. Earlier coordinates remain arithmetic expressions in those atoms.

The log is untrusted certificate preparation, never proof evidence. The native
hooks may lose events under compiler optimization; missing provenance is an
explicit error. Export checks reconstructed values, and the resulting source
uses the ordinary scalar field and kernel-checked geometric certificates.
There is no global log and no change to Hex or to the mathematical definitions.
-/

namespace LeanOrigami.Text

/-- An arithmetic DAG node. References must name earlier nodes. -/
inductive ArithmeticOp where
  | rational (value : Rat)
  | root
  | add (left right : Nat)
  | sub (left right : Nat)
  | mul (left right : Nat)
  | div (left right : Nat)
  | neg (input : Nat)
  | inv (input : Nat)
  | pow (input exponent : Nat)
  deriving Repr

/-- Exact values paired with their recorded arithmetic, in dependency order. -/
abbrev ArithmeticLog := Array (Scalar × ArithmeticOp)

namespace ArithmeticLog

/-- Find an already recorded exact value, independently of its representation. -/
def find (log : ArithmeticLog) (value : Scalar) : Option Nat :=
  log.findIdx? (fun entry => decide (entry.1 = value))

-- Rational values need no root search or coordinate recovery.
private def rational? (value : Scalar) : Option Rat := do
  guard (value.val.p.natDegree == 1)
  let q : Rat := -(value.val.p.coeff 0 : Rat) / (value.val.p.coeff 1 : Rat)
  guard (decide ((q : Scalar) = value))
  return q

private def locate (ref : IO.Ref ArithmeticLog) (value : Scalar) : BaseIO (Option Nat) := do
  let log ← ref.get
  if let some i := log.find value then return some i
  if let some q := rational? value then
    ref.set (log.push (value, .rational q))
    return some log.size
  return none

private def record (ref : IO.Ref ArithmeticLog) (value : Scalar)
    (op : ArithmeticOp) : BaseIO Unit := do
  if (← locate ref value).isNone then ref.modify (·.push (value, op))

private unsafe def binaryImpl (ref : IO.Ref ArithmeticLog) (op : Nat → Nat → ArithmeticOp)
    (f : Scalar → Scalar → Scalar) (a b : Scalar) : Scalar :=
  let value := f a b
  unsafeBaseIO do
    if let some i ← locate ref a then
      if let some j ← locate ref b then record ref value (op i j)
    return value

private unsafe def unaryImpl (ref : IO.Ref ArithmeticLog) (op : Nat → ArithmeticOp)
    (f : Scalar → Scalar) (a : Scalar) : Scalar :=
  let value := f a
  unsafeBaseIO do
    if let some i ← locate ref a then record ref value (op i)
    return value

-- These hooks are definitionally the original operations. Their runtime
-- implementations only add a best-effort log entry to this recording's ref.
private unsafe def addImpl (r : IO.Ref ArithmeticLog) := binaryImpl r .add (· + ·)
private unsafe def subImpl (r : IO.Ref ArithmeticLog) := binaryImpl r .sub (· - ·)
private unsafe def mulImpl (r : IO.Ref ArithmeticLog) := binaryImpl r .mul (· * ·)
private unsafe def divImpl (r : IO.Ref ArithmeticLog) := binaryImpl r .div (· / ·)
private unsafe def negImpl (r : IO.Ref ArithmeticLog) := unaryImpl r .neg (- ·)
private unsafe def invImpl (r : IO.Ref ArithmeticLog) := unaryImpl r .inv (·⁻¹)
private unsafe def powImpl (r : IO.Ref ArithmeticLog) (a : Scalar) (n : Nat) :=
  unaryImpl r (fun i => .pow i n) (· ^ n) a

@[implemented_by addImpl] private def add (_r : IO.Ref ArithmeticLog) (a b : Scalar) := a + b
@[implemented_by subImpl] private def sub (_r : IO.Ref ArithmeticLog) (a b : Scalar) := a - b
@[implemented_by mulImpl] private def mul (_r : IO.Ref ArithmeticLog) (a b : Scalar) := a * b
@[implemented_by divImpl] private def div (_r : IO.Ref ArithmeticLog) (a b : Scalar) := a / b
@[implemented_by negImpl] private def neg (_r : IO.Ref ArithmeticLog) (a : Scalar) := -a
@[implemented_by invImpl] private def inv (_r : IO.Ref ArithmeticLog) (a : Scalar) := a⁻¹
@[implemented_by powImpl] private def pow (_r : IO.Ref ArithmeticLog) (a : Scalar) (n : Nat) := a ^ n

private abbrev field (ref : IO.Ref ArithmeticLog) : Field Scalar :=
  { (inferInstance : Field Scalar) with
    add := add ref, sub := sub ref, mul := mul ref, div := div ref,
    neg := neg ref, inv := inv ref, npow := fun n a => pow ref a n }

/-- Add a selected root only when it is not already known by arithmetic. -/
private def select (ref : IO.Ref ArithmeticLog) (value : Scalar) : BaseIO Unit :=
  record ref value .root

private def get {α : Type} (result : Except ConstructionError α) : IO α :=
  match result with
  | .ok a => pure a
  | .error e => throw (IO.userError s!"recording: {repr e}")

/-- Recompute one already selected operation using the same candidate formulas.
No new fold is chosen and no solver search is repeated. -/
def step (ref : IO.Ref ArithmeticLog) (state : Program.State Scalar)
    (instruction : Instruction Scalar) : IO (Program.State Scalar) := do
  let object ← get (Program.step state instruction)
  match instruction with
  | .fold request selected =>
    let input ← get (Program.resolve state request)
    let parameter := match input with
      | .axiom5 p _ l =>
        let landing := selected.reflect p
        if l.a = 0 then landing.1 else landing.2
      | _ => selected.b
    match input with
    | .axiom3 .. | .axiom5 .. | .axiom6 .. => select ref parameter
    | _ => pure ()
    -- Inference through the existing inputs can select the ordinary field.
    -- Pass this dictionary explicitly so execution retains the recording hooks.
    let candidates := @FoldInput.rawCandidates Scalar (field ref) inferInstance
      (inferInstance : IsStrictOrderedRing Scalar)
      (fun _ => [parameter]) input
    unless candidates.any (fun l => decide (l = selected)) do
      throw (IO.userError "recording: selected fold could not be reconstructed")
    for value in [selected.a, selected.b, selected.c] do
      if (← locate ref value).isNone then
        throw (IO.userError "recording: missing fold arithmetic")
  | .intersect left right selected =>
    let l ← get (Program.line state left)
    let m ← get (Program.line state right)
    if h : @Line.determinant Scalar (field ref) l m ≠ 0 then do
      let p := @Line.intersection Scalar (field ref) l m h
      unless p = selected do throw (IO.userError "recording: intersection changed")
      for value in [p.1, p.2] do
        if (← locate ref value).isNone then
          throw (IO.userError "recording: missing intersection arithmetic")
    else throw (IO.userError "recording: parallel intersection")
  return state ++ [object]

/-- Record the public midpoint formula directly. This captures arithmetic
provenance without constructing or traversing the recipe's auxiliary creases. -/
def midpoint (ref : IO.Ref ArithmeticLog) (first second : Point Scalar) : IO (Point Scalar) := do
  let output := @Midpoint.point Scalar (field ref) first second
  for value in [output.1, output.2] do
    if (← locate ref value).isNone then
      throw (IO.userError "recording: missing midpoint arithmetic")
  return output

/-- Seed a recording with exact rational coordinates such as the original
points. Nonrational values must already have construction provenance. -/
def seed (ref : IO.Ref ArithmeticLog) (values : List Scalar) : IO Unit := do
  for value in values do
    if (← locate ref value).isNone then
      throw (IO.userError "recording: input has no arithmetic provenance")

/-- Record a saved program, preserving all selected outputs and checking every
instruction. The incremental `step` function is also usable while editing. -/
def ofProgram (program : Program Scalar) : IO ArithmeticLog := do
  let ref ← IO.mkRef (#[] : ArithmeticLog)
  let mut state := Program.initial (K := Scalar)
  for (instruction, index) in program.zipIdx do
    try state ← step ref state instruction
    catch error => throw (IO.userError s!"recording instruction {index+1}: {error}")
  for value in [(0 : Scalar), 1] do discard (locate ref value)
  return ← ref.get

end ArithmeticLog
end LeanOrigami.Text
