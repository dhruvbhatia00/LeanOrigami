import LeanOrigami.Text.Recording
import LeanOrigami.Scalar.Presentation
import HexNumberField.CommonField

/-!
# Small field certificates from recorded arithmetic

Only root parameters need coordinate recovery. All other coordinates are
calculated by replaying the arithmetic DAG in reduced polynomial arithmetic.
Fields are shared by connected construction steps, not by unrelated roots.
-/

namespace LeanOrigami.Text
open Hex

/-- A saved scalar is either rational or a coordinate in one certificate field. -/
inductive SavedScalar where
  | rational (value : Rat)
  | coordinate (field : Nat) (coefficients : DensePoly Rat)

/-- Checked preparations for serialization; correctness is checked again by
compiling the exported geometric proof, not trusted from this data structure. -/
structure CoordinateTable where
  fields : Array Scalar.Presentation
  entries : List (Scalar × SavedScalar)

namespace CoordinateTable

private def operands : ArithmeticOp → List Nat
  | .add i j | .sub i j | .mul i j | .div i j => [i, j]
  | .neg i | .inv i | .pow i _ => [i]
  | _ => []

private def dependencies (log : ArithmeticLog) : Except String (Array (List Nat)) := do
  let mut out := #[]
  for (_, op) in log do
    let mut roots := []
    if let .root := op then roots := [out.size]
    for i in operands op do
      let some earlier := out[i]? | throw "arithmetic log contains a forward reference"
      roots := (roots ++ earlier).dedup
    out := out.push roots
  return out

private def lineValues (l : Line Scalar) : List Scalar := [l.a, l.b, l.c]
private def pointValues (p : Point Scalar) : List Scalar := [p.1, p.2]

/-- Exact coefficients explicitly selected by an instruction. -/
def instructionValues : Instruction Scalar → List Scalar
  | .fold _ l => lineValues l
  | .intersect _ _ p => pointValues p

private def inputValues : FoldInput Scalar → List Scalar
  | .axiom1 p q | .axiom2 p q => pointValues p ++ pointValues q
  | .axiom3 l m => lineValues l ++ lineValues m
  | .axiom4 p l => pointValues p ++ lineValues l
  | .axiom5 p q l => pointValues p ++ pointValues q ++ lineValues l
  | .axiom6 p q l m => pointValues p ++ pointValues q ++ lineValues l ++ lineValues m
  | .axiom7 p l m => pointValues p ++ lineValues l ++ lineValues m

private def rootsFor (log : ArithmeticLog) (deps : Array (List Nat))
    (values : List Scalar) : Except String (List Nat) := do
  let mut roots := []
  for value in values do
    let some i := log.find value | throw "missing coordinate provenance"
    let some ids := deps[i]? | throw "missing arithmetic dependencies"
    roots := (roots ++ ids).dedup
  return roots

private def merge (groups : List (List Nat)) (roots : List Nat) : List (List Nat) :=
  if roots.isEmpty then groups else
    let (joined, separate) := groups.partition (fun group => group.any roots.contains)
    (roots ++ joined.flatten).dedup :: separate

private def groups (log : ArithmeticLog) (deps : Array (List Nat))
    (program : Program Scalar) : Except String (List (List Nat)) := do
  let mut state := Program.initial (K := Scalar)
  let mut groups := []
  for instruction in program do
    let (values, object) ← match instruction with
      | .fold request selected => do
        let input ← (Program.resolve state request).mapError reprStr
        pure (inputValues input ++ lineValues selected, Object.line selected)
      | .intersect l m p => do
        let left ← (Program.line state l).mapError reprStr
        let right ← (Program.line state m).mapError reprStr
        pure (lineValues left ++ lineValues right ++ pointValues p, Object.point p)
    groups := merge groups (← rootsFor log deps values)
    state := state ++ [object]
  return if groups.isEmpty then [[]] else groups

-- Try a largest-degree selected root before adjoining another generator. This
-- is membership recovery for root parameters only, never for every coordinate.
private def present (roots : Array AlgebraicNumber) : QAdjoin.Presentation := Id.run do
  if roots.isEmpty then return QAdjoin.common #[]
  if roots.size == 1 then
    let generator := roots[0]!
    return ⟨generator, #[generator.toQAdjoin]⟩
  let sorted := roots.qsort (fun a b => a.p.natDegree > b.p.natDegree)
  let generator := sorted[0]!
  let recovered := QAdjoin.ofAlgebraics? generator roots
  if recovered.all Option.isSome then
    return ⟨generator, recovered.filterMap id⟩
  return QAdjoin.common roots

private def evaluate (field : Scalar.Presentation) (log : ArithmeticLog)
    (atoms : List (Nat × field.Coordinates)) : Array (Option field.Coordinates) := Id.run do
  let mut out : Array (Option field.Coordinates) := #[]
  for (_, op) in log do
    let get (i : Nat) := (out[i]?).join
    let value : Option field.Coordinates := match op with
      | .rational q => some (PolyQuot.ofRat q)
      | .root => (atoms.find? (fun entry => entry.1 == out.size)).map Prod.snd
      | .add i j => return PolyQuot.add (← get i) (← get j)
      | .sub i j => return PolyQuot.sub (← get i) (← get j)
      | .mul i j => return PolyQuot.mul (← get i) (← get j)
      | .div i j => return PolyQuot.div (← get i) (← get j)
      | .neg i => return PolyQuot.neg (← get i)
      | .inv i => return PolyQuot.inv (← get i)
      | .pow i n => return PolyQuot.natPow (← get i) n
    out := out.push value
  return out

/-- Reconstruct every selected coordinate exactly, using arithmetic rather than
canonical-number power tables for intermediate expressions. -/
def prepare (log : ArithmeticLog) (program : Program Scalar) (target : Scalar) :
    Except String CoordinateTable := do
  let deps ← dependencies log
  let groups ← groups log deps program
  let values := (target :: program.flatMap instructionValues).dedup
  let mut fields : Array Scalar.Presentation := #[]
  let mut entries : List (Scalar × SavedScalar) := []
  for ids in groups do
    let roots ← ids.toArray.mapM fun i => do
      let some (value, _) := log[i]? | throw "missing selected root"
      pure value.val
    let common := present roots
    let field : Scalar.Presentation ←
      if h : common.generator.rep.1.square.meetsRealAxis = true then
        pure ⟨common.generator.p, common.generator.checked, common.generator.rep, h⟩
      else throw "certificate field is not real"
    unless common.entries.size == ids.length do throw "root coordinate recovery failed"
    let atoms := ids.zip (common.entries.toList.map fun value =>
      PolyQuot.reduce field.polynomial (SimpleRoot.mk field.isolation) value.coeffs)
    let coordinates := evaluate field log atoms
    for value in values do
      if entries.any (fun entry => decide (entry.1 = value)) then continue
      let some i := log.find value | throw "missing saved coordinate"
      let some (some coordinate) := coordinates[i]? | continue
      unless field.scalar coordinate = value do
        throw "recorded arithmetic changed an exact selected coordinate"
      let saved := match log[i]? with
        | some (_, .rational q) => SavedScalar.rational q
        | _ => .coordinate fields.size coordinate.coeffs
      entries := (value, saved) :: entries
    fields := fields.push field
  unless entries.length == values.length do throw "certificate fields omit a selected coordinate"
  return ⟨fields, entries⟩

end CoordinateTable
end LeanOrigami.Text
