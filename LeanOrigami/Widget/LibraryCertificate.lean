import LeanOrigami.Widget.LibraryDiscovery
import LeanOrigami.Text.Exact
import LeanOrigami.Scalar.Bounds

/-!
# Small certificates for public library outputs

Record the same formulas used by preview, then serialize witnesses and proofs of
polynomial equations and branch inequalities. Private fold histories never enter
this preparation. All generated source still requires ordinary kernel checking.
-/

namespace LeanOrigami.Widget.LibraryRecipe
open Text

open Lean Elab Tactic in
/-- Normalize public library formulas and choose a number field for the remaining
coordinate equations. Keeping the search here avoids emitting unused fallback
tactics into every saved proof. Every successful attempt still constructs a
kernel-checked coordinate proof. -/
elab "origami_library_arithmetic" "[" fields:term,* "]" : tactic => do
  evalTactic (← `(tactic| try dsimp only [ArithmeticOperation.Valid,
    ArithmeticOperation.value, MeasurementOperation.value, Midpoint.point,
    DistanceRecipe.squared, Trisection.Roots.cosine, Trisection.unitVector,
    Point.dot, Point.sqNorm, Prod.fst_sub, Prod.snd_sub]))
  if (← getGoals).isEmpty then return
  let initial ← saveState
  for field in fields.getElems do
    try
      evalTactic (← `(tactic| origami_coordinates $field))
      return
    catch _ => initial.restore
  throwError "No saved number field could certify these library coordinates."

/-- Record public formulas with the instrumented field, selecting only genuinely
new root atoms. The returned witnesses are ephemeral certificate data. -/
def record (recipe : LibraryRecipe) (log : IO.Ref ArithmeticLog)
    (inputs : Program.State Scalar) : IO (Discovery Scalar) := do
  let select (coefficients : List Scalar) (branch : Scalar → Bool) : ExceptT String IO Scalar := do
    let root ← liftExcept (chooseRoot coefficients branch)
    ArithmeticLog.select log root
    return root
  let result ← (@discover Scalar (ArithmeticLog.field log) inferInstance
    (ExceptT String IO) inferInstance inferInstance recipe select inputs).run
  match result with
  | .ok found => return found
  | .error message => throw (IO.userError message)

-- Zero needs an equation, not a shrinking enclosure. Every other requested sign
-- is positive; the same strict enclosure also proves weak inequalities.
private def separated (table : CoordinateTable) (values : List Scalar) (bits : Nat) : Bool :=
  values.all fun value =>
    if value = 0 then true else
    match table.entries.find? (fun entry => decide (entry.1 = value)) with
    | some (_, .rational q) => decide (0 < q)
    | some (_, .coordinate i coefficients) =>
      match table.fields[i]? with
      | none => false
      | some field =>
        let ball := Hex.PolyQuot.evalRatBall coefficients field.isolation.1.square bits
        decide (ball.radius < ball.re)
    | none => false

/-- Refine saved isolating regions until all nonzero sign witnesses are separated
from zero. Refinement preserves each root; exported bounds are checked anew. -/
partial def refineSigns (table : CoordinateTable) (values : List Scalar)
    (bits : Nat := 64) : Except String (CoordinateTable × Nat) := do
  unless values.all (fun value => decide (0 ≤ value)) do
    throw "A library branch has a negative sign witness."
  unless values.all (fun value => table.entries.any (fun entry => decide (entry.1 = value))) do
    throw "A library branch is missing a saved sign witness."
  if separated table values bits then return (table, bits)
  let fields ← table.fields.mapM fun field => do
    let some refined := field.isolation.refineTo? (bits : Int)
      | throw "Could not refine a certificate's root enclosure."
    if h : refined.val.1.square.meetsRealAxis = true then
      pure ({ field with isolation := refined.val, real := h } : Scalar.Presentation)
    else throw "Refinement lost the real root enclosure."
  refineSigns { table with fields } values (2 * bits)

/-- Propose a sign proof from rational arithmetic or a checked rational ball.
The caller determines whether the mathematical branch needs a strict sign. -/
def signSource (table : CoordinateTable) (arithmetic : String) (bits : Nat)
    (value : Scalar) (strict : Bool) : Except String String := do
  let source ← table.scalarSource value
  if value = 0 then
    if strict then throw "A strict library branch witness is zero."
    return s!"have hzero : {source} = 0 := by {arithmetic}\n" ++
      "simpa only [hzero] using (le_refl (0 : Scalar))"
  let some (_, saved) := table.entries.find? (fun entry => decide (entry.1 = value))
    | throw "Missing sign coordinate."
  match saved with
  | .rational _ => return "norm_num"
  | .coordinate .. =>
    let theoremName := if strict then "coordinate_pos" else "coordinate_nonneg"
    return s!"apply Scalar.Presentation.{theoremName} _ _ {bits}\ndecide +kernel"

private def point (inputs : Program.State Scalar) (index : Nat) : Except String (Point Scalar) :=
  match inputs[index]? with
  | some (.point p) => .ok p
  | _ => .error "Missing library point input."

private def indent (source : String) : String := "  " ++ source.replace "\n" "\n  "

/-- Proof of the public-output relation. Existential witnesses and branch facts
are explicit; all remaining scalar equations use number-field reflection. -/
def certificateSource (recipe : LibraryRecipe) (table : CoordinateTable)
    (arithmetic : String) (bits : Nat) (inputs : Program.State Scalar)
    (found : Discovery Scalar) : Except String String := do
  match recipe with
  | .midpoint =>
    let p ← table.pointSource (← point inputs 0)
    let q ← table.pointSource (← point inputs 1)
    return s!"refine ⟨{p}, {q}, rfl, ?_, ?_⟩\n· {arithmetic}\n" ++
      s!"· {arithmetic}"
  | .arithmetic op =>
    let x ← table.scalarSource (← point inputs 5).1
    let y ← if op.arity == 7 then table.scalarSource (← point inputs 6).1
      else pure "(0 : Scalar)"
    return s!"refine ⟨{x}, {y}, rfl, ?_, ?_⟩\n" ++
      s!"· {arithmetic}\n" ++
      s!"· {arithmetic}"
  | .measurement op =>
    let p ← table.pointSource (← point inputs 5)
    let q ← if op.arity == 7 then table.pointSource (← point inputs 6)
      else pure "((0, 0) : Point Scalar)"
    let [root] := found.witnesses | throw "Missing measurement root witness."
    let t ← table.scalarSource root
    let preamble := s!"refine ⟨{p}, {q}, {t}, rfl, ?_, ?_, ?_⟩\n"
    let output := s!"· {arithmetic}"
    match op with
    | .sqrt =>
      let positive ← signSource table arithmetic bits root false
      return s!"have nonneg : 0 ≤ {t} := by\n{indent positive}\n" ++
        s!"have square : {t} ^ 2 = ({p}).1 := by {arithmetic}\n" ++ preamble ++
        "· refine ⟨?_, ?_⟩\n" ++ s!"  · {arithmetic}\n" ++
        s!"  · exact (sq_nonneg {t}).trans_eq square\n" ++
        "· exact ⟨nonneg, square⟩\n" ++ output
    | .cbrt => return preamble ++ s!"· change ({p}).2 = 0\n  {arithmetic}\n" ++
        s!"· change {t} ^ 3 = ({p}).1\n  {arithmetic}\n" ++ output
    | .distanceX | .distanceY =>
      let positive ← signSource table arithmetic bits root false
      return s!"have nonneg : 0 ≤ {t} := by\n{indent positive}\n" ++ preamble ++
        "· trivial\n· refine ⟨nonneg, ?_⟩\n" ++
        s!"  {arithmetic}\n" ++ output
    | _ => return preamble ++ "· trivial\n· trivial\n" ++ output
  | .trisection =>
    let v ← table.pointSource (← point inputs 5)
    let p ← table.pointSource (← point inputs 6)
    let q ← table.pointSource (← point inputs 7)
    let [a, b, s, t, r] := ← found.witnesses.mapM table.scalarSource
      | throw "Missing trisection root witnesses."
    let mut preamble := s!"let roots : Trisection.Roots Scalar := ⟨{a}, {b}, {s}, {t}, {r}⟩\n"
    let [_, _, _, lowerValue, upperValue, _] := found.signs
      | throw "Missing trisection branch witnesses."
    for (value, i) in found.signs.zipIdx do
      let source ← table.scalarSource value
      let proof ← signSource table arithmetic bits value true
      preamble := preamble ++ s!"have sign{i} : 0 < {source} := by\n{indent proof}\n"
    let low ← table.scalarSource lowerValue
    let high ← table.scalarSource upperValue
    preamble := preamble ++ s!"have lower : (1/2 : Scalar) < {t} := by\n" ++
      s!"  apply sub_pos.mp\n  have eq : {t} - 1/2 = {low} := by {arithmetic}\n" ++
      "  rw [eq]; exact sign3\n" ++
      s!"have upper : {t} < (1 : Scalar) := by\n" ++
      s!"  apply sub_pos.mp\n  have eq : 1 - {t} = {high} := by {arithmetic}\n" ++
      "  rw [eq]; exact sign4\n"
    return preamble ++ s!"have valid : roots.Valid {v} {p} {q} := by\n" ++
      "  dsimp only [Trisection.Roots.Valid, roots]\n" ++
      "  refine ⟨sign0, ?_, sign1, ?_, sign2, ?_, lower, upper, ?_, sign5, ?_⟩\n" ++
      indent ("all_goals\n" ++ indent arithmetic) ++ "\n" ++
      s!"refine ⟨{v}, {p}, {q}, roots, valid, rfl, ?_⟩\n" ++
      "dsimp only [LibraryRecipe.trisectionOutputs, Trisection.Roots.firstPoint,\n" ++
      "  Trisection.Roots.secondPoint, Trisection.Roots.perpendicularUnit,\n" ++
      "  Trisection.Roots.cosine, Trisection.unitVector, Point.dot, roots, Line.through]\n" ++ arithmetic

end LeanOrigami.Widget.LibraryRecipe
