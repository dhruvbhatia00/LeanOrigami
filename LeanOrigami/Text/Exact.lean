import LeanOrigami.Text
import LeanOrigami.Text.Coordinates

/-!
# Automatic submission of solver-selected exact programs

Export replays recorded arithmetic in small real number fields and writes
checked isolation data and rational coordinates. Unrelated root constructions
can keep separate fields. The resulting ordinary `Program Scalar` is certified
by `origami_check`; discovery and coordinate preparation are not part of its
proof. Use `Artifact.writeLean` to replay it in a fresh Lean process.
-/

namespace LeanOrigami.Text
open Hex

-- Used both for conditional branches and final equations. Never fall back to
-- evaluating canonical scalar arithmetic when transport was incomplete.
private def decideCoordinates : Lean.Elab.Tactic.TacticM Unit := do
  let target ← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)
  if target.getUsedConstants.any (fun name =>
      [``Scalar, ``realSubfield, ``Scalar.Presentation.scalar,
        ``Scalar.Presentation.hom].contains name) then
    throwError "coordinate conversion left scalar arithmetic: {target}"
  Lean.Elab.Tactic.evalTactic (← `(tactic| decide +kernel))

/-- Certify geometric equations by reducing rational coordinates in the saved
number field. Every Boolean calculation here is checked by the Lean kernel. -/
elab "origami_coordinates " s:term : tactic => Lean.Elab.Tactic.focus do
  Lean.Elab.Tactic.evalTactic (← `(tactic|
  (let : Field ($s).Coordinates := Hex.PolyQuot.field _ _
   try rw [FoldInput.axiom3_iff_two_points]
   try simp only [FoldInput.FiniteCondition, FoldInput.Satisfies,
     FoldInput.axiom6FreeDirection, FoldInput.axiom6Polynomial, Univariate.Cubic.IsZero,
     Line.Contains, Line.Perpendicular, Line.perpendicularAlignmentDot,
     Line.reflect, Line.residual, Line.normalSq, Line.chart, Line.horizontal,
     Line.determinant, Line.intersection, Line.pointAt, Line.perpendicularThrough,
     Line.normalize, Coordinate.get, ne_eq, Prod.ext_iff, Line.ext_iff]
   all_goals try simp (disch := run_tac decideCoordinates) only
     [ite_true, ite_false, ite_eq_left, ite_eq_right, Scalar.Presentation.scalar_eq_hom,
     ← map_zero ($s).hom, ← map_one ($s).hom, ← map_ofNat ($s).hom,
     ← map_add, ← map_sub, ← map_mul, ← map_div₀, ← map_neg, ← map_inv₀, ← map_pow,
     RingHom.injective ($s).hom |>.eq_iff])))
  Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals run_tac decideCoordinates))

private def fieldName (i : Nat) : String := if i == 0 then "field" else s!"field{i}"

private def fieldSource (field : Scalar.Presentation) : String :=
  let rep := field.isolation
  s!"⟨{repr field.polynomial}, ⟨by decide +kernel, by decide +kernel⟩, " ++
    s!"⟨⟨{Display.square rep.1.square}, {Display.certificate rep.1.witness}⟩, by decide +kernel⟩, by decide +kernel⟩"

private def artifact (table : CoordinateTable) (program : Program Scalar)
    (point : PointRef) (coordinate : Coordinate) (target : Scalar) : Except String Artifact := do
  let scalar (a : Scalar) : Except String String := do
    let some (_, saved) := table.entries.find? (fun entry => decide (entry.1 = a))
      | throw "missing saved coordinate"
    match saved with
    | .rational q => return s!"(({q.num} : Scalar) / {q.den})"
    | .coordinate i coeffs =>
      return s!"({fieldName i}.scalar (Hex.PolyQuot.reduce _ _ ({repr coeffs})))"
  let mut steps : List String := []
  for instruction in program do
    match instruction with
    | .fold request l =>
      let line ← if l.a == 1 then do
          pure s!"⟨1, {← scalar l.b}, {← scalar l.c}, Or.inl rfl⟩"
        else do
          unless l.a == 0 && l.b == 1 do throw "line is not normalized"
          pure s!"⟨0, 1, {← scalar l.c}, Or.inr ⟨rfl, rfl⟩⟩"
      steps := s!".fold ({repr request}) ({line})" :: steps
    | .intersect l r p =>
      steps := s!".intersect ⟨{l.index}⟩ ⟨{r.index}⟩ ({← scalar p.1}, {← scalar p.2})" :: steps
  let declarations := table.fields.toList.zipIdx |>.map fun (field, i) =>
    s!"def {fieldName i} : Scalar.Presentation := {fieldSource field}\n\n"
  let tactics := (List.range table.fields.size).map fun i =>
    s!"origami_coordinates {fieldName i}"
  let proof := "first | " ++ String.intercalate " | " tactics
  let coordinateSource := match coordinate with | .x => ".x" | .y => ".y"
  let source := "import LeanOrigami.Text.Exact\n\nopen LeanOrigami LeanOrigami.Text Hex\n" ++
    "namespace SavedOrigami\nset_option maxRecDepth 8192\nset_option maxHeartbeats 4000000\nset_option exponentiation.threshold 8192\n\n" ++
    String.join declarations ++
    "def program : Program Scalar := [\n  " ++ String.intercalate ",\n  " steps.reverse ++ "]\n\n" ++
    s!"def target : Scalar := {← scalar target}\n\n" ++
    s!"theorem accepted : Program.accepts program ⟨{point.index}⟩ {coordinateSource} target = true := by\n" ++
    s!"  unfold program target\n  origami_check using {proof}\n\n" ++
    "theorem submitted : ConstructibleNumber (Scalar.toReal target) :=\n" ++
    s!"  Program.accepts_sound Scalar.realHom program ⟨{point.index}⟩ {coordinateSource} target accepted\n\n" ++
    "#print axioms accepted\n#print axioms submitted\nend SavedOrigami\n"
  return ⟨1, "SavedOrigami.submitted", source⟩

/-- Prepare a standalone certificate for actual exact choices. A caller that
records steps while editing can supply that arithmetic log; otherwise export
records the saved steps first. Native success is not certification: compile
and kernel-check the returned artifact. Every reconstructed coordinate must
match its saved exact scalar, even when a caller supplies an untrusted log. -/
def exportExact (program : Program Scalar) (point : PointRef)
    (coordinate : Coordinate) (target : Scalar) (recording : Option ArithmeticLog := none) :
    IO (Except String Artifact) := do
  unless Program.accepts program point coordinate target do
    return .error "the saved program does not accept the selected target"
  try
    let log ← match recording with
      | some log => pure log
      | none => ArithmeticLog.ofProgram program
    return do
      let table ← CoordinateTable.prepare log program target
      artifact table program point coordinate target
  catch error => return .error error.toString

end LeanOrigami.Text
