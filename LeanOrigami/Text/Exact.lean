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
  (let : Hex.ZPoly.CheckedIrreducible ($s).polynomial := ($s).checked
   let : Field ($s).Coordinates := Hex.PolyQuot.field _ _
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
     ← map_ratCast ($s).hom,
     ← map_add, ← map_sub, ← map_mul, ← map_div₀, ← map_neg, ← map_inv₀, ← map_pow,
     RingHom.injective ($s).hom |>.eq_iff])))
  Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals run_tac decideCoordinates))

private def fieldName (i : Nat) : String := if i == 0 then "field" else s!"field{i}"

private def fieldSource (field : Scalar.Presentation) : String :=
  let rep := field.isolation
  s!"⟨{repr field.polynomial}, ⟨by decide +kernel, by decide +kernel⟩, " ++
    s!"⟨⟨{(Display.square rep.1.square).replace ": Dyadic" ": _root_.Dyadic"}, {(Display.certificate rep.1.witness).replace ": Dyadic" ": _root_.Dyadic"}⟩, by decide +kernel⟩, by decide +kernel⟩"

/-- Serialized exact data shared by standalone files and local proof expressions. -/
structure CertificateSource where
  fields : List (String × String)
  program : String
  target : String
  acceptance : String
  conclusion : String

private def certificate (table : CoordinateTable) (program : Program Scalar)
    (point : PointRef) (coordinate : Coordinate) (target : Scalar) : Except String CertificateSource := do
  let scalar (a : Scalar) : Except String String := do
    let some (_, saved) := table.entries.find? (fun entry => decide (entry.1 = a))
      | throw "missing saved coordinate"
    match saved with
    | .rational q => return s!"(({q.num} : LeanOrigami.Scalar) / {q.den})"
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
  let fields := table.fields.toList.zipIdx |>.map fun (field, i) =>
    (fieldName i, fieldSource field)
  let coordinateSource := match coordinate with | .x => ".x" | .y => ".y"
  return {
    fields
    program := "[\n  " ++ String.intercalate ",\n  " steps.reverse ++ "]"
    target := ← scalar target
    acceptance := s!"LeanOrigami.Program.accepts program ⟨{point.index}⟩ {coordinateSource} target = true"
    conclusion := s!"LeanOrigami.Program.accepts_sound LeanOrigami.Scalar.realHom program ⟨{point.index}⟩ {coordinateSource} target accepted"
  }

/-- The certificate's arithmetic tactic, shared by acceptance and target matching. -/
def CertificateSource.arithmetic (source : CertificateSource) : String :=
  "first | " ++ String.intercalate " | " (source.fields.map fun (name, _) =>
    s!"origami_coordinates {name}")

/-- Ordinary standalone Lean source, independent of any editing session. -/
def CertificateSource.artifact (source : CertificateSource) : Artifact :=
  let declarations := source.fields.map fun (name, value) =>
    s!"def {name} : Scalar.Presentation := {value}\n\n"
  let text := "import LeanOrigami.Text.Exact\n\nopen LeanOrigami LeanOrigami.Text Hex\n" ++
    "namespace SavedOrigami\nset_option maxRecDepth 8192\nset_option maxHeartbeats 4000000\nset_option exponentiation.threshold 8192\n\n" ++
    String.join declarations ++
    s!"def program : Program Scalar := {source.program}\n\n" ++
    s!"def target : Scalar := {source.target}\n\n" ++
    s!"theorem accepted : {source.acceptance} := by\n" ++
    s!"  unfold program target\n  origami_check using {source.arithmetic}\n\n" ++
    "theorem submitted : ConstructibleNumber (Scalar.toReal target) :=\n" ++
    s!"  {source.conclusion}\n\n" ++
    "#print axioms accepted\n#print axioms submitted\nend SavedOrigami\n"
  ⟨1, "SavedOrigami.submitted", text⟩

/-- An expression sharing the exact program and its acceptance certificate.
The continuation can return a proof or a persistent, editable construction. -/
def CertificateSource.expression (source : CertificateSource) (finish : String) : String :=
  let declarations := source.fields.map fun (name, value) =>
    s!"  let {name} : LeanOrigami.Scalar.Presentation := {value}\n"
  "set_option maxRecDepth 8192 in\nset_option maxHeartbeats 4000000 in\n" ++
    "set_option exponentiation.threshold 8192 in\nopen LeanOrigami LeanOrigami.Text Hex in\nby\n" ++ String.join declarations ++
    s!"  let program : LeanOrigami.Program LeanOrigami.Scalar := {source.program}\n" ++
    s!"  let target : LeanOrigami.Scalar := {source.target}\n" ++
    s!"  have accepted : {source.acceptance} := by\n" ++
    s!"    dsimp only [program, target]\n    origami_check using {source.arithmetic}\n" ++
    "  " ++ finish.replace "\n" "\n  " ++ "\n"

/-- A local proof body with the same exact data as a standalone artifact.
The caller supplies a final goal-matching tactic, which Lean must check. -/
def CertificateSource.proof (source : CertificateSource) (finish : String) : String :=
  source.expression (s!"have constructed := {source.conclusion}\n" ++ finish)

/-- Prepare a standalone certificate for actual exact choices. A caller that
records steps while editing can supply that arithmetic log; otherwise export
records the saved steps first. Native success is not certification: compile
and kernel-check the returned artifact. Every reconstructed coordinate must
match its saved exact scalar, even when a caller supplies an untrusted log. -/
def prepareExact (program : Program Scalar) (point : PointRef)
    (coordinate : Coordinate) (target : Scalar) (recording : Option ArithmeticLog := none) :
    IO (Except String CertificateSource) := do
  unless Program.accepts program point coordinate target do
    return .error "the saved program does not accept the selected target"
  try
    let log ← match recording with
      | some log => pure log
      | none => ArithmeticLog.ofProgram program
    return do
      let table ← CoordinateTable.prepare log program target
      certificate table program point coordinate target
  catch error => return .error error.toString

/-- Export the shared exact certificate as a standalone Lean artifact. -/
def exportExact (program : Program Scalar) (point : PointRef)
    (coordinate : Coordinate) (target : Scalar) (recording : Option ArithmeticLog := none) :
    IO (Except String Artifact) := do
  return (← prepareExact program point coordinate target recording).map CertificateSource.artifact

end LeanOrigami.Text
