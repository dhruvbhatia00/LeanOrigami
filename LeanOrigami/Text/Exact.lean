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

/-- Shared finite budget for exported certificates and editor proof checking.
The general trisection recipe exceeds the former four-million-heartbeat limit;
both entry points must allow the same work, without relaxing proof checking. -/
def certificateHeartbeats : Nat := 16000000

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
     Line.normalize, Coordinate.get, ne_eq, Prod.ext_iff, Line.ext_iff,
     List.cons.injEq, Object.point.injEq, Object.line.injEq, and_true]
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

/-- Serialize one exact scalar using the certificate's shared field table. -/
def CoordinateTable.scalarSource (table : CoordinateTable) (a : Scalar) : Except String String := do
  let some (_, saved) := table.entries.find? (fun entry => decide (entry.1 = a))
    | throw "missing saved coordinate"
  match saved with
  | .rational q =>
    if q.den == 1 then return s!"({q.num} : LeanOrigami.Scalar)"
    return s!"(({q.num} : LeanOrigami.Scalar) / {q.den})"
  | .coordinate i coeffs =>
    return s!"({fieldName i}.scalar (Hex.PolyQuot.reduce _ _ ({repr coeffs})))"

/-- A point keeps exact coordinates; display approximations never enter source. -/
def CoordinateTable.pointSource (table : CoordinateTable) (point : Point Scalar) : Except String String := do
  return s!"({← table.scalarSource point.1}, {← table.scalarSource point.2})"

/-- Serialize normalized line coefficients and their normalization witness. -/
def CoordinateTable.lineSource (table : CoordinateTable) (line : Line Scalar) : Except String String := do
  if line.a == 1 then
    return s!"⟨1, {← table.scalarSource line.b}, {← table.scalarSource line.c}, Or.inl rfl⟩"
  unless line.a == 0 && line.b == 1 do throw "line is not normalized"
  return s!"⟨0, 1, {← table.scalarSource line.c}, Or.inr ⟨rfl, rfl⟩⟩"

/-- Serialize an object at either a public or a private recipe boundary. -/
def CoordinateTable.objectSource (table : CoordinateTable) : Object Scalar → Except String String
  | .point point => return s!".point ({← table.pointSource point})"
  | .line line => return s!".line ({← table.lineSource line})"

/-- Primitive instructions share one serializer across both saved formats. -/
def CoordinateTable.instructionSource (table : CoordinateTable) : Instruction Scalar → Except String String
  | .fold request line => return s!".fold ({repr request}) ({← table.lineSource line})"
  | .intersect left right point =>
    return s!".intersect ⟨{left.index}⟩ ⟨{right.index}⟩ ({← table.pointSource point})"

/-- Declarations needed by every serialized coordinate in this table. -/
def CoordinateTable.fieldSources (table : CoordinateTable) : List (String × String) :=
  table.fields.toList.zipIdx |>.map fun (field, i) => (fieldName i, fieldSource field)

private def certificate (table : CoordinateTable) (program : Program Scalar)
    (point : PointRef) (coordinate : Coordinate) (target : Scalar) : Except String CertificateSource := do
  let steps ← program.mapM table.instructionSource
  let fields := table.fieldSources
  let coordinateSource := match coordinate with | .x => ".x" | .y => ".y"
  return {
    fields
    program := "[\n  " ++ String.intercalate ",\n  " steps ++ "]"
    target := ← table.scalarSource target
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
    s!"namespace SavedOrigami\nset_option maxRecDepth 8192\nset_option maxHeartbeats {certificateHeartbeats}\nset_option exponentiation.threshold 8192\n\n" ++
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
  s!"set_option maxRecDepth 8192 in\nset_option maxHeartbeats {certificateHeartbeats} in\n" ++
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
