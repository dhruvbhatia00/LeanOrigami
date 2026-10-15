import LeanOrigami.Widget.Session
import LeanOrigami.Text.Exact
import LeanOrigami.Widget.Certificate

/-!
# Persistent visual constructions

A saved construction contains one exact program and the evidence checked by
the kernel. The editor reconstructs its objects from that same program. Native
evaluation is used only to reopen the drawing, never to establish soundness.
-/

namespace LeanOrigami.Widget

/-- Source-persistent construction data, acceptance, and identification with
the theorem's real target. No process-local widget references are stored. -/
structure SavedConstruction (value : ℝ) where
  program : Program Scalar
  point : PointRef
  coordinate : Coordinate
  target : Scalar
  accepted : Program.accepts program point coordinate target = true
  identified : Scalar.toReal target = value

/-- The ordinary program checker and target identity justify a saved tactic. -/
theorem SavedConstruction.sound {value : ℝ} (saved : SavedConstruction value) :
    ConstructibleNumber value :=
  saved.identified ▸ Program.accepts_sound Scalar.realHom saved.program
    saved.point saved.coordinate saved.target saved.accepted

/-- Serialize a saved construction using the existing exact certificate data.
The surrounding tactic supplies its expected real target. -/
def savedSource (certificate : Text.CertificateSource) (point : Nat)
    (coordinate : Coordinate) : String :=
  let axis := match coordinate with | .x => "x" | .y => "y"
  certificate.expression (
    s!"refine ⟨program, ⟨{point}⟩, .{axis}, target, accepted, ?_⟩\n" ++
    s!"origami_identify target using {certificate.arithmetic}")

/-- A retained call tree and its certificate share one definition-derived registry.
The final public state is kept explicitly to avoid replaying geometry on reopening. -/
structure SavedComposition (value : ℝ) where
  history : Execution.History Scalar
  final : Program.State Scalar
  point : PointRef
  coordinate : Coordinate
  target : Scalar
  certified : Composition.Certified (Execution.registry history) Program.initial
    (Execution.construction history) final
  selected : ∃ p, final[point.index]? = some (.point p) ∧ coordinate.get p = target
  identified : Scalar.toReal target = value

/-- Recipe calls use their registered theorem; primitive leaves use the same
geometric checker as legacy saved constructions. -/
theorem SavedComposition.sound {value : ℝ} (saved : SavedComposition value) :
    ConstructibleNumber value := by
  obtain ⟨point, selected, equal⟩ := saved.selected
  exact saved.identified ▸ saved.certified.coordinate_sound Scalar.realHom
    saved.point.index point saved.coordinate saved.target selected equal

open Lean Meta

-- This evaluator is deliberately outside the certification path. Its result
-- feeds an editable session; every subsequent save is proved afresh.
private unsafe def reopenUnsafe (saved : Expr) : MetaM (Except String (Session × Nat × Coordinate)) := do
  -- Reduce projections before compilation: the certificate's real parameter
  -- must not become a runtime argument, even though it appears only in types.
  let project (name : Name) := do
    whnf (← mkAppM name #[saved])
  let program ← project ``SavedConstruction.program
  let point ← project ``SavedConstruction.point
  let coordinate ← project ``SavedConstruction.coordinate
  let index ← whnf (← mkAppM ``PointRef.index #[point])
  let expression ← mkAppM ``Prod.mk #[program, ← mkAppM ``Prod.mk #[index, coordinate]]
  let expression ← zetaReduce (← instantiateMVars expression)
  let (program, point, coordinate) ←
    evalExpr (Program Scalar × Nat × Coordinate) (← inferType expression) expression
  return do
    return (← Session.ofProgram program, point, coordinate)

/-- Execute saved data for display. The proof-producing tactic never calls this
function; only the RPC that opens the panel does. -/
@[implemented_by reopenUnsafe]
opaque reopen (saved : Expr) : MetaM (Except String (Session × Nat × Coordinate))

private unsafe def reopenCompositionUnsafe (saved : Expr) :
    MetaM (Except String (Session × Nat × Coordinate)) := do
  let project (name : Name) := do
    whnf (← mkAppM name #[saved])
  let history ← project ``SavedComposition.history
  let point ← project ``SavedComposition.point
  let coordinate ← project ``SavedComposition.coordinate
  let index ← whnf (← mkAppM ``PointRef.index #[point])
  let expression ← mkAppM ``Prod.mk #[history, ← mkAppM ``Prod.mk #[index, coordinate]]
  let expression ← zetaReduce (← instantiateMVars expression)
  let (history, point, coordinate) ←
    evalExpr (Execution.History Scalar × Nat × Coordinate) (← inferType expression) expression
  return do
    let objects ← (Execution.replay Program.initial history).mapError errorMessage
    return ({ program := history, objects, groups := Execution.groups 2 history }, point, coordinate)

/-- Reopen only computational data. Certificates are used by `sound`, not by
native evaluation. Private recipe histories remain available for inspection. -/
@[implemented_by reopenCompositionUnsafe]
opaque reopenComposition (saved : Expr) : MetaM (Except String (Session × Nat × Coordinate))

end LeanOrigami.Widget
