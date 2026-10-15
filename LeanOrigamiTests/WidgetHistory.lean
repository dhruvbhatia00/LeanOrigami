import LeanOrigami.Widget.Session

/-!
# History references for visual inspection

History metadata preserves the exact input references of all seven folds and
intersections. It does not depend on approximate geometry or execute a proof.
-/

namespace LeanOrigamiTests.WidgetHistory
open LeanOrigami LeanOrigami.Widget

/-- Input order includes every point and line, especially the four A6 inputs. -/
example (crease : Line Scalar) :
    (#[FoldRequest.axiom1 ⟨0⟩ ⟨1⟩, .axiom2 ⟨1⟩ ⟨0⟩, .axiom3 ⟨2⟩ ⟨3⟩,
      .axiom4 ⟨1⟩ ⟨2⟩, .axiom5 ⟨1⟩ ⟨0⟩ ⟨3⟩, .axiom6 ⟨0⟩ ⟨1⟩ ⟨2⟩ ⟨3⟩,
      .axiom7 ⟨1⟩ ⟨2⟩ ⟨3⟩].map fun request => (historyStep 4 (.fold request crease)).inputs) =
    #[#[0, 1], #[1, 0], #[2, 3], #[1, 2], #[1, 0, 3], #[0, 1, 2, 3], #[1, 2, 3]] := by
  simp [historyStep]

-- The view follows a runtime cursor through nested scopes. This is a UI
-- behavior check, not mathematical proof evidence.
#eval show IO Unit from do
  let crease : Line Scalar := Line.horizontal 0
  let session : Session := { program := Execution.ofProgram [
    .fold (.axiom1 ⟨0⟩ ⟨1⟩) crease, .fold (.axiom2 ⟨0⟩ ⟨1⟩) crease,
    .intersect ⟨2⟩ ⟨3⟩ (0,0)] }
  let history := (session.view 32).history
  unless history.map (·.output) == #[2,3,4] &&
      history.map (·.inputs) == #[#[0,1], #[0,1], #[2,3]] do
    throw (IO.userError "History references changed")

end LeanOrigamiTests.WidgetHistory
