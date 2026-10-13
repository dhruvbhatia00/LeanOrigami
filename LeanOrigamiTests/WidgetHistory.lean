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

/-- The third instruction produces object 4; intersections highlight both lines. -/
example (crease : Line Scalar) :
    let session : Session := { program := [
      .fold (.axiom1 ⟨0⟩ ⟨1⟩) crease, .fold (.axiom2 ⟨0⟩ ⟨1⟩) crease,
      .intersect ⟨2⟩ ⟨3⟩ (0, 0)] }
    ((session.view 32).history.map (·.output) = #[2, 3, 4]) ∧
      ((session.view 32).history.map (·.inputs) = #[#[0, 1], #[0, 1], #[2, 3]]) := by
  simp [Session.view, historyStep, Program.initial]

end LeanOrigamiTests.WidgetHistory
