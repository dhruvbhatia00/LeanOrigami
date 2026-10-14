import LeanOrigami.Widget

/-!
# A recipe with declared input requirements

Place the cursor on `origami_recipe` to view/edit the construction and open
Requirements. Both samples start on the x-axis. Move A off that axis to see an
exact rejection; Reset samples recovers the construction. These declarations
are input requirements, not a proof of a general midpoint specification.
-/
open LeanOrigami LeanOrigami.Widget
namespace LeanOrigamiDemos.Requirements

origami_recipe axisMidpoint samples (
  [("A", .point (0, 0)), ("B", .point (2, 0))]) saved (
  { parameters := #[⟨"A", .point⟩, ⟨"B", .point⟩]
    steps := [.fold (.axiom1 ⟨0⟩ ⟨1⟩), .fold (.axiom2 ⟨0⟩ ⟨1⟩), .intersect ⟨2⟩ ⟨3⟩]
    output := 4
    requirements := #[.onXAxis 0, .onXAxis 1, .not (.samePoint 0 1)] })

-- Start a separate draft here to try automatic input names and new requirements.
origami_recipe

end LeanOrigamiDemos.Requirements
