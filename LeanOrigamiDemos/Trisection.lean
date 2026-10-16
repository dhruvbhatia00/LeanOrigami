import LeanOrigami.Widget

/-!
# Explore both interior trisectors

Place the cursor on `origami_recipe` below. The saved recipe trisects a right
angle, displaying both output points and both creases. Its first endpoint is
(√3/2, 1/2); its second is (1/2, √3/2).

The history contains one library call and four public outputs. Expand that
entry and choose Inspect to explore its original 856 private construction steps.
Those steps are not replayed when certifying an unchanged library call.

Use Edit samples to change the vertex or ray points. For a translated example
with unequal ray lengths, use vertex (2,-3), first point (2,-1), and second point
(6/25,-192/25). For clockwise input, change the right-angle sample's second ray
point to (0,-1). Zero and straight angles are rejected. Frame samples must stay
at their stated standard values. Samples support exploration, not new proof seeds.
-/
namespace LeanOrigamiDemos.Trisection
open LeanOrigami LeanOrigami.Widget

/-- A right angle in the standard frame, with no preselected algebraic roots. -/
def samples : RecipeSamples :=
  trisectionTemplate.parameters.toList.map (·.name) |>.zip
    (TrisectionRecipe.inputs ((0 : Scalar), 0) (1, 0) (0, 1))

/-- A caller exposes all four results while retaining the library invocation. -/
def construction : RecipeTemplate where
  parameters := trisectionTemplate.parameters
  requirements := trisectionTemplate.requirements
  steps := [.call "Trisection" trisectionTemplate (Array.range 8)]
  output := 8
  outputs := #[⟨"First trisector point", 8⟩, ⟨"Second trisector point", 9⟩,
    ⟨"First trisector line", 10⟩, ⟨"Second trisector line", 11⟩]

origami_recipe trisectors samples (samples) saved (construction)

end LeanOrigamiDemos.Trisection
