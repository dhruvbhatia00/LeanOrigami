import LeanOrigami.Widget

/-!
# Explore both interior trisectors

Place the cursor on `origami_recipe` below. The saved recipe trisects a right
angle, displaying both output points and both creases. Its first endpoint is
(√3/2, 1/2); its second is (1/2, √3/2).

The current coordinate-arithmetic recipe expands to 856 primitive steps.
A compact geometric replacement is recorded in the plan as follow-up work.

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

origami_recipe trisectors samples (samples) saved (trisectionTemplate)

end LeanOrigamiDemos.Trisection
