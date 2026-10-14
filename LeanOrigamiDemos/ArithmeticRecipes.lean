import LeanOrigami.Widget

/-!
# Arithmetic in the visual recipe editor

Place the cursor on `origami_recipe` below. The saved multiplication template
runs on the displayed signed samples. Its positive-diagonal branch is selected
by an exact condition, and the result is (-2, 0). Change either scalar sample
with Edit samples to replay it, including zero operands.

The operation menu also contains addition, subtraction, negation, reciprocal,
and division, with explicit coordinate-frame inputs and proved specifications.
-/
namespace LeanOrigamiDemos.ArithmeticRecipes
open LeanOrigami LeanOrigami.Widget

/-- Names match the template parameters; these objects are exploratory samples. -/
def samples : RecipeSamples :=
  (arithmeticTemplate .mul).parameters.toList.map (·.name) |>.zip
    (ArithmeticOperation.inputs .mul (-1 : Scalar) 2)

origami_recipe signedProduct samples (samples) saved (arithmeticTemplate .mul)

end LeanOrigamiDemos.ArithmeticRecipes
