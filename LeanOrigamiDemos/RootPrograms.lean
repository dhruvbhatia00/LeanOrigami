import LeanOrigami.Construction.RootRecipe
import Mathlib.Data.Fin.VecNotation

/-!
# Saved programs for irrational root demonstrations

These constructors accept exact candidate values, not constructed input points.
Every coefficient is built from the seeds; the ordinary checker validates the
candidate folds. The same functions work over rationals or Hex's real scalars.
The mathematical identification of their intended outputs is in Roots.lean.
-/

namespace LeanOrigamiDemos.RootPrograms
open LeanOrigami
variable (K : Type) [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Basis references shared by these programs. -/
def basis : RootRecipe.BasisArguments := ⟨⟨0⟩, ⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨8⟩⟩

private def arithmetic (first second : PointRef) : Fin 7 → Nat :=
  (ArithmeticRecipe.Arguments.mk ⟨0⟩ ⟨1⟩ ⟨2⟩ ⟨3⟩ ⟨8⟩ first second).indices

-- A builder keeps the next free reference separately from the growing program.
-- This also keeps symbolic replay from repeatedly expanding earlier prefixes.
private def finish (body : RecipeBuilder K PointRef) : Program K × PointRef :=
  let recipe := RecipeBuilder.build 2 body
  (recipe.steps, recipe.output)

private def twoBuilder : RecipeBuilder K PointRef := do
  let _ ← RecipeBuilder.use (⟨Basis.program K true, ⟨8⟩⟩ : Recipe K 2) (fun i => i.val)
  RecipeBuilder.use (ArithmeticRecipe.add 1 1) (arithmetic ⟨1⟩ ⟨1⟩)

/-- Construct the coefficient two. -/
def two : Program K × PointRef := finish K (twoBuilder K)

/-- Replayable nonnegative square root of two, if the candidate passes its guard. -/
def squareRootTwo (t : K) : Option (Program K × PointRef) := do
  let recipe ← RootRecipe.squareRoot 2 t
  return finish K do
    let coefficient ← twoBuilder K
    RecipeBuilder.use recipe (basis.indices ![coefficient])

/-- The coefficient minus two is constructed before the cubic fold. -/
def cubeRootTwo (t : K) : Program K × PointRef := finish K do
  let coefficient ← twoBuilder K
  let negative ← RecipeBuilder.use (ArithmeticRecipe.sub 0 2) (arithmetic ⟨0⟩ coefficient)
  RecipeBuilder.use (RootRecipe.monicCubic 0 0 (-2) t)
    (basis.indices ![⟨0⟩, ⟨0⟩, negative])

/-- Reuse the first root's output reference as the second radicand. -/
def fourthRootTwo (square fourth : K) : Option (Program K × PointRef) := do
  let first ← RootRecipe.squareRoot 2 square
  let second ← RootRecipe.squareRoot square fourth
  return finish K do
    let coefficient ← twoBuilder K
    let root ← RecipeBuilder.use first (basis.indices ![coefficient])
    RecipeBuilder.use second (basis.indices ![root])

private def trisectionBuilder (t : K) : RecipeBuilder K PointRef := do
  let two ← twoBuilder K
  let four ← RecipeBuilder.use (ArithmeticRecipe.add 2 2) (arithmetic two two)
  let six ← RecipeBuilder.use (ArithmeticRecipe.add 4 2) (arithmetic four two)
  let eight ← RecipeBuilder.use (ArithmeticRecipe.add 4 4) (arithmetic four four)
  let minusSix ← RecipeBuilder.use (ArithmeticRecipe.sub 0 6) (arithmetic ⟨0⟩ six)
  let minusOne ← RecipeBuilder.use (ArithmeticRecipe.sub 0 1) (arithmetic ⟨0⟩ ⟨1⟩)
  RecipeBuilder.use (RootRecipe.cubic 8 0 (-6) (-1) t (by norm_num))
    (basis.indices ![eight, ⟨0⟩, minusSix, minusOne])

/-- Construct the coefficients of `8*t³-6*t-1`, then select the trisection
cosine. Branch selection and identification are checked in the separate demos. -/
def trisectionCosine (t : K) : Program K × PointRef := finish K (trisectionBuilder K t)

/-- Finish the upper unit-circle point from the selected cosine and positive
sine. Both coordinates are obtained by constructions before pairing them. -/
def trisectionPoint (cosine sine : K) : Option (Program K × PointRef) := do
  if ¬((1/2 : K) < cosine ∧ cosine < 1 ∧ 0 < sine) then none else do
    let recipe ← RootRecipe.squareRoot (1-cosine*cosine) sine
    return finish K do
      let first ← trisectionBuilder K cosine
      let square ← RecipeBuilder.use (ArithmeticRecipe.mul cosine cosine)
        (arithmetic first first)
      let radicand ← RecipeBuilder.use (ArithmeticRecipe.sub 1 (cosine*cosine))
        (arithmetic ⟨1⟩ square)
      let second ← RecipeBuilder.use recipe (basis.indices ![radicand])
      RecipeBuilder.use (ArithmeticRecipe.pair cosine sine) (arithmetic first second)

end LeanOrigamiDemos.RootPrograms
