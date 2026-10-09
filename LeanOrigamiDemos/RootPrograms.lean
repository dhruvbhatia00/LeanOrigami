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

/-- Construct the coefficient two. -/
def two : Program K × PointRef :=
  (ArithmeticRecipe.add 1 1).append (Basis.program K true) (arithmetic ⟨1⟩ ⟨1⟩)

/-- Replayable nonnegative square root of two, if the candidate passes its guard. -/
def squareRootTwo (t : K) : Option (Program K × PointRef) := do
  let recipe ← RootRecipe.squareRoot 2 t
  return recipe.append (two K).1 (basis.indices ![(two K).2])

/-- The coefficient minus two is constructed before the cubic fold. -/
def cubeRootTwo (t : K) : Program K × PointRef :=
  let neg := (ArithmeticRecipe.sub 0 2).append (two K).1 (arithmetic ⟨0⟩ (two K).2)
  (RootRecipe.monicCubic 0 0 (-2) t).append neg.1
    (basis.indices ![⟨0⟩, ⟨0⟩, neg.2])

/-- Reuse the first root's output reference as the second radicand. -/
def fourthRootTwo (square fourth : K) : Option (Program K × PointRef) := do
  let first ← squareRootTwo K square
  let recipe ← RootRecipe.squareRoot square fourth
  return recipe.append first.1 (basis.indices ![first.2])

/-- Construct the coefficients of `8*t³-6*t-1`, then select the trisection
cosine. Branch selection and identification are checked in the separate demos. -/
def trisectionCosine (t : K) : Program K × PointRef :=
  let four := (ArithmeticRecipe.add 2 2).append (two K).1
    (arithmetic (two K).2 (two K).2)
  let six := (ArithmeticRecipe.add 4 2).append four.1 (arithmetic four.2 (two K).2)
  let eight := (ArithmeticRecipe.add 4 4).append six.1 (arithmetic four.2 four.2)
  let minusSix := (ArithmeticRecipe.sub 0 6).append eight.1 (arithmetic ⟨0⟩ six.2)
  let minusOne := (ArithmeticRecipe.sub 0 1).append minusSix.1 (arithmetic ⟨0⟩ ⟨1⟩)
  (RootRecipe.cubic 8 0 (-6) (-1) t (by norm_num)).append minusOne.1
    (basis.indices ![eight.2, ⟨0⟩, minusSix.2, minusOne.2])

/-- Finish the upper unit-circle point from the selected cosine and positive
sine. Both coordinates are obtained by constructions before pairing them. -/
def trisectionPoint (cosine sine : K) : Option (Program K × PointRef) := do
  if ¬((1/2 : K) < cosine ∧ cosine < 1 ∧ 0 < sine) then none else do
    let first := trisectionCosine K cosine
    let square := (ArithmeticRecipe.mul cosine cosine).append first.1
      (arithmetic first.2 first.2)
    let radicand := (ArithmeticRecipe.sub 1 (cosine*cosine)).append square.1
      (arithmetic ⟨1⟩ square.2)
    let recipe ← RootRecipe.squareRoot (1-cosine*cosine) sine
    let second := recipe.append radicand.1 (basis.indices ![radicand.2])
    return (ArithmeticRecipe.pair cosine sine).append second.1
      (arithmetic first.2 second.2)

end LeanOrigamiDemos.RootPrograms
