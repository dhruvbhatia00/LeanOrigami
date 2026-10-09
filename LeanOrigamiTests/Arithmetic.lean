import LeanOrigamiDemos.Arithmetic

/-!
# Arithmetic boundaries, placement, and recipe reuse

These tests exercise the public expansion API and exact submission. General
geometric correctness is supplied by the construction theorems; these small
computations also check reference relocation and saved-coordinate handling.
-/

namespace LeanOrigamiTests.Arithmetic
open LeanOrigami LeanOrigamiDemos.Arithmetic

private def check (recipe : Recipe ℚ 7) (first second : PointRef) (value : ℚ) : Bool :=
  let (program, result) := recipe.append (Basis.program ℚ true) (arguments first second).indices
  Program.accepts program result .x value

example : check (ArithmeticRecipe.add 0 1) ⟨0⟩ ⟨1⟩ 1 = true := by decide +kernel
example : check (ArithmeticRecipe.add 1 0) ⟨1⟩ ⟨0⟩ 1 = true := by decide +kernel
example : check (ArithmeticRecipe.sub 1 1) ⟨1⟩ ⟨1⟩ 0 = true := by decide +kernel
example : check (ArithmeticRecipe.sub 0 1) ⟨0⟩ ⟨1⟩ (-1) = true := by decide +kernel
example : check (ArithmeticRecipe.mul 0 1) ⟨0⟩ ⟨1⟩ 0 = true := by decide +kernel
example : check (ArithmeticRecipe.mul 1 0) ⟨1⟩ ⟨0⟩ 0 = true := by decide +kernel
example : check (ArithmeticRecipe.div 0 1 (by decide)) ⟨0⟩ ⟨1⟩ 0 = true := by decide +kernel
example : check (ArithmeticRecipe.div 1 1 (by decide)) ⟨1⟩ ⟨1⟩ 1 = true := by decide +kernel

-- The coordinates used to assemble a recipe are checked against its actual inputs.
example : check (ArithmeticRecipe.add 42 1) ⟨0⟩ ⟨1⟩ 43 = false := by decide +kernel
example : check (ArithmeticRecipe.div 1 1 (by decide)) ⟨1⟩ ⟨0⟩ 1 = false := by decide +kernel
-- A line reference passed in a point slot and a missing reference both fail replay.
example : check (ArithmeticRecipe.add 0 1) ⟨2⟩ ⟨1⟩ 1 = false := by decide +kernel
example : check (ArithmeticRecipe.add 0 1) ⟨42⟩ ⟨1⟩ 1 = false := by decide +kernel

private def placementArguments : Fin 5 → Nat := fun i =>
  match i.val with | 0 => 8 | 1 => 0 | 2 => 1 | 3 => 2 | _ => 3

-- Signed placement transfers a negative vertical coordinate to the original axis.
example :
    let result := (ArithmeticRecipe.place ((0, -1) : Point ℚ) .y).append
      (Basis.program ℚ false) placementArguments
    Program.accepts result.1 result.2 .x (-1) = true := by decide +kernel
-- The other coordinate is zero; this causes no coincident-point construction.
example :
    let result := (ArithmeticRecipe.place ((0, -1) : Point ℚ) .x).append
      (Basis.program ℚ false) placementArguments
    Program.accepts result.1 result.2 .x 0 = true := by decide +kernel

-- The public theorems require construction evidence for both operands.
example (x y : ℝ) (hx : ConstructibleNumber x) (hy : ConstructibleNumber y) :
    Constructible (.point (x*y, x-y)) :=
  ConstructibleNumber.point (hx.mul hy) (hx.sub hy)
example (x y : ℝ) (hx : ConstructibleNumber x) (hy : ConstructibleNumber y) (h : y ≠ 0) :
    ConstructibleNumber (-(x/y)) := (hx.div hy h).neg

#print axioms constructible_point_iff
#print axioms ConstructibleNumber.add
#print axioms ConstructibleNumber.sub
#print axioms ConstructibleNumber.mul
#print axioms ConstructibleNumber.div
#print axioms Recipe.relocate_lt
#print axioms LeanOrigamiDemos.Arithmetic.result_constructible

end LeanOrigamiTests.Arithmetic
