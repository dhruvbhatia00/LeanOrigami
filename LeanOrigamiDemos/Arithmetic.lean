import LeanOrigami.Construction.ArithmeticRecipe

/-!
# Arithmetic by expanding reusable folds

This example constructs `2`, `-2`, `4`, then `4 / -2 = -2`. Each recipe is
expanded after the preceding program, so all intermediate references shift.
Only the original two seed points are assumed. The final theorem is checked
by kernel computation over rationals, not by the native Hex interpreter.
-/

namespace LeanOrigamiDemos.Arithmetic
open LeanOrigami

/-- The basis recipe leaves the axes at 2 and 3 and the vertical unit at 8. -/
def arguments (first second : PointRef) : ArithmeticRecipe.Arguments :=
  ⟨⟨0⟩, ⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨8⟩, first, second⟩

/-- First expansion: `1 + 1 = 2`. -/
def two : Program ℚ × PointRef :=
  (ArithmeticRecipe.add 1 1).append (Basis.program ℚ true) (arguments ⟨1⟩ ⟨1⟩).indices

/-- Reuse the result reference as an operand: `0 - 2 = -2`. -/
def negativeTwo : Program ℚ × PointRef :=
  (ArithmeticRecipe.sub 0 2).append two.1 (arguments ⟨0⟩ two.2).indices

/-- Squaring the negative result constructs `4`. -/
def four : Program ℚ × PointRef :=
  (ArithmeticRecipe.mul (-2) (-2)).append negativeTwo.1
    (arguments negativeTwo.2 negativeTwo.2).indices

/-- Division reuses two different earlier outputs, at different offsets. -/
def quotient : Program ℚ × PointRef :=
  (ArithmeticRecipe.div 4 (-2) (by decide)).append four.1
    (arguments four.2 negativeTwo.2).indices

set_option maxRecDepth 4096 in
/-- Replay checks every saved fold, intersection, reference, and final coordinate. -/
theorem accepts : Program.accepts quotient.1 quotient.2 .x (-2) = true := by
  decide +kernel

/-- The computed acceptance is converted into a geometric construction proof. -/
theorem result_constructible : ConstructibleNumber (-2 : ℝ) := by
  have h := Program.accepts_sound (Rat.castHom ℝ) quotient.1 quotient.2 .x (-2) accepts
  simpa using h

#print axioms result_constructible

end LeanOrigamiDemos.Arithmetic
