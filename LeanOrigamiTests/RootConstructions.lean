import LeanOrigami.Construction.RootRecipe
import LeanOrigami.Construction.Roots

/-!
# Root construction boundaries and replay

The rational examples exercise the same generic recipes used with Hex for
irrational outputs. Acceptance is reduced by the kernel from the two seeds.
Geometric tests include coincident source points and the horizontal zero root.
-/

namespace LeanOrigamiTests.RootConstructions
open LeanOrigami

/-- Standard basis indices after expanding the off-axis construction. -/
def basis : RootRecipe.BasisArguments := ⟨⟨0⟩, ⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨8⟩⟩

/-- Obtain the coefficient minus one from existing seed coordinates. -/
def negativeOne : Program ℚ × PointRef :=
  (ArithmeticRecipe.sub 0 1).append (Basis.program ℚ true)
    (ArithmeticRecipe.Arguments.mk ⟨0⟩ ⟨1⟩ ⟨2⟩ ⟨3⟩ ⟨8⟩ ⟨0⟩ ⟨1⟩).indices

/-- Three branches of `t³-t`, sharing the same coefficient history. -/
def threeBranches (t : ℚ) : Program ℚ × PointRef :=
  (RootRecipe.monicCubic 0 (-1) 0 t).append negativeOne.1
    (basis.indices ![⟨0⟩, negativeOne.2, ⟨0⟩])

set_option maxRecDepth 8192 in
/-- All three choices replay, including the horizontal crease at zero. -/
theorem three_branches_accept :
    [(-1 : ℚ), 0, 1].all (fun t =>
      Program.accepts (threeBranches t).1 (threeBranches t).2 .x t) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
/-- An unrelated saved crease is rejected during replay. -/
theorem wrong_root_rejected :
    Program.accepts (threeBranches 2).1 (threeBranches 2).2 .x 2 = false := by
  decide +kernel

/-- The cubic `(t+1)²(t-1)` has a repeated root at minus one. -/
def repeated : Program ℚ × PointRef :=
  (RootRecipe.monicCubic 1 (-1) (-1) (-1)).append negativeOne.1
    (basis.indices ![⟨1⟩, negativeOne.2, negativeOne.2])

set_option maxRecDepth 8192 in
/-- Repeated roots require no division by a derivative or root separation. -/
theorem repeated_accept : Program.accepts repeated.1 repeated.2 .x (-1) = true := by
  decide +kernel

/-- A genuine nonmonic cubic `2*t³-2*t`, with both coefficients constructed. -/
def nonmonic : Program ℚ × PointRef :=
  let two := (ArithmeticRecipe.add 1 1).append (Basis.program ℚ true)
    (ArithmeticRecipe.Arguments.mk ⟨0⟩ ⟨1⟩ ⟨2⟩ ⟨3⟩ ⟨8⟩ ⟨1⟩ ⟨1⟩).indices
  let neg := (ArithmeticRecipe.sub 0 2).append two.1
    (ArithmeticRecipe.Arguments.mk ⟨0⟩ ⟨1⟩ ⟨2⟩ ⟨3⟩ ⟨8⟩ ⟨0⟩ two.2).indices
  (RootRecipe.cubic 2 0 (-2) 0 1 (by decide)).append neg.1
    (basis.indices ![two.2, ⟨0⟩, neg.2, ⟨0⟩])

set_option maxRecDepth 8192 in
/-- Normalization constructs the divisions before the selected fold. -/
example : Program.accepts nonmonic.1 nonmonic.2 .x 1 = true := by decide +kernel

set_option maxRecDepth 8192 in
/-- Both roots of `t²-1` survive the quadratic guard and replay. -/
example : [(-1 : ℚ), 1].all (fun t =>
    ((RootRecipe.quadratic 1 0 (-1) t (by decide)).map fun recipe =>
      let result := recipe.append negativeOne.1 (basis.indices ![⟨1⟩, ⟨0⟩, negativeOne.2])
      Program.accepts result.1 result.2 .x t).getD false) = true := by decide +kernel

set_option maxRecDepth 8192 in
/-- Square root zero is valid and does not divide by the selected root. -/
example : ((RootRecipe.squareRoot (0 : ℚ) 0).map fun recipe =>
    let result := recipe.append (Basis.program ℚ true) (basis.indices ![⟨0⟩])
    Program.accepts result.1 result.2 .x 0).getD false = true := by decide +kernel

/-- Quadratic embedding must reject its artificial zero root. -/
example : RootRecipe.quadratic (1 : ℚ) 0 (-1) 0 (by decide) = none := by decide +kernel

/-- A negative square-root branch is not the requested nonnegative square root. -/
example : RootRecipe.squareRoot (1 : ℚ) (-1) = none := by decide +kernel

/-- A negative radicand cannot pass the exact square-root guard. -/
example : RootRecipe.squareRoot (-1 : ℚ) 0 = none := by decide +kernel

/-- Even coincident sources in this coefficient configuration remain finite. -/
example : (RootGeometry.input (0 : ℝ) 1 0).Admissible := RootGeometry.admissible _ _ _

/-- A zero root has a horizontal crease, and remains a legal choice. -/
example : (RootGeometry.input (0 : ℝ) 1 0).Legal (RootGeometry.crease 0) := by
  exact ⟨RootGeometry.admissible _ _ _, (RootGeometry.satisfies_iff _ _ _ _).mpr (by norm_num)⟩

/-- A constant nonzero equation has no root; the zero equation places no
restriction and therefore supplies no new construction evidence. -/
example {c t : ℝ} (hc : c ≠ 0) : ¬(0*t+c = 0) := by simpa using hc

#print axioms ConstructibleNumber.monic_cubic_root
#print axioms ConstructibleNumber.cubic_root
#print axioms ConstructibleNumber.quadratic_root
#print axioms ConstructibleNumber.sqrt
#print axioms three_branches_accept
#print axioms repeated_accept

end LeanOrigamiTests.RootConstructions
