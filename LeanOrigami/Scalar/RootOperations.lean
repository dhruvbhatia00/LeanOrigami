import LeanOrigami.Construction.RootOperation
import LeanOrigami.Scalar.FoldDiscovery
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt

/-!
# Existence of the exact roots used by recipes

The real analysis is confined to this proof bridge. Hex's complete root list
represents the required real root exactly; executable recipes continue to use
algebraic scalars and the ordinary fold discovery operations.
-/

namespace LeanOrigami

/-- A real cube root exists for either sign of the input. -/
theorem RootOperation.real_cube_exists (x : ℝ) : ∃ t : ℝ, t^3 = x := by
  by_cases hx : 0 ≤ x
  · exact ⟨x ^ (3⁻¹ : ℝ), Real.rpow_inv_natCast_pow hx (by decide : (3 : ℕ) ≠ 0)⟩
  · refine ⟨-((-x) ^ (3⁻¹ : ℝ)), ?_⟩
    have h := Real.rpow_inv_natCast_pow (by linarith : 0 ≤ -x) (by decide : (3 : ℕ) ≠ 0)
    nlinarith only [h]

namespace Scalar

/-- Every permitted input has its specified root in the executable scalar
field. No surjection from algebraic numbers onto arbitrary reals is assumed. -/
theorem rootOperation_exists (op : RootOperation) (x : Scalar) (h : op.Domain x) :
    ∃ t : Scalar, op.Relation x t := by
  cases op with
  | square =>
    have hx : 0 ≤ toReal x := by simpa using (toReal_le 0 x).mpr h
    obtain ⟨t, _, ht⟩ := rootList_quadratic_complete 1 0 (-x)
      (Or.inl one_ne_zero) (Real.sqrt (toReal x)) (by
        change realHom 1 * _^2 + realHom 0 * _ + realHom (-x) = 0
        simp only [map_one, map_zero, map_neg, one_mul, zero_mul, add_zero]
        change (Real.sqrt (toReal x))^2 + -(toReal x) = 0
        rw [Real.sq_sqrt hx]
        ring)
    refine ⟨t, ?_, ?_⟩
    · apply (toReal_le 0 t).mp
      simp [ht]
    · apply realHom.injective
      rw [map_pow]
      change (toReal t)^2 = toReal x
      rw [ht, Real.sq_sqrt hx]
  | cube =>
    obtain ⟨r, hr⟩ := RootOperation.real_cube_exists (toReal x)
    let polynomial : Univariate.Cubic Scalar := ⟨-x, 0, 0, 1⟩
    obtain ⟨t, _, ht⟩ := rootList_cubic_complete polynomial
      (by simp [polynomial, Univariate.Cubic.IsZero]) r (by
        simp only [polynomial, Univariate.Cubic.map, Univariate.Cubic.eval,
          map_neg, map_zero, map_one, zero_add, mul_one]
        change -(toReal x) + r * (r * r) = 0
        nlinarith [hr])
    refine ⟨t, ?_⟩
    apply realHom.injective
    rw [map_pow]
    change (toReal t)^3 = toReal x
    rw [ht, hr]

end Scalar
end LeanOrigami
