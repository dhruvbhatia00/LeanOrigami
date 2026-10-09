import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Root bounds including degree drops

The bounds apply over ordered fields without assuming square or cube roots
exist. They bound distinct values, not multiplicities. Choosing a root inside
these proofs does not participate in executable root discovery.
-/

namespace LeanOrigami.Univariate
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A nonzero polynomial of degree at most two has at most two roots. -/
theorem quadratic_zeros_subset_pair (a b c : K) (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    ∃ r s : K, ∀ t, a*t^2 + b*t + c = 0 → t = r ∨ t = s := by
  classical
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · have hc := (h.resolve_left (not_not.mpr ha)).resolve_left (not_not.mpr hb)
      exact ⟨0, 0, fun t ht => False.elim (hc (by simpa [ha, hb] using ht))⟩
    · refine ⟨-c/b, -c/b, ?_⟩
      intro t ht
      apply Or.inl
      apply (eq_div_iff hb).mpr
      simp only [ha, zero_mul, zero_add] at ht
      nlinarith
  · by_cases hex : ∃ r : K, a*r^2 + b*r + c = 0
    · obtain ⟨r, hr⟩ := hex
      refine ⟨r, -r-b/a, ?_⟩
      intro t ht
      have hfactor : (t-r)*(a*t+a*r+b) = 0 := by linear_combination ht - hr
      rcases mul_eq_zero.mp hfactor with ht | ht
      · exact Or.inl (sub_eq_zero.mp ht)
      · apply Or.inr
        field_simp [ha]
        nlinarith [ht]
    · exact ⟨0, 0, fun t ht => False.elim (hex ⟨t, ht⟩)⟩

/-- A nonzero polynomial of degree at most three has at most three roots. -/
theorem cubic_zeros_subset_triple (a b c d : K)
    (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0) :
    ∃ r s u : K, ∀ t, a*t^3 + b*t^2 + c*t + d = 0 → t = r ∨ t = s ∨ t = u := by
  classical
  by_cases ha : a = 0
  · obtain ⟨r, s, hrs⟩ := quadratic_zeros_subset_pair b c d (h.resolve_left (not_not.mpr ha))
    refine ⟨r, s, s, ?_⟩
    intro t ht
    exact (hrs t (by simpa [ha] using ht)).imp_right Or.inl
  · by_cases hex : ∃ r : K, a*r^3 + b*r^2 + c*r + d = 0
    · obtain ⟨r, hr⟩ := hex
      obtain ⟨s, u, hsu⟩ := quadratic_zeros_subset_pair a (a*r+b) (a*r^2+b*r+c) (Or.inl ha)
      refine ⟨r, s, u, ?_⟩
      intro t ht
      have hf : (t-r)*(a*t^2+(a*r+b)*t+(a*r^2+b*r+c)) = 0 := by
        linear_combination ht - hr
      rcases mul_eq_zero.mp hf with hf | hf
      · exact Or.inl (sub_eq_zero.mp hf)
      · exact Or.inr (hsu t hf)
    · exact ⟨0, 0, 0, fun t ht => False.elim (hex ⟨t, ht⟩)⟩

/-- The same bound as a finiteness statement for polynomial zero sets. -/
theorem finite_cubic_zeros (a b c d : K) (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0) :
    {t : K | a*t^3 + b*t^2 + c*t + d = 0}.Finite := by
  obtain ⟨r, s, u, hrs⟩ := cubic_zeros_subset_triple a b c d h
  exact (Set.toFinite ({r, s, u} : Set K)).subset (fun t ht => hrs t ht)

end LeanOrigami.Univariate
