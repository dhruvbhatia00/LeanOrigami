import LeanOrigami.Scalar.RootOperations
import LeanOrigami.Geometry.Trisection

/-!
# Exact witnesses for general angle trisection

Real trigonometry proves that the required cubic branch exists. Completeness
of the algebraic root finder places it in the executable scalar field. The
construction itself uses only field operations and exact root choices.
-/

namespace LeanOrigami.Scalar

/-- The trisection cubic has its intended root strictly between one half and
one whenever the cosine of the input angle lies strictly between -1 and 1. -/
theorem thirdCosine_exists (c : Scalar) (hc : -1 < c ∧ c < 1) :
    ∃ t : Scalar, 1/2 < t ∧ t < 1 ∧ 4*t^3-3*t = c := by
  have hcr : -1 < toReal c ∧ toReal c < 1 := by
    constructor
    · have hn : toReal (-1) = -1 := by
        change realHom (-1) = -1
        simp
      simpa only [hn] using (toReal_lt (-1) c).mpr hc.1
    · simpa using (toReal_lt c 1).mpr hc.2
  let θ := Real.arccos (toReal c)
  have hθ : 0 < θ ∧ θ < Real.pi :=
    ⟨Real.arccos_pos.mpr hcr.2, Real.arccos_lt_pi.mpr hcr.1⟩
  have hlow : 1/2 < Real.cos (θ/3) := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi
      (by linarith : 0 ≤ θ/3) (by linarith [Real.pi_pos] : Real.pi/3 ≤ Real.pi)
      (by linarith : θ/3 < Real.pi/3)
    simpa only [Real.cos_pi_div_three] using h
  have hhigh : Real.cos (θ/3) < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi
      (le_refl (0 : ℝ)) (by linarith : θ/3 ≤ Real.pi) (by linarith : 0 < θ/3)
    simpa only [Real.cos_zero] using h
  have heq : 4*(Real.cos (θ/3))^3-3*Real.cos (θ/3) = toReal c := by
    have he := Real.cos_three_mul (θ/3)
    have hcos : Real.cos θ = toReal c := Real.cos_arccos hcr.1.le hcr.2.le
    rw [show 3*(θ/3) = θ by ring, hcos] at he
    exact he.symm
  let polynomial : Univariate.Cubic Scalar := ⟨-c, -3, 0, 4⟩
  obtain ⟨t, _, ht⟩ := rootList_cubic_complete polynomial
    (by norm_num [polynomial, Univariate.Cubic.IsZero]) (Real.cos (θ/3)) (by
      simp only [polynomial, Univariate.Cubic.map, Univariate.Cubic.eval,
        map_neg, map_zero, map_ofNat, zero_add]
      change -(toReal c) + Real.cos (θ/3)*(-3 + Real.cos (θ/3)*(Real.cos (θ/3)*4)) = 0
      nlinarith [heq])
  refine ⟨t, ?_, ?_, ?_⟩
  · apply (toReal_lt (1/2) t).mp
    have hh : toReal (1/2) = 1/2 := by
      change realHom (1/2) = 1/2
      simp [map_ofNat]
    simpa only [hh, ht] using hlow
  · apply (toReal_lt t 1).mp
    simpa [ht] using hhigh
  · apply realHom.injective
    simp only [map_sub, map_mul, map_pow, map_ofNat]
    change 4*(toReal t)^3-3*toReal t = toReal c
    rw [ht]
    exact heq

/-- A strictly positive radicand has a strictly positive exact square root. -/
private theorem positive_square_exists (x : Scalar) (hx : 0 < x) :
    ∃ t : Scalar, 0 < t ∧ t^2 = x := by
  obtain ⟨t, ht, he⟩ := rootOperation_exists .square x hx.le
  refine ⟨t, ?_, he⟩
  by_contra hn
  have hz : t = 0 := le_antisymm (le_of_not_gt hn) ht
  simp [hz] at he
  exact (ne_of_gt hx) he.symm

/-- Every nonzero, nonstraight pair of rays admits all five exact root
choices, with the strict signs and cubic interval used by the recipe. -/
theorem trisectionRoots_exists (vertex first second : Point Scalar)
    (h : Trisection.Domain vertex first second) :
    ∃ roots : Trisection.Roots Scalar, roots.Valid vertex first second := by
  obtain ⟨hfirst, hsecond⟩ := Trisection.domain_lengths vertex first second h
  obtain ⟨a, ha, ha2⟩ := positive_square_exists _ hfirst
  obtain ⟨b, hb, hb2⟩ := positive_square_exists _ hsecond
  let c := (Trisection.unitVector vertex first a).dot (Trisection.unitVector vertex second b)
  have hc : -1 < c ∧ c < 1 := Trisection.cosine_bounds vertex first second a b h ha hb ha2 hb2
  have hs : 0 < 1-c^2 := by nlinarith [mul_pos (by linarith : 0 < 1-c) (by linarith : 0 < 1+c)]
  obtain ⟨s, hs, hs2⟩ := positive_square_exists _ hs
  obtain ⟨t, ht, ht1, ht3⟩ := thirdCosine_exists c hc
  have hr : 0 < 1-t^2 := by nlinarith [mul_pos (by linarith : 0 < 1-t) (by linarith : 0 < 1+t)]
  obtain ⟨r, hr, hr2⟩ := positive_square_exists _ hr
  exact ⟨⟨a, b, s, t, r⟩, ha, ha2, hb, hb2, hs, hs2, ht, ht1, ht3, hr, hr2⟩

/-- Exact witness equations imply actual real-plane trisection, including
both interior rays and all three equal angles. -/
theorem trisectionRoots_sound (roots : Trisection.Roots Scalar) (vertex first second : Point Scalar)
    (h : roots.Valid vertex first second) :
    Trisection.IsTrisection (Prod.map realHom realHom vertex) (Prod.map realHom realHom first)
      (Prod.map realHom realHom second) (Prod.map realHom realHom (roots.firstPoint vertex first second))
      (Prod.map realHom realHom (roots.secondPoint vertex first second)) := by
  have hm := roots.map_valid realHom (fun _ _ h => (toReal_lt _ _).mpr h) vertex first second h
  have he := (roots.map realHom).isTrisection _ _ _ hm
  obtain ⟨hfirst, hsecond⟩ := roots.points_map realHom vertex first second
  rw [hfirst, hsecond] at he
  exact he

end LeanOrigami.Scalar
