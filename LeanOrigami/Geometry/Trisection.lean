import LeanOrigami.Geometry.TrisectionModel
import LeanOrigami.Geometry.AngleSemantics

/-!
# Geometric meaning of the trisection construction

The exact root choices describe two interior rays with three equal Mathlib
angles. Positive linear combinations certify interior placement; angles from
the first ray certify their order. A cubic equation alone is not the claim.
-/

namespace LeanOrigami.Trisection
open InnerProductGeometry

/-- A direction strictly inside the cone spanned by two noncollinear rays. -/
def InteriorRay (first second direction : Plane) : Prop :=
  ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ direction = a • first + b • second

/-- Two ordered interior trisectors of an angle strictly between zero and π.
Endpoints are normalized to one unit from the vertex. -/
def IsTrisection (vertex first second firstOutput secondOutput : Point ℝ) : Prop :=
  let a := first.toPlane-vertex.toPlane
  let b := second.toPlane-vertex.toPlane
  let x := firstOutput.toPlane-vertex.toPlane
  let y := secondOutput.toPlane-vertex.toPlane
  let θ := angle a b
  0 < θ ∧ θ < Real.pi ∧ ‖x‖ = 1 ∧ ‖y‖ = 1 ∧
    InteriorRay a b x ∧ InteriorRay a b y ∧
    angle a x = θ/3 ∧ angle x y = θ/3 ∧ angle y b = θ/3 ∧ angle a y = 2*θ/3

private noncomputable def direction (u w : Plane) (φ : ℝ) : Plane :=
  Real.cos φ • u + Real.sin φ • w

private theorem direction_inner (u w : Plane) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (horth : inner ℝ u w = 0) (α β : ℝ) :
    inner ℝ (direction u w α) (direction u w β) = Real.cos (β-α) := by
  have hrev : inner ℝ w u = 0 := by rw [real_inner_comm]; exact horth
  simp [direction, inner_add_left, inner_add_right, real_inner_smul_left, inner_smul_right,
    hu, hw, horth, hrev, Real.cos_sub]

private theorem direction_norm (u w : Plane) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (horth : inner ℝ u w = 0) (φ : ℝ) : ‖direction u w φ‖ = 1 := by
  have h := direction_inner u w hu hw horth φ φ
  rw [real_inner_self_eq_norm_sq, sub_self, Real.cos_zero] at h
  nlinarith [norm_nonneg (direction u w φ)]

private theorem angle_directions (u w : Plane) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (horth : inner ℝ u w = 0) (α β : ℝ) (hgap : 0 ≤ β-α ∧ β-α ≤ Real.pi) :
    angle (direction u w α) (direction u w β) = β-α := by
  apply Real.injOn_cos ⟨angle_nonneg _ _, angle_le_pi _ _⟩ hgap
  rw [cos_angle, direction_norm u w hu hw horth α,
    direction_norm u w hu hw horth β, direction_inner u w hu hw horth]
  simp

private theorem direction_interior (u w : Plane) (θ φ : ℝ)
    (hθ : 0 < θ ∧ θ < Real.pi) (hφ : 0 < φ ∧ φ < θ) :
    InteriorRay u (direction u w θ) (direction u w φ) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hp := Real.sin_pos_of_pos_of_lt_pi hφ.1 (hφ.2.trans hθ.2)
  have hd := Real.sin_pos_of_pos_of_lt_pi (by linarith : 0 < θ-φ)
    (by linarith : θ-φ < Real.pi)
  refine ⟨Real.sin (θ-φ)/Real.sin θ, Real.sin φ/Real.sin θ,
    div_pos hd hs, div_pos hp hs, ?_⟩
  ext i
  change Real.cos φ*u i + Real.sin φ*w i =
    (Real.sin (θ-φ)/Real.sin θ)*u i +
      (Real.sin φ/Real.sin θ)*(Real.cos θ*u i+Real.sin θ*w i)
  rw [Real.sin_sub]
  field_simp
  ring

private theorem unitVector_toPlane (vertex endpoint : Point ℝ) (length : ℝ) :
    (unitVector vertex endpoint length).toPlane =
      length⁻¹ • (endpoint.toPlane-vertex.toPlane) := by
  ext i
  fin_cases i <;> simp [unitVector, Point.toPlane, div_eq_mul_inv, mul_comm]

private theorem norm_one (u : Point ℝ) (h : u.sqNorm = 1) : ‖u.toPlane‖ = 1 := by
  rw [Point.sqNorm_eq_norm_sq] at h
  nlinarith [norm_nonneg u.toPlane]

private theorem interior_of_normalized (a b z : Plane) (l m : ℝ) (hl : 0 < l) (hm : 0 < m)
    (h : InteriorRay (l⁻¹ • a) (m⁻¹ • b) z) : InteriorRay a b z := by
  obtain ⟨α, β, hα, hβ, he⟩ := h
  refine ⟨α/l, β/m, div_pos hα hl, div_pos hβ hm, ?_⟩
  simpa [smul_smul, div_eq_mul_inv] using he

/-- The polynomial root choices produce both actual interior trisectors.
This statement includes the three equal angles, their order, and strict
interior placement, for arbitrary translated, rotated, or scaled inputs. -/
theorem Roots.isTrisection (roots : Roots ℝ) (vertex first second : Point ℝ)
    (h : roots.Valid vertex first second) :
    IsTrisection vertex first second (roots.firstPoint vertex first second)
      (roots.secondPoint vertex first second) := by
  let a := first.toPlane-vertex.toPlane
  let b := second.toPlane-vertex.toPlane
  let u := unitVector vertex first roots.firstLength
  let v := unitVector vertex second roots.secondLength
  let w := roots.perpendicularUnit vertex first second
  let c := roots.cosine vertex first second
  let θ := angle u.toPlane v.toPlane
  have hf := roots.frame vertex first second h
  change u.sqNorm = 1 ∧ w.sqNorm = 1 ∧ u.dot w = 0 ∧
    v = (c*u.1+roots.sine*w.1, c*u.2+roots.sine*w.2) at hf
  rcases h with ⟨ha, ha2, hb, hb2, hs, hs2, ht, _ht1, ht3, hr, hr2⟩
  have hu := norm_one u hf.1
  have hv := norm_one v (unitVector_sqNorm _ _ _ (ne_of_gt hb) hb2)
  have hw := norm_one w hf.2.1
  have horth : inner ℝ u.toPlane w.toPlane = 0 := by
    rw [← Point.dot_eq_inner]
    exact hf.2.2.1
  have hua : u.toPlane = roots.firstLength⁻¹ • a := unitVector_toPlane _ _ _
  have hvb : v.toPlane = roots.secondLength⁻¹ • b := unitVector_toPlane _ _ _
  have hcos : Real.cos θ = c := by
    dsimp [θ]
    rw [cos_angle, hu, hv]
    simpa [c, Roots.cosine, u, v] using (Point.dot_eq_inner u v).symm
  change roots.sine^2 = 1-c^2 at hs2
  have hc : -1 < c ∧ c < 1 := by
    have hp := sq_pos_of_ne_zero (ne_of_gt hs)
    constructor <;> nlinarith [sq_nonneg (c-1), sq_nonneg (c+1)]
  have hθ : 0 < θ ∧ θ < Real.pi := by
    have h0 : 0 ≤ θ := angle_nonneg _ _
    have hp : θ ≤ Real.pi := angle_le_pi _ _
    constructor
    · by_contra hn
      have he : θ = 0 := by linarith
      have hh := hcos
      rw [he, Real.cos_zero] at hh
      linarith [hc.2]
    · by_contra hn
      have he : θ = Real.pi := by linarith
      have hh := hcos
      rw [he, Real.cos_pi] at hh
      linarith [hc.1]
  have hsin : Real.sin θ = roots.sine := by
    apply (sq_eq_sq₀ (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le hθ.2.le) hs.le).mp
    have he := Real.sin_sq_add_cos_sq θ
    rw [hcos] at he
    nlinarith
  have hthird : 1/2 < Real.cos (θ/3) := by
    have he := Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith : 0 ≤ θ/3)
      (by linarith [Real.pi_pos] : Real.pi/3 ≤ Real.pi) (by linarith : θ/3 < Real.pi/3)
    simpa [Real.cos_pi_div_three] using he
  have hthirdPoly : 4*Real.cos (θ/3)^3-3*Real.cos (θ/3) = c := by
    have he := Real.cos_three_mul (θ/3)
    rw [show 3*(θ/3) = θ by ring, hcos] at he
    linarith
  have htEq : roots.thirdCosine = Real.cos (θ/3) :=
    thirdCosine_unique ht hthird ht3 hthirdPoly
  have hrEq : roots.thirdSine = Real.sin (θ/3) := by
    have hp := Real.sin_pos_of_pos_of_lt_pi (by linarith : 0 < θ/3)
      (by linarith [Real.pi_pos] : θ/3 < Real.pi)
    apply (sq_eq_sq₀ hr.le hp.le).mp
    rw [htEq] at hr2
    nlinarith [Real.sin_sq_add_cos_sq (θ/3)]
  have h0 : direction u.toPlane w.toPlane 0 = u.toPlane := by simp [direction]
  have hvdir : v.toPlane = direction u.toPlane w.toPlane θ := by
    ext i
    fin_cases i
    · change v.1 = Real.cos θ*u.1 + Real.sin θ*w.1
      rw [hcos, hsin]
      exact congrArg Prod.fst hf.2.2.2
    · change v.2 = Real.cos θ*u.2 + Real.sin θ*w.2
      rw [hcos, hsin]
      exact congrArg Prod.snd hf.2.2.2
  have hx : (roots.firstPoint vertex first second).toPlane-vertex.toPlane =
      direction u.toPlane w.toPlane (θ/3) := by
    ext i
    fin_cases i
    · change (vertex.1+roots.thirdCosine*u.1+roots.thirdSine*w.1)-vertex.1 =
        Real.cos (θ/3)*u.1+Real.sin (θ/3)*w.1
      rw [htEq, hrEq]
      ring
    · change (vertex.2+roots.thirdCosine*u.2+roots.thirdSine*w.2)-vertex.2 =
        Real.cos (θ/3)*u.2+Real.sin (θ/3)*w.2
      rw [htEq, hrEq]
      ring
  have hy : (roots.secondPoint vertex first second).toPlane-vertex.toPlane =
      direction u.toPlane w.toPlane (2*θ/3) := by
    ext i
    fin_cases i
    · change (vertex.1+(2*roots.thirdCosine^2-1)*u.1+
          2*roots.thirdCosine*roots.thirdSine*w.1)-vertex.1 =
        Real.cos (2*θ/3)*u.1+Real.sin (2*θ/3)*w.1
      rw [show 2*θ/3 = 2*(θ/3) by ring, Real.cos_two_mul, Real.sin_two_mul, htEq, hrEq]
      ring
    · change (vertex.2+(2*roots.thirdCosine^2-1)*u.2+
          2*roots.thirdCosine*roots.thirdSine*w.2)-vertex.2 =
        Real.cos (2*θ/3)*u.2+Real.sin (2*θ/3)*w.2
      rw [show 2*θ/3 = 2*(θ/3) by ring, Real.cos_two_mul, Real.sin_two_mul, htEq, hrEq]
      ring
  have hθoriginal : angle a b = θ := by
    dsimp [θ]
    rw [hua, hvb, angle_smul_left_of_pos _ _ (inv_pos.mpr ha),
      angle_smul_right_of_pos _ _ (inv_pos.mpr hb)]
  have interior (φ : ℝ) (hp : 0 < φ ∧ φ < θ) : InteriorRay a b (direction u.toPlane w.toPlane φ) := by
    have hi := direction_interior u.toPlane w.toPlane θ φ hθ hp
    rw [← hvdir] at hi
    apply interior_of_normalized a b _ _ _ ha hb
    simpa only [hua, hvb] using hi
  change 0 < angle a b ∧ angle a b < Real.pi ∧ _
  rw [hθoriginal, hx, hy]
  refine ⟨hθ.1, hθ.2, direction_norm _ _ hu hw horth _, direction_norm _ _ hu hw horth _,
    interior _ ⟨by linarith, by linarith⟩, interior _ ⟨by linarith, by linarith⟩,
    ?_, ?_, ?_, ?_⟩
  · have he := angle_directions _ _ hu hw horth 0 (θ/3) ⟨by linarith, by linarith⟩
    rw [h0, hua, angle_smul_left_of_pos _ _ (inv_pos.mpr ha)] at he
    simpa only [← hua, sub_zero] using he
  · have he := angle_directions _ _ hu hw horth (θ/3) (2*θ/3) ⟨by linarith, by linarith⟩
    convert he using 1
    ring
  · have he := angle_directions _ _ hu hw horth (2*θ/3) θ ⟨by linarith, by linarith⟩
    rw [← hvdir, hvb, angle_smul_right_of_pos _ _ (inv_pos.mpr hb)] at he
    convert he using 1
    ring
  · have he := angle_directions _ _ hu hw horth 0 (2*θ/3) ⟨by linarith, by linarith⟩
    rw [h0, hua, angle_smul_left_of_pos _ _ (inv_pos.mpr ha)] at he
    simpa only [← hua, sub_zero] using he

end LeanOrigami.Trisection
