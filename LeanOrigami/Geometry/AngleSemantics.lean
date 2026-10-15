import LeanOrigami.Geometry.Angles
import LeanOrigami.Geometry.Euclidean
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# Real meaning of exact angle conditions

The polynomial predicates agree with Mathlib's angle of vectors. Lines use
the smaller angle in `[0, π/2]`; rays use the angle in `[0, π]`. Trigonometry
appears only in these specifications and proofs, never in condition execution.
-/

namespace LeanOrigami
open InnerProductGeometry

namespace Point

/-- Coordinate and Euclidean dot products coincide. -/
theorem dot_eq_inner (u v : Point ℝ) : u.dot v = inner ℝ u.toPlane v.toPlane := by
  simp [dot, toPlane, PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

/-- Coordinate squared length is the squared Euclidean norm. -/
theorem sqNorm_eq_norm_sq (u : Point ℝ) : u.sqNorm = ‖u.toPlane‖^2 := by
  simp [sqNorm, toPlane, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

/-- Coordinate interpretation preserves the zero direction. -/
theorem toPlane_eq_zero_iff (u : Point ℝ) : u.toPlane = 0 ↔ u = 0 := by
  have hz : (0 : Point ℝ).toPlane = 0 := by
    ext i
    fin_cases i <;> rfl
  exact ⟨fun h => toPlane_injective (h.trans hz.symm), fun h => h ▸ hz⟩

/-- Reversing a coordinate direction reverses its Euclidean interpretation. -/
@[simp] theorem toPlane_neg (u : Point ℝ) : (-u).toPlane = -u.toPlane := by
  ext i
  fin_cases i <;> rfl

/-- Displacements are interpreted as Euclidean vector differences. -/
@[simp] theorem toPlane_sub (u v : Point ℝ) : (u-v).toPlane = u.toPlane-v.toPlane := by
  ext i
  fin_cases i <;> rfl

end Point

/-- Forget the signs of two directions and take their smaller line angle. -/
noncomputable def unorientedAngle (u v : Plane) : ℝ :=
  min (angle u v) (Real.pi - angle u v)

/-- Unoriented angles always lie between zero and a right angle. -/
theorem unorientedAngle_bounds (u v : Plane) :
    0 ≤ unorientedAngle u v ∧ unorientedAngle u v ≤ Real.pi/2 := by
  have h0 := angle_nonneg u v
  have hp := angle_le_pi u v
  constructor
  · exact le_min h0 (by linarith)
  · by_cases h : angle u v ≤ Real.pi/2
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans (by linarith)

/-- The smaller angle between the nonzero directions of two lines. -/
noncomputable def Line.smallerAngle (l m : Line ℝ) : ℝ :=
  unorientedAngle l.directionVector m.directionVector

namespace NamedAngle

/-- The intended real angle, used only for mathematical interpretation. -/
noncomputable def radians : NamedAngle → ℝ
  | .thirty => Real.pi / 6
  | .fortyFive => Real.pi / 4
  | .sixty => Real.pi / 3

/-- All advertised named angles are strictly acute. -/
theorem radians_bounds (a : NamedAngle) : 0 < a.radians ∧ a.radians < Real.pi/2 := by
  cases a <;> dsimp [radians] <;> constructor <;> linarith [Real.pi_pos]

/-- The integer coefficient in the exact predicate is the intended squared cosine. -/
theorem cosineNumerator_eq (a : NamedAngle) :
    (a.cosineNumerator : ℝ) = 4 * Real.cos a.radians ^ 2 := by
  cases a <;> simp only [radians, cosineNumerator]
  · rw [Real.cos_pi_div_six]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  · rw [Real.cos_pi_div_four]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  · rw [Real.cos_pi_div_three]
    norm_num

private theorem acute_angle_iff (u v : Plane) (hu : u ≠ 0) (hv : v ≠ 0)
    (θ : ℝ) (hθ : 0 < θ ∧ θ < Real.pi/2) :
    angle u v = θ ↔ 0 < inner ℝ u v ∧
      (inner ℝ u v)^2 = Real.cos θ^2 * ‖u‖^2 * ‖v‖^2 := by
  have hn : 0 < ‖u‖ * ‖v‖ := mul_pos (norm_pos_iff.mpr hu) (norm_pos_iff.mpr hv)
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ.2⟩
  have hid := cos_angle_mul_norm_mul_norm u v
  constructor
  · intro h
    rw [h] at hid
    rw [← hid]
    exact ⟨mul_pos hc hn, by ring⟩
  · rintro ⟨hi, he⟩
    have he' : inner ℝ u v = Real.cos θ * (‖u‖ * ‖v‖) := by
      apply (sq_eq_sq₀ hi.le (mul_pos hc hn).le).mp
      nlinarith [he]
    have hcos : Real.cos (angle u v) = Real.cos θ :=
      mul_right_cancel₀ (ne_of_gt hn) (hid.trans he')
    exact Real.injOn_cos ⟨angle_nonneg u v, angle_le_pi u v⟩
      ⟨hθ.1.le, by linarith⟩ hcos

/-- The exact ray predicate excludes degenerate rays and identifies the actual
Mathlib angle, including the sign needed to reject its supplement. -/
theorem rays_iff_angle (a : NamedAngle) (u v : Point ℝ) :
    a.Rays u v ↔ u ≠ 0 ∧ v ≠ 0 ∧ angle u.toPlane v.toPlane = a.radians := by
  constructor
  · rintro ⟨⟨hu, hv, he⟩, hd⟩
    have hu' := (Point.sqNorm_pos_iff u).mp hu
    have hv' := (Point.sqNorm_pos_iff v).mp hv
    refine ⟨hu', hv', (acute_angle_iff _ _
      (mt (Point.toPlane_eq_zero_iff u).mp hu')
      (mt (Point.toPlane_eq_zero_iff v).mp hv') _ a.radians_bounds).mpr ?_⟩
    rw [← Point.dot_eq_inner, ← Point.sqNorm_eq_norm_sq, ← Point.sqNorm_eq_norm_sq]
    rw [a.cosineNumerator_eq] at he
    exact ⟨hd, by nlinarith [he]⟩
  · rintro ⟨hu, hv, hangle⟩
    have h := (acute_angle_iff _ _ (mt (Point.toPlane_eq_zero_iff u).mp hu)
      (mt (Point.toPlane_eq_zero_iff v).mp hv) _ a.radians_bounds).mp hangle
    rw [← Point.dot_eq_inner, ← Point.sqNorm_eq_norm_sq, ← Point.sqNorm_eq_norm_sq] at h
    refine ⟨⟨(Point.sqNorm_pos_iff u).mpr hu, (Point.sqNorm_pos_iff v).mpr hv, ?_⟩, h.1⟩
    rw [a.cosineNumerator_eq]
    nlinarith [h.2]

/-- The unsigned polynomial allows precisely the two signs of a ray direction. -/
private theorem unoriented_iff_rays (a : NamedAngle) (u v : Point ℝ) :
    a.Unoriented u v ↔ a.Rays u v ∨ a.Rays u (-v) := by
  have hn : a.Unoriented u (-v) ↔ a.Unoriented u v := by
    have hv : (-v.1, -v.2) = -v := by ext <;> rfl
    simpa [hv] using a.unoriented_scale_iff u v 1 (-1) (by norm_num) (by norm_num)
  have hd : u.dot (-v) = -u.dot v := by simp [Point.dot, mul_neg, add_comm]
  constructor
  · intro h
    have hc : 0 < (a.cosineNumerator : ℝ) := by cases a <;> norm_num [cosineNumerator]
    have hp := mul_pos (mul_pos hc h.1) h.2.1
    have hz : u.dot v ≠ 0 := by
      intro hz
      have he := h.2.2
      rw [hz] at he
      nlinarith
    rcases lt_or_gt_of_ne hz with hneg | hpos
    · exact Or.inr ⟨hn.mpr h, by rw [hd]; linarith⟩
    · exact Or.inl ⟨h, hpos⟩
  · rintro (h | h)
    · exact h.1
    · exact hn.mp h.1

/-- The unsigned predicate means the smaller line angle, not an arbitrary
angle having the same squared cosine. -/
theorem unoriented_iff_angle (a : NamedAngle) (u v : Point ℝ) :
    a.Unoriented u v ↔
      u ≠ 0 ∧ v ≠ 0 ∧ unorientedAngle u.toPlane v.toPlane = a.radians := by
  rw [unoriented_iff_rays, rays_iff_angle, rays_iff_angle, Point.toPlane_neg,
    angle_neg_right, neg_ne_zero]
  simp only [← and_or_left]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  dsimp [unorientedAngle]
  have ha := a.radians_bounds
  constructor
  · rintro (h | h)
    · rw [h]
      exact min_eq_left (by linarith)
    · have he : angle u.toPlane v.toPlane = Real.pi-a.radians := by linarith
      rw [he, show Real.pi-(Real.pi-a.radians) = a.radians by ring]
      exact min_eq_right (by linarith)
  · intro h
    by_cases hle : angle u.toPlane v.toPlane ≤ Real.pi-angle u.toPlane v.toPlane
    · left
      simpa [min_def, hle] using h
    · right
      simpa [min_def, hle] using h

/-- Exact line coefficients agree with the angle of their Euclidean tangent
directions. Vertical lines require no separate slope convention. -/
theorem lines_iff_angle (a : NamedAngle) (l m : Line ℝ) :
    a.Lines l m ↔ l.smallerAngle m = a.radians := by
  have hl : (-l.b, l.a) ≠ (0 : Point ℝ) := (Point.sqNorm_pos_iff _).mp
    (by simpa [Point.sqNorm, Line.normalSq, add_comm] using l.normalSq_pos)
  have hm : (-m.b, m.a) ≠ (0 : Point ℝ) := (Point.sqNorm_pos_iff _).mp
    (by simpa [Point.sqNorm, Line.normalSq, add_comm] using m.normalSq_pos)
  have h := a.unoriented_iff_angle (-l.b, l.a) (-m.b, m.a)
  simpa [Lines, Unoriented, Point.sqNorm, Point.dot, Line.smallerAngle,
    Line.directionVector, hl, hm, add_comm] using h

/-- The ray form uses displacement vectors from the user-selected vertex. -/
theorem atVertex_iff_angle (a : NamedAngle) (vertex first second : Point ℝ) :
    a.AtVertex vertex first second ↔ first ≠ vertex ∧ second ≠ vertex ∧
      angle (first.toPlane-vertex.toPlane) (second.toPlane-vertex.toPlane) = a.radians := by
  simpa [AtVertex, sub_ne_zero] using a.rays_iff_angle (first-vertex) (second-vertex)

end NamedAngle
end LeanOrigami
