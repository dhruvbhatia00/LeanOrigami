import LeanOrigami.Solvers.LineLine
import Mathlib.Analysis.Real.Sqrt

/-!
# Exactly two folds for intersecting lines

The direction equation has two distinct real directions. Neither direction
loses the offset constraint when the input lines intersect. This strengthens
the general two-crease bound to an exact classification; parallel and
coincident cases are handled in `LineLine.lean`.
-/

namespace LeanOrigami.FoldInput

private theorem direction_dot_ne (l m : Line ℝ) (hd : l.determinant m ≠ 0) (t : ℝ)
    (ht : l.directionCross m*(1-t^2)-2*l.directionDifference m*t = 0) : m.chartDot t ≠ 0 := by
  intro hz
  have he : l.directionCross m*(1-t^2)-2*l.directionDifference m*t =
      l.determinant m*(1+t^2)+2*m.chartDot t*(l.b-l.a*t) := by
    dsimp [Line.directionCross, Line.directionDifference, Line.determinant, Line.chartDot]
    ring
  rw [ht, hz, mul_zero, zero_mul, add_zero] at he
  exact hd ((mul_eq_zero.mp he.symm).resolve_right (by positivity))

private theorem chart_bisector (l m : Line ℝ) (hd : l.determinant m ≠ 0) (t : ℝ)
    (ht : l.directionCross m*(1-t^2)-2*l.directionDifference m*t = 0) :
    (axiom3 l m).Satisfies (Line.chart t ((l.pointAt 0).1+t*(l.pointAt 0).2-
      m.residual (l.pointAt 0)*(1+t^2)/(2*m.chartDot t))) := by
  apply (axiom3_iff_equations l m _).mpr
  refine ⟨(Line.alignment_chart_iff_offset m _ _ _ (direction_dot_ne l m hd t ht)).mpr rfl, ?_⟩
  simpa [Line.chart] using ht

private theorem two_quadratic_directions (s d : ℝ) (hs : s ≠ 0) :
    ∃ r u, r ≠ u ∧ s*(1-r^2)-2*d*r = 0 ∧ s*(1-u^2)-2*d*u = 0 := by
  let v := Real.sqrt (d^2+s^2)
  have hv : v^2 = d^2+s^2 := Real.sq_sqrt (by positivity)
  have hvpos : 0 < v := Real.sqrt_pos.mpr (by positivity)
  refine ⟨(-d+v)/s, (-d-v)/s, ?_, ?_, ?_⟩
  · intro he
    have h := (div_left_inj' hs).mp he
    linarith
  · field_simp
    linear_combination -hv
  · field_simp
    linear_combination -hv

/-- Intersecting input lines give exactly two distinct crease choices. -/
theorem axiom3_intersecting_exactly_two (l m : Line ℝ) (hd : l.determinant m ≠ 0) :
    ∃ first second : Line ℝ, first ≠ second ∧ (axiom3 l m).solutions = {first, second} := by
  have hlm : l ≠ m := by
    rintro rfl
    exact hd (by simp [Line.determinant])
  have hex : ∃ first second : Line ℝ, first ≠ second ∧
      (axiom3 l m).Satisfies first ∧ (axiom3 l m).Satisfies second := by
    by_cases hs : l.directionCross m = 0
    · have hmb : m.b ≠ 0 := by
        intro hb
        apply hd
        dsimp [Line.directionCross] at hs
        dsimp [Line.determinant]
        rw [hb] at hs ⊢
        nlinarith
      let first := Line.chart 0 ((l.pointAt 0).1-m.residual (l.pointAt 0)/(2*m.chartDot 0))
      let second := Line.horizontal ((l.pointAt 0).2-m.residual (l.pointAt 0)/(2*m.b))
      refine ⟨first, second, ?_, ?_, ?_⟩
      · intro he
        have h := congrArg Line.a he
        norm_num [first, second, Line.chart, Line.horizontal] at h
      · simpa [first] using chart_bisector l m hd 0 (by simp [hs])
      · apply (axiom3_iff_equations l m second).mpr
        constructor
        · dsimp [second]
          rw [Line.alignmentEquation_horizontal]
          field_simp
          ring
        · simp [second, Line.horizontal, hs]
    · obtain ⟨r, u, hru, hr, hu⟩ := two_quadratic_directions _ _ hs
      let candidate (t : ℝ) := Line.chart t ((l.pointAt 0).1+t*(l.pointAt 0).2-
        m.residual (l.pointAt 0)*(1+t^2)/(2*m.chartDot t))
      refine ⟨candidate r, candidate u, ?_, chart_bisector l m hd r hr, chart_bisector l m hd u hu⟩
      exact fun he => hru (congrArg Line.b he)
  obtain ⟨first, second, hne, hf, hs⟩ := hex
  obtain ⟨a, b, hab⟩ := axiom3_solutions_subset_pair l m hlm
  refine ⟨first, second, hne, Set.Subset.antisymm ?_ ?_⟩
  · intro crease hc
    have h₁ := hab hf
    have h₂ := hab hs
    have h₃ := hab hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h₁ h₂ h₃ ⊢
    aesop
  · intro crease hc
    rcases hc with rfl | rfl
    · exact hf
    · exact hs

end LeanOrigami.FoldInput
