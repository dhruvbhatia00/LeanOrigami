import LeanOrigami.Solvers.Equations
import LeanOrigami.Solvers.PointLine

/-!
# Line-to-line folding

Reflection of a whole line is checked by its equation. The direction equation
is quadratic; the offset is then unique unless the input lines coincide.
Horizontal creases are handled separately from the nonhorizontal chart.
-/

namespace LeanOrigami
namespace Line
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Squared length of the reflected normal after clearing denominators. -/
theorem reflected_normal_sq (crease target : Line K) :
    (target.a * crease.normalSq -
      2 * (target.a * crease.a + target.b * crease.b) * crease.a)^2 +
    (target.b * crease.normalSq -
      2 * (target.a * crease.a + target.b * crease.b) * crease.b)^2 =
      target.normalSq * crease.normalSq^2 := by
  dsimp [normalSq]
  ring

/-- The image (equivalently preimage) of a line under a reflection. -/
def reflected (crease target : Line K) : Line K :=
  let d := target.a * crease.a + target.b * crease.b
  normalize (target.a * crease.normalSq - 2*d*crease.a)
    (target.b * crease.normalSq - 2*d*crease.b)
    (target.c * crease.normalSq - 2*d*crease.c) (by
      by_contra h
      push Not at h
      have hs := reflected_normal_sq crease target
      have hp : 0 < target.normalSq * crease.normalSq^2 :=
        mul_pos target.normalSq_pos (sq_pos_of_ne_zero crease.normalSq_ne_zero)
      change target.a * crease.normalSq - 2*d*crease.a = 0 ∧
        target.b * crease.normalSq - 2*d*crease.b = 0 at h
      change _ + _ = target.normalSq * crease.normalSq^2 at hs
      rw [h.1, h.2] at hs
      nlinarith)

/-- The computed line is precisely the reflected target set. -/
theorem contains_reflected (crease target : Line K) (p : Point K) :
    (crease.reflected target).Contains p ↔ target.Contains (crease.reflect p) := by
  rw [reflected, contains_normalize, ← alignmentEquation_zero_iff]
  dsimp [alignmentEquation, residual]
  constructor <;> intro h <;> nlinarith [h]

omit [IsStrictOrderedRing K] in
/-- Distinct parameters give distinct points on a line. -/
theorem pointAt_injective (l : Line K) : Function.Injective l.pointAt := by
  intro t u h
  by_cases ha : l.a = 0
  · simpa only [pointAt, ha, ite_true] using congrArg Prod.fst h
  · simpa only [pointAt, ha, ite_false] using congrArg Prod.snd h

/-- The direction coefficients in the line-to-line quadratic. -/
def directionCross (l m : Line K) : K := l.a*m.b + l.b*m.a

/-- The other coefficient in the direction quadratic. -/
def directionDifference (l m : Line K) : K := l.a*m.a - l.b*m.b

/-- The two direction coefficients cannot both vanish. -/
theorem direction_coefficients_ne (l m : Line K) :
    l.directionCross m ≠ 0 ∨ l.directionDifference m ≠ 0 := by
  have hidentity : (l.directionCross m)^2 + (l.directionDifference m)^2 =
      l.normalSq * m.normalSq := by
    dsimp [directionCross, directionDifference, normalSq]
    ring
  have hp := mul_pos l.normalSq_pos m.normalSq_pos
  by_contra h
  push Not at h
  rw [h.1, h.2] at hidentity
  nlinarith

/-- The difference of two incidence equations is the direction equation. -/
theorem alignment_pointAt_difference (l m crease : Line K) :
    crease.alignmentEquation m (l.pointAt 1) - crease.alignmentEquation m (l.pointAt 0) =
      if l.a = 0 then
        -(l.directionCross m * (crease.a^2-crease.b^2) -
          2*l.directionDifference m*crease.a*crease.b)
      else l.directionCross m * (crease.a^2-crease.b^2) -
          2*l.directionDifference m*crease.a*crease.b := by
  rcases l.normalized with ha | ⟨ha, hb⟩
  · simp only [pointAt, ha, one_ne_zero, ite_false, mul_zero, sub_zero, mul_one]
    dsimp [alignmentEquation, residual, normalSq, directionCross, directionDifference]
    rw [ha]
    ring
  · simp only [pointAt, ha, ite_true]
    dsimp [alignmentEquation, residual, normalSq, directionCross, directionDifference]
    rw [ha, hb]
    ring

/-- The line parameterization commutes with a coordinate-field embedding. -/
theorem pointAt_map {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L]
    (f : K →+* L) (l : Line K) (t : K) :
    (l.map f).pointAt (f t) = (f (l.pointAt t).1, f (l.pointAt t).2) := by
  rcases l.normalized with ha | ⟨ha, hb⟩ <;>
    simp [pointAt, map, ha, map_sub, map_mul]

/-- Parallel canonical lines have identical normal coefficients. -/
theorem normal_eq_of_determinant_zero (l m : Line K) (h : l.determinant m = 0) :
    l.a = m.a ∧ l.b = m.b := by
  rcases l.normalized with ha | ⟨ha, hb⟩ <;>
    rcases m.normalized with hc | ⟨hc, hd⟩ <;> simp_all [determinant, sub_eq_zero]

/-- The midway parallel line. Its reflection property requires parallel inputs. -/
def parallelMidline (l m : Line K) : Line K :=
  ⟨l.a, l.b, (l.c+m.c)/2, l.normalized⟩

end Line
namespace FoldInput
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Whole-line reflection is equality with the computed reflected line. -/
theorem axiom3_iff_reflected (l m crease : Line K) :
    (axiom3 l m).Satisfies crease ↔ l = crease.reflected m := by
  simp only [Satisfies, ← Line.contains_reflected, ← Line.eq_iff_contains]

/-- Two distinct source points suffice to check reflection of the entire line. -/
theorem axiom3_iff_two_points (l m crease : Line K) :
    (axiom3 l m).Satisfies crease ↔
      m.Contains (crease.reflect (l.pointAt 0)) ∧
      m.Contains (crease.reflect (l.pointAt 1)) := by
  constructor
  · intro h
    exact ⟨(h _).mp (l.pointAt_mem 0), (h _).mp (l.pointAt_mem 1)⟩
  · rintro ⟨h₀, h₁⟩
    apply (axiom3_iff_reflected l m crease).mpr
    exact Line.eq_of_common_points l (crease.reflected m) _ _
      (fun h => zero_ne_one (l.pointAt_injective h))
      (l.pointAt_mem 0) (l.pointAt_mem 1)
      ((Line.contains_reflected _ _ _).mpr h₀)
      ((Line.contains_reflected _ _ _).mpr h₁)

/-- All primitive relations have executable exact checks. For rule 3, two
source points certify the universally quantified whole-line condition. -/
instance (input : FoldInput K) (crease : Line K) : Decidable (input.Satisfies crease) := by
  cases input with
  | axiom3 l m =>
    exact decidable_of_iff
      (m.Contains (crease.reflect (l.pointAt 0)) ∧ m.Contains (crease.reflect (l.pointAt 1)))
      (axiom3_iff_two_points l m crease).symm
  | _ => dsimp [Satisfies]; infer_instance

/-- Whole-line reflection transports through embeddings even when their
images do not exhaust the receiving field. No preservation of order is assumed. -/
theorem axiom3_map {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L]
    (f : K →+* L) (l m crease : Line K) (h : (axiom3 l m).Satisfies crease) :
    (axiom3 (l.map f) (m.map f)).Satisfies (crease.map f) := by
  rw [axiom3_iff_two_points] at h ⊢
  have h₀ := Line.pointAt_map f l 0
  have h₁ := Line.pointAt_map f l 1
  simp only [map_zero] at h₀
  simp only [map_one] at h₁
  rw [h₀, h₁, Line.reflect_map, Line.reflect_map]
  exact ⟨(Line.contains_map f _ _).mpr h.1, (Line.contains_map f _ _).mpr h.2⟩

/-- A crease perpendicular to the target preserves that target as a whole set. -/
theorem axiom3_perpendicular_iff (l m crease : Line K) (hd : crease.Perpendicular m) :
    (axiom3 l m).Satisfies crease ↔ l = m := by
  have hdot : m.a*crease.a + m.b*crease.b = 0 :=
    (Line.perpendicular_comm crease m).mp hd
  have hm (p : Point K) : m.Contains (crease.reflect p) ↔ m.Contains p := by
    rw [← Line.alignmentEquation_zero_iff]
    simp only [Line.alignmentEquation, hdot, mul_zero, sub_zero, mul_eq_zero,
      crease.normalSq_ne_zero, or_false, Line.residual_eq_zero]
  simpa only [Satisfies, hm] using Line.eq_iff_contains l m |>.symm

/-- Distinct input lines force a nonzero normal dot product for every solution. -/
theorem axiom3_dot_ne (l m crease : Line K) (hlm : l ≠ m)
    (h : (axiom3 l m).Satisfies crease) : m.a*crease.a + m.b*crease.b ≠ 0 := by
  intro hd
  have hp : crease.Perpendicular m := (Line.perpendicular_comm crease m).mpr hd
  exact hlm ((axiom3_perpendicular_iff l m crease hp).mp h)

/-- Every line-to-line crease satisfies the quadratic direction equation. -/
theorem axiom3_direction (l m crease : Line K) (h : (axiom3 l m).Satisfies crease) :
    l.directionCross m * (crease.a^2 - crease.b^2) -
      2*l.directionDifference m*crease.a*crease.b = 0 := by
  have h₀ := (Line.alignmentEquation_zero_iff crease m _).mpr
    ((h _).mp (l.pointAt_mem 0))
  have h₁ := (Line.alignmentEquation_zero_iff crease m _).mpr
    ((h _).mp (l.pointAt_mem 1))
  have hd := Line.alignment_pointAt_difference l m crease
  by_cases ha : l.a = 0 <;> simp [h₀, h₁, ha] at hd <;> linarith

/-- One incidence equation and the direction equation characterize the whole-line relation. -/
theorem axiom3_iff_equations (l m crease : Line K) :
    (axiom3 l m).Satisfies crease ↔
      crease.alignmentEquation m (l.pointAt 0) = 0 ∧
      l.directionCross m * (crease.a^2-crease.b^2) -
        2*l.directionDifference m*crease.a*crease.b = 0 := by
  constructor
  · intro h
    exact ⟨(Line.alignmentEquation_zero_iff _ _ _).mpr ((h _).mp (l.pointAt_mem 0)),
      axiom3_direction l m crease h⟩
  · rintro ⟨h₀, hd⟩
    apply (axiom3_iff_two_points l m crease).mpr
    refine ⟨(Line.alignmentEquation_zero_iff _ _ _).mp h₀, ?_⟩
    apply (Line.alignmentEquation_zero_iff _ _ _).mp
    have he := Line.alignment_pointAt_difference l m crease
    by_cases ha : l.a = 0 <;> simpa [h₀, hd, ha] using he

/-- In the nonhorizontal chart, the source's first point fixes the offset. -/
theorem axiom3_chart_offset (l m : Line K) (t c : K) (hlm : l ≠ m)
    (h : (axiom3 l m).Satisfies (Line.chart t c)) :
    c = (l.pointAt 0).1 + t*(l.pointAt 0).2 -
      m.residual (l.pointAt 0)*(1+t^2)/(2*m.chartDot t) := by
  apply (Line.alignment_chart_iff_offset m _ t c ?_).mp
  · exact (Line.alignmentEquation_zero_iff _ _ _).mpr ((h _).mp (l.pointAt_mem 0))
  · simpa [Line.chart, Line.chartDot] using axiom3_dot_ne l m _ hlm h

/-- The horizontal chart also has a unique offset for distinct input lines. -/
theorem axiom3_horizontal_offset (l m : Line K) (c : K) (hlm : l ≠ m)
    (h : (axiom3 l m).Satisfies (Line.horizontal c)) :
    c = (l.pointAt 0).2 - m.residual (l.pointAt 0)/(2*m.b) := by
  have hd : m.b ≠ 0 := by
    simpa [Line.horizontal] using axiom3_dot_ne l m _ hlm h
  have he := (Line.alignmentEquation_zero_iff _ _ _).mpr ((h _).mp (l.pointAt_mem 0))
  rw [Line.alignmentEquation_horizontal] at he
  field_simp
  nlinarith

/-- Distinct source and target lines permit at most two real crease choices.
When a horizontal crease is possible, the direction polynomial loses degree. -/
theorem axiom3_solutions_subset_pair (l m : Line ℝ) (hlm : l ≠ m) :
    ∃ first second : Line ℝ, (axiom3 l m).solutions ⊆ {first, second} := by
  let candidate (t : ℝ) := Line.chart t ((l.pointAt 0).1 + t*(l.pointAt 0).2 -
    m.residual (l.pointAt 0)*(1+t^2)/(2*m.chartDot t))
  have hc (t c : ℝ) (h : (axiom3 l m).Satisfies (Line.chart t c)) :
      Line.chart t c = candidate t :=
    congrArg (Line.chart t) (axiom3_chart_offset l m t c hlm h)
  by_cases hs : l.directionCross m = 0
  · have ht : l.directionDifference m ≠ 0 :=
      (l.direction_coefficients_ne m).resolve_left (not_not.mpr hs)
    refine ⟨candidate 0,
      Line.horizontal ((l.pointAt 0).2 - m.residual (l.pointAt 0)/(2*m.b)), ?_⟩
    intro crease h
    rcases crease.chart_cases with he | he
    · have h' : (axiom3 l m).Satisfies (Line.chart crease.b crease.c) := he ▸ h
      have hd := axiom3_direction l m _ h'
      simp only [Line.chart, hs, zero_mul, zero_sub, one_pow, mul_one] at hd
      have hz : crease.b = 0 := by
        have hz : l.directionDifference m * crease.b = 0 := by nlinarith [hd]
        exact (mul_eq_zero.mp hz).resolve_left ht
      exact Or.inl (he.trans ((hc _ _ h').trans (congrArg candidate hz)))
    · have h' : (axiom3 l m).Satisfies (Line.horizontal crease.c) := he ▸ h
      exact Or.inr (he.trans (congrArg Line.horizontal
        (axiom3_horizontal_offset l m _ hlm h')))
  · obtain ⟨r, s, hrs⟩ := Univariate.quadratic_zeros_subset_pair
      (-l.directionCross m) (-2*l.directionDifference m) (l.directionCross m)
      (Or.inl (neg_ne_zero.mpr hs))
    refine ⟨candidate r, candidate s, ?_⟩
    intro crease h
    rcases crease.chart_cases with he | he
    · have h' : (axiom3 l m).Satisfies (Line.chart crease.b crease.c) := he ▸ h
      have hd := axiom3_direction l m _ h'
      simp only [Line.chart, one_pow, mul_one] at hd
      have hroot := hrs crease.b (by nlinarith [hd])
      have hcrease := he.trans (hc _ _ h')
      exact hroot.imp (fun hr => hcrease.trans (congrArg candidate hr))
        (fun hr => hcrease.trans (congrArg candidate hr))
    · have hd := axiom3_direction l m _ (he ▸ h)
      simp only [Line.horizontal, zero_pow (by decide : 2 ≠ 0), one_pow,
        zero_sub, mul_neg, mul_one, mul_zero, sub_zero, neg_eq_zero] at hd
      exact False.elim (hs hd)

/-- There are infinitely many parallel translates perpendicular to any given line. -/
theorem infinite_perpendicular_lines (l : Line ℝ) :
    {crease : Line ℝ | crease.Perpendicular l}.Infinite := by
  let family (c : ℝ) : Line ℝ :=
    if l.b = 0 then Line.horizontal c else Line.chart (-l.a/l.b) c
  have hinj : Function.Injective family := by
    intro c d h
    have he := congrArg Line.c h
    by_cases hb : l.b = 0 <;> simpa [family, hb, Line.chart, Line.horizontal] using he
  have hp (c : ℝ) : (family c).Perpendicular l := by
    by_cases hb : l.b = 0
    · simp [family, hb, Line.horizontal, Line.Perpendicular]
    · simp [family, hb, Line.chart, Line.Perpendicular]
  apply (Set.infinite_range_of_injective hinj).mono
  rintro crease ⟨c, rfl⟩
  exact hp c

/-- Coincident input lines leave infinitely many whole-line reflections. -/
theorem axiom3_same_not_admissible (l : Line ℝ) : ¬(axiom3 l l).Admissible := by
  apply (infinite_perpendicular_lines l).mono
  intro crease h
  exact (axiom3_perpendicular_iff l l crease h).mpr rfl

/-- Distinctness is the exact real finite-choice guard for rule 3. -/
theorem axiom3_admissible_iff (l m : Line ℝ) : (axiom3 l m).Admissible ↔ l ≠ m := by
  constructor
  · intro h heq
    subst m
    exact axiom3_same_not_admissible l h
  · intro h
    obtain ⟨first, second, hs⟩ := axiom3_solutions_subset_pair l m h
    exact (Set.toFinite ({first, second} : Set (Line ℝ))).subset hs

/-- Distinct parallel lines have exactly their midway line as a crease. -/
theorem axiom3_parallel_iff (l m crease : Line K) (hparallel : l.determinant m = 0)
    (hlm : l ≠ m) :
    (axiom3 l m).Satisfies crease ↔ crease = l.parallelMidline m := by
  obtain ⟨ha, hb⟩ := l.normal_eq_of_determinant_zero m hparallel
  have hp := l.pointAt_mem 0
  change l.a*(l.pointAt 0).1 + l.b*(l.pointAt 0).2 = l.c at hp
  rw [ha, hb] at hp
  constructor
  · intro h
    have hd := axiom3_dot_ne l m crease hlm h
    have he := axiom3_direction l m crease h
    dsimp [Line.directionCross, Line.directionDifference] at he
    rw [ha, hb] at he
    have hfactor : (2*(m.a*crease.a+m.b*crease.b)) *
        (crease.a*m.b-m.a*crease.b) = 0 := by linear_combination he
    have hdet : crease.determinant m = 0 :=
      (mul_eq_zero.mp hfactor).resolve_left (mul_ne_zero two_ne_zero hd)
    obtain ⟨hca, hcb⟩ := crease.normal_eq_of_determinant_zero m hdet
    have hc := ((axiom3_iff_equations l m crease).mp h).1
    dsimp [Line.alignmentEquation, Line.residual, Line.normalSq] at hc
    rw [hca, hcb, hp] at hc
    have hmul : (2*crease.c-l.c-m.c) * m.normalSq = 0 := by
      dsimp [Line.normalSq]
      linear_combination hc
    have hc' := (mul_eq_zero.mp hmul).resolve_right m.normalSq_ne_zero
    exact Line.ext (hca.trans ha.symm) (hcb.trans hb.symm) (by
      change crease.c = (l.c+m.c)/2
      linarith)
  · rintro rfl
    apply (axiom3_iff_equations l m _).mpr
    constructor
    · dsimp [Line.alignmentEquation, Line.residual, Line.normalSq, Line.parallelMidline]
      rw [ha, hb, hp]
      ring
    · dsimp [Line.directionCross, Line.directionDifference, Line.parallelMidline]
      rw [ha, hb]
      ring

end FoldInput
end LeanOrigami
