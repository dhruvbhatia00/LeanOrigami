import LeanOrigami.Solvers.Basic

/-!
# Polynomial equations for fold relations

These equations are equivalent to the original reflection conditions. Clearing
the squared normal is safe for every valid crease, including horizontal and
vertical ones. They do not, by themselves, establish finite admissibility.
-/

namespace LeanOrigami
namespace Line
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The point-to-line reflection condition with its denominator cleared. -/
def alignmentEquation (crease target : Line K) (source : Point K) : K :=
  target.residual source * crease.normalSq -
    2 * crease.residual source * (target.a * crease.a + target.b * crease.b)

/-- The equation is the reflected point's residual times a nonzero factor. -/
theorem alignmentEquation_eq (crease target : Line K) (source : Point K) :
    crease.alignmentEquation target source =
      target.residual (crease.reflect source) * crease.normalSq := by
  have hn := crease.normalSq_ne_zero
  dsimp [alignmentEquation, reflect, residual]
  field_simp
  ring

/-- No roots are lost or introduced when the reflection denominator is cleared. -/
theorem alignmentEquation_zero_iff (crease target : Line K) (source : Point K) :
    crease.alignmentEquation target source = 0 ↔ target.Contains (crease.reflect source) := by
  rw [alignmentEquation_eq, mul_eq_zero]
  simp only [crease.normalSq_ne_zero, or_false, residual_eq_zero]

/-- All nonhorizontal creases have this chart, including vertical creases at `t = 0`. -/
def chart (t c : K) : Line K := ⟨1, t, c, Or.inl rfl⟩

/-- Horizontal creases are the missing direction of the other chart. -/
def horizontal (c : K) : Line K := ⟨0, 1, c, Or.inr ⟨rfl, rfl⟩⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Every canonical crease occurs in one of the two charts. -/
theorem chart_cases (crease : Line K) :
    crease = chart crease.b crease.c ∨ crease = horizontal crease.c := by
  rcases crease.normalized with ha | ⟨ha, hb⟩
  · exact Or.inl (Line.ext ha rfl rfl)
  · exact Or.inr (Line.ext ha hb rfl)

/-- The normal dot product appearing in the nonhorizontal chart. -/
def chartDot (target : Line K) (t : K) : K := target.a + target.b * t

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The chart equation is quadratic in direction and linear in offset. -/
theorem alignmentEquation_chart (target : Line K) (source : Point K) (t c : K) :
    (chart t c).alignmentEquation target source =
      target.residual source * (1 + t^2) -
        2 * (source.1 + t * source.2 - c) * target.chartDot t := by
  simp [alignmentEquation, chart, residual, normalSq, chartDot]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The horizontal chart has a separate linear equation, with no slope division. -/
theorem alignmentEquation_horizontal (target : Line K) (source : Point K) (c : K) :
    (horizontal c).alignmentEquation target source =
      target.residual source - 2 * (source.2 - c) * target.b := by
  simp [alignmentEquation, horizontal, residual, normalSq]

/-- If the direction is not parallel to the target, alignment fixes the offset. -/
theorem alignment_chart_iff_offset (target : Line K) (source : Point K) (t c : K)
    (hd : target.chartDot t ≠ 0) :
    (chart t c).alignmentEquation target source = 0 ↔
      c = source.1 + t * source.2 -
        target.residual source * (1 + t^2) / (2 * target.chartDot t) := by
  rw [alignmentEquation_chart]
  constructor <;> intro h
  · field_simp
    nlinarith [h]
  · field_simp at h
    nlinarith [h]

end Line

namespace FoldInput
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Rule 5 is a polynomial alignment equation together with incidence. -/
theorem axiom5_iff_equations (p q : Point K) (target crease : Line K) :
    (axiom5 p q target).Satisfies crease ↔
      crease.alignmentEquation target p = 0 ∧ crease.Contains q := by
  rw [Line.alignmentEquation_zero_iff]
  rfl

/-- Rule 6 is exactly the pair of point-to-line polynomial equations. -/
theorem axiom6_iff_equations (p q : Point K) (l m crease : Line K) :
    (axiom6 p q l m).Satisfies crease ↔
      crease.alignmentEquation l p = 0 ∧ crease.alignmentEquation m q = 0 := by
  rw [Line.alignmentEquation_zero_iff, Line.alignmentEquation_zero_iff]
  rfl

/-- Rule 7 adds the perpendicularity equation to point-to-line alignment. -/
theorem axiom7_iff_equations (p : Point K) (l m crease : Line K) :
    (axiom7 p l m).Satisfies crease ↔
      crease.alignmentEquation l p = 0 ∧ crease.a * m.a + crease.b * m.b = 0 := by
  rw [Line.alignmentEquation_zero_iff]
  rfl

/-- Eliminate the crease offset from rule 6 in the nonhorizontal chart.
This expression has degree at most three in `t`. A zero value is not enough
without checking a nonzero dot product or treating the exceptional direction. -/
def axiom6Eliminant (p q : Point K) (l m : Line K) (t : K) : K :=
  2 * ((p.1 - q.1) + t * (p.2 - q.2)) * l.chartDot t * m.chartDot t -
    (1 + t^2) * (l.residual p * m.chartDot t - m.residual q * l.chartDot t)

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The eliminant is a linear combination of the original equations. -/
theorem axiom6Eliminant_eq (p q : Point K) (l m : Line K) (t c : K) :
    axiom6Eliminant p q l m t =
      l.chartDot t * (Line.chart t c).alignmentEquation m q -
        m.chartDot t * (Line.chart t c).alignmentEquation l p := by
  rw [Line.alignmentEquation_chart, Line.alignmentEquation_chart]
  unfold axiom6Eliminant
  ring

/-- Every nonhorizontal rule-6 crease gives a root of the eliminant. -/
theorem axiom6_eliminant_zero (p q : Point K) (l m : Line K) (t c : K)
    (h : (axiom6 p q l m).Satisfies (Line.chart t c)) :
    axiom6Eliminant p q l m t = 0 := by
  obtain ⟨hl, hm⟩ := (axiom6_iff_equations p q l m _).mp h
  rw [axiom6Eliminant_eq p q l m t c, hl, hm]
  ring

/-- The first alignment and eliminant recover both alignments when division is valid. -/
theorem axiom6_iff_eliminant (p q : Point K) (l m : Line K) (t c : K)
    (hd : l.chartDot t ≠ 0) :
    (axiom6 p q l m).Satisfies (Line.chart t c) ↔
      c = p.1 + t * p.2 - l.residual p * (1 + t^2) / (2 * l.chartDot t) ∧
        axiom6Eliminant p q l m t = 0 := by
  constructor
  · intro h
    exact ⟨(Line.alignment_chart_iff_offset l p t c hd).mp
      ((axiom6_iff_equations p q l m _).mp h).1,
      axiom6_eliminant_zero p q l m t c h⟩
  · rintro ⟨hc, he⟩
    have hl := (Line.alignment_chart_iff_offset l p t c hd).mpr hc
    apply (axiom6_iff_equations p q l m _).mpr
    refine ⟨hl, ?_⟩
    rw [axiom6Eliminant_eq p q l m t c, hl, mul_zero, sub_zero] at he
    exact (mul_eq_zero.mp he).resolve_left hd

/-- A horizontal solution forces the cubic leading coefficient to vanish.
This accounts for that extra direction in the eventual bound of three creases. -/
theorem axiom6_horizontal_leading_zero (p q : Point K) (l m : Line K) (c : K)
    (h : (axiom6 p q l m).Satisfies (Line.horizontal c)) :
    2 * (p.2 - q.2) * l.b * m.b -
      (l.residual p * m.b - m.residual q * l.b) = 0 := by
  obtain ⟨hl, hm⟩ := (axiom6_iff_equations p q l m _).mp h
  rw [Line.alignmentEquation_horizontal] at hl hm
  linear_combination l.b * hm - m.b * hl

end FoldInput
end LeanOrigami
