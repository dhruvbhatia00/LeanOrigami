import LeanOrigami.Solvers.Cubic

/-!
# Encoding a prescribed cubic by a double alignment

The coefficient points and target lines depend only on the given coefficients.
The crease with slope `t` is legal exactly when `t` is a root of the monic
cubic. Normalization includes the horizontal crease at the zero root.
-/

namespace LeanOrigami.RootGeometry
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The two alignments encoding `t³ + a*t² + b*t + c = 0`. -/
def input (a b c : K) : FoldInput K :=
  .axiom6 (0, 1) (c-a, b) (Line.horizontal (-1)) (Line.chart 0 (-a-c))

/-- The tangent `y = t*x - t²`, with canonical line coefficients. -/
def crease (t : K) : Line K := Line.normalize (-t) 1 (-t^2) (Or.inr one_ne_zero)

/-- The first alignment holds for every parameter. -/
theorem first_alignment (t : K) :
    (crease t).alignmentEquation (Line.horizontal (-1)) (0, 1) = 0 := by
  by_cases ht : t = 0
  · subst t; norm_num [crease, Line.normalize, Line.alignmentEquation,
      Line.horizontal, Line.residual, Line.normalSq]
  · simp [crease, Line.normalize, ht, Line.alignmentEquation,
      Line.horizontal, Line.residual, Line.normalSq]
    field_simp
    ring

/-- The second alignment expresses precisely the prescribed cubic. -/
theorem satisfies_iff (a b c t : K) :
    (input a b c).Satisfies (crease t) ↔ t^3+a*t^2+b*t+c = 0 := by
  rw [input, FoldInput.axiom6_iff_equations, first_alignment]
  simp only [true_and]
  by_cases ht : t = 0
  · subst t
    simp [crease, Line.normalize, Line.alignmentEquation, Line.chart,
      Line.residual, Line.normalSq]
    constructor <;> intro h <;> nlinarith
  · simp [crease, Line.normalize, ht, Line.alignmentEquation, Line.chart,
      Line.residual, Line.normalSq]
    field_simp
    constructor <;> intro h <;> nlinarith

/-- Perpendicular targets and a nonzero eliminant give a finite choice for
all coefficients, even when the two source points coincide. -/
theorem admissible (a b c : ℝ) : (input a b c).Admissible := by
  apply (FoldInput.axiom6_admissible_iff _ _ _ _).mpr
  constructor
  · simp [FoldInput.axiom6FreeDirection, Line.determinant, Line.horizontal, Line.chart]
  · intro h
    have hc := h.1
    norm_num [FoldInput.axiom6Polynomial, Line.horizontal, Line.chart, Line.residual] at hc

/-- Incidence on the selected crease in unnormalized coordinates. -/
theorem contains_crease (t : K) (p : Point K) :
    (crease t).Contains p ↔ -t*p.1+p.2 = -t^2 := by
  simpa only [crease, one_mul] using
    (Line.contains_normalize (-t) 1 (-t^2) (Or.inr one_ne_zero) p)

/-- A crease satisfying the first alignment cannot be vertical. -/
theorem nonvertical (f : Line K)
    (h : f.alignmentEquation (Line.horizontal (-1)) (0, 1) = 0) : f.b ≠ 0 := by
  intro hb
  have ha := f.normal_ne_zero.resolve_right (not_not.mpr hb)
  simp [Line.alignmentEquation, Line.horizontal, Line.residual, Line.normalSq, hb] at h
  exact ha (by nlinarith [sq_nonneg f.a])

/-- Every valid crease has the advertised slope; there are no missing vertical
branches. The coefficient equation also identifies its intercept. -/
theorem slope_equation (f : Line K)
    (h : f.alignmentEquation (Line.horizontal (-1)) (0, 1) = 0) :
    f.c / f.b = -(-f.a / f.b)^2 := by
  have hb := nonvertical f h
  simp [Line.alignmentEquation, Line.horizontal, Line.residual, Line.normalSq] at h
  field_simp
  nlinarith

/-- The parameterization covers every crease satisfying the first alignment. -/
theorem eq_crease_of_first_alignment (f : Line K)
    (h : f.alignmentEquation (Line.horizontal (-1)) (0, 1) = 0) :
    f = crease (-f.a/f.b) := by
  have hb := nonvertical f h
  apply Line.ext_contains
  intro p
  rw [contains_crease, ← slope_equation f h]
  unfold Line.Contains
  field_simp

/-- All solutions, in both directions: every valid crease encodes a root and
every root encodes a valid crease. No exceptional direction is omitted. -/
theorem satisfies_iff_exists (a b c : K) (f : Line K) :
    (input a b c).Satisfies f ↔
      ∃ t, t^3+a*t^2+b*t+c = 0 ∧ f = crease t := by
  constructor
  · intro h
    have hfirst := ((FoldInput.axiom6_iff_equations _ _ _ _ _).mp h).1
    have he := eq_crease_of_first_alignment f hfirst
    exact ⟨-f.a/f.b, (satisfies_iff a b c _).mp (he ▸ h), he⟩
  · rintro ⟨t, ht, rfl⟩
    exact (satisfies_iff a b c t).mpr ht

end LeanOrigami.RootGeometry
