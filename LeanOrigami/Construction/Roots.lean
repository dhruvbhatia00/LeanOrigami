import LeanOrigami.Construction.Arithmetic
import LeanOrigami.Construction.RootGeometry
import Mathlib.Analysis.Real.Sqrt

/-!
# Closure under real roots of quadratics and cubics

Every coefficient must have construction evidence. A prescribed real root
selects a legal crease, and two vertical intersections recover its slope by
subtraction. Thus the root is an output, never an assumed input object.
Quadratics reuse the cubic construction after multiplication by the variable.
-/

namespace LeanOrigami.ConstructibleNumber

/-- A monic cubic's coefficient configuration is constructed using field operations. -/
theorem cubic_inputs {a b c : ℝ} (ha : ConstructibleNumber a)
    (hb : ConstructibleNumber b) (hc : ConstructibleNumber c) :
    (RootGeometry.input a b c).Available Constructible := by
  have hp := point zero one
  have hq := point (hc.sub ha) hb
  have hl := Constructible.horizontal (point zero one.neg)
  have hm := Constructible.vertical (point (ha.neg.sub hc) zero)
  simpa [FoldInput.Available, RootGeometry.input, FoldInput.objects] using
    And.intro hp (And.intro hq (And.intro hl hm))

/-- Intersections at abscissas zero and one recover the selected crease's slope.
The unknown root is not used to construct any input to the fold. -/
theorem of_root_crease {t : ℝ} (hf : Constructible (.line (RootGeometry.crease t))) :
    ConstructibleNumber t := by
  have hb := RootGeometry.nonvertical _ (RootGeometry.first_alignment t)
  have at_x (x : ℝ) (hx : ConstructibleNumber x) :
      Constructible (.point (x, t*x-t^2)) := by
    apply Constructible.of_intersection hf (Constructible.vertical hx.axis_point)
    · simpa [Line.determinant, Line.chart] using neg_ne_zero.mpr hb
    · rw [RootGeometry.contains_crease]; ring
    · simp [Line.Contains, Line.chart]
  have h := (of_y (at_x 1 one)).sub (of_y (at_x 0 zero))
  simpa using h

/-- Every real root of a monic cubic with constructed coefficients is constructed. -/
theorem monic_cubic_root {a b c t : ℝ} (ha : ConstructibleNumber a)
    (hb : ConstructibleNumber b) (hc : ConstructibleNumber c)
    (ht : t^3+a*t^2+b*t+c = 0) : ConstructibleNumber t := by
  apply of_root_crease
  exact Constructible.fold (RootGeometry.input a b c) (RootGeometry.crease t)
    (cubic_inputs ha hb hc)
    ⟨RootGeometry.admissible a b c, (RootGeometry.satisfies_iff a b c t).mpr ht⟩

/-- Normalize a genuine cubic; the theorem applies separately to every real root. -/
theorem cubic_root {a b c d t : ℝ} (ha : ConstructibleNumber a)
    (hb : ConstructibleNumber b) (hc : ConstructibleNumber c) (hd : ConstructibleNumber d)
    (hne : a ≠ 0) (ht : a*t^3+b*t^2+c*t+d = 0) : ConstructibleNumber t := by
  apply monic_cubic_root (hb.div ha hne) (hc.div ha hne) (hd.div ha hne)
  field_simp
  nlinarith

/-- Multiplication by the variable embeds a quadratic in a monic cubic.
Its extra zero root does not change the selected quadratic root. -/
theorem quadratic_root {a b c t : ℝ} (ha : ConstructibleNumber a)
    (hb : ConstructibleNumber b) (hc : ConstructibleNumber c)
    (hne : a ≠ 0) (ht : a*t^2+b*t+c = 0) : ConstructibleNumber t := by
  apply monic_cubic_root (hb.div ha hne) (hc.div ha hne) zero
  field_simp
  nlinarith [mul_eq_zero.mpr (Or.inr ht : t = 0 ∨ a*t^2+b*t+c = 0)]

/-- The degree-one case only needs division by its nonzero coefficient. -/
theorem linear_root {a b t : ℝ} (ha : ConstructibleNumber a)
    (hb : ConstructibleNumber b) (hne : a ≠ 0) (ht : a*t+b = 0) :
    ConstructibleNumber t := by
  have he : t = -b/a := by field_simp; nlinarith
  rw [he]
  exact hb.neg.div ha hne

/-- The nonnegative square root is a particular real quadratic root. -/
theorem sqrt {a : ℝ} (ha : ConstructibleNumber a) (hn : 0 ≤ a) :
    ConstructibleNumber (Real.sqrt a) := by
  apply quadratic_root one zero ha.neg one_ne_zero
  simp [Real.sq_sqrt hn]

end LeanOrigami.ConstructibleNumber
