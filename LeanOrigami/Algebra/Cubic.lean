import LeanOrigami.Algebra.LowDegree
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Tactic.Ring

/-!
# Executable coefficients for equations of degree at most three

Degree drops and the zero polynomial are explicit. The coefficient list is
the input format of the exact root adapter; the record gives named access
to the leading coefficient needed for geometric exceptional cases.
-/

namespace LeanOrigami.Univariate

/-- Coefficients in increasing degree order; the leading terms may vanish. -/
structure Cubic (K : Type*) where
  constant : K
  linear : K
  quadratic : K
  cubic : K

namespace Cubic
variable {K : Type*} [Field K]

/-- Horner evaluation uses only field arithmetic. -/
def eval (p : Cubic K) (t : K) : K :=
  p.constant + t*(p.linear+t*(p.quadratic+t*p.cubic))

/-- The dense coefficient list expected by the real-root adapter. -/
def coefficients (p : Cubic K) : List K := [p.constant, p.linear, p.quadratic, p.cubic]

/-- Identically zero, as distinct from a nonzero polynomial without roots. -/
def IsZero (p : Cubic K) : Prop :=
  p.constant = 0 ∧ p.linear = 0 ∧ p.quadratic = 0 ∧ p.cubic = 0

instance [DecidableEq K] (p : Cubic K) : Decidable p.IsZero :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The list and record have the same evaluation. -/
theorem coefficients_eval (p : Cubic K) (t : K) :
    p.coefficients.foldr (fun a value => a+t*value) 0 = p.eval t := by
  simp [coefficients, eval]

/-- Expanded form used by root bounds. -/
theorem eval_eq (p : Cubic K) (t : K) :
    p.eval t = p.cubic*t^3+p.quadratic*t^2+p.linear*t+p.constant := by
  dsimp [eval]
  ring

/-- A zero coefficient record vanishes at every input. -/
theorem eval_of_isZero (p : Cubic K) (h : p.IsZero) (t : K) : p.eval t = 0 := by
  simp [eval, h.1, h.2.1, h.2.2.1, h.2.2.2]

/-- A nonzero equation has at least one nonzero coefficient, in descending order. -/
theorem nonzero_coefficients (p : Cubic K) (h : ¬p.IsZero) :
    p.cubic ≠ 0 ∨ p.quadratic ≠ 0 ∨ p.linear ≠ 0 ∨ p.constant ≠ 0 := by
  by_contra hn
  push Not at hn
  exact h ⟨hn.2.2.2, hn.2.2.1, hn.2.1, hn.1⟩

/-- Interpret coefficients through a field embedding. -/
def map {L : Type*} [Field L] (f : K →+* L) (p : Cubic K) : Cubic L :=
  ⟨f p.constant, f p.linear, f p.quadratic, f p.cubic⟩

/-- Zero-polynomial classification is preserved and reflected by embeddings. -/
theorem isZero_map_iff {L : Type*} [Field L] (f : K →+* L) (p : Cubic K) :
    (p.map f).IsZero ↔ p.IsZero := by
  simp only [IsZero, map, ← map_zero f, f.injective.eq_iff]

/-- Horner evaluation commutes with embeddings. -/
theorem eval_map {L : Type*} [Field L] (f : K →+* L) (p : Cubic K) (t : K) :
    (p.map f).eval (f t) = f (p.eval t) := by simp [eval, map]

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- Every nonzero coefficient record has at most three distinct roots. -/
theorem zeros_subset_triple (p : Cubic K) (h : ¬p.IsZero) :
    ∃ r s u : K, ∀ t, p.eval t = 0 → t = r ∨ t = s ∨ t = u := by
  simpa only [eval_eq] using cubic_zeros_subset_triple p.cubic p.quadratic p.linear
    p.constant (p.nonzero_coefficients h)

/-- When the cubic term drops out, the bound drops to two, even after further degree loss. -/
theorem zeros_subset_pair (p : Cubic K) (h : ¬p.IsZero) (hc : p.cubic = 0) :
    ∃ r s : K, ∀ t, p.eval t = 0 → t = r ∨ t = s := by
  simpa only [eval_eq, hc, zero_mul, zero_add] using
    quadratic_zeros_subset_pair p.quadratic p.linear p.constant
      ((p.nonzero_coefficients h).resolve_left (not_not.mpr hc))

end Cubic
end LeanOrigami.Univariate
