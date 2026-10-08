import HexNumberFieldMathlib
import LeanOrigami.Geometry.Exact

/-!
# Phase 0: exact arithmetic and semantic correspondence

The Phase 0 experiments now use the public Phase 1 scalar and geometry
interfaces. No separate real subtype is maintained in the tests.

Theorems reuse verified correspondence results. Runtime experiments are
separate: passing an executable check is not used as a proof premise.
-/

namespace LeanOrigamiTests.Feasibility

open Hex

open LeanOrigami ComplexOrder

/-- A concrete irrational, with the positive principal square-root branch. -/
def sqrtTwo : AlgebraicNumber := (2 : AlgebraicNumber).sqrt

/-- Another irrational to exercise operations across two number fields. -/
def sqrtThree : AlgebraicNumber := (3 : AlgebraicNumber).sqrt

/-- Certification uses the general root theorem, without reducing root search. -/
theorem sqrtTwo_sq : sqrtTwo ^ 2 = 2 := AlgebraicNumber.sqrt_sq 2

/-- A short irrational computation has a compact algebraic proof. -/
theorem irrational_sequence :
    (sqrtTwo + sqrtThree) * (sqrtTwo - sqrtThree) = -1 := by
  have h₂ := sqrtTwo_sq
  have h₃ : sqrtThree ^ 2 = 3 := AlgebraicNumber.sqrt_sq 3
  calc
    (sqrtTwo + sqrtThree) * (sqrtTwo - sqrtThree) =
        sqrtTwo ^ 2 - sqrtThree ^ 2 := by ring
    _ = -1 := by rw [h₂, h₃]; norm_num

/-- The computed square root has the expected Mathlib interpretation. -/
theorem sqrtTwo_semantics : sqrtTwo.toComplex = Complex.sqrt 2 := by
  simp [sqrtTwo]

/-- Completeness is available for polynomials with algebraic coefficients. -/
theorem algebraic_root_membership (p : AlgebraicPoly) (z : ℂ) :
    RootSet.Contains p.roots z ↔ p.toPolynomial.eval z = 0 :=
  AlgebraicPoly.contains_roots_iff p z

/-- The zero polynomial is distinguished from an empty finite root set. -/
theorem zero_polynomial_roots (p : AlgebraicPoly) :
    p.roots = .all ↔ p.toPolynomial = 0 := AlgebraicPoly.roots_all_iff p

/-- Approximation carries a mathematical containment guarantee. -/
theorem approximation_contains (a : AlgebraicNumber) (precision : Int) :
    a.toComplex ∈ (a.approx precision).set :=
  AlgebraicNumber.approx_mem a precision

/-- An irrational value in the public real scalar type. -/
def realSqrtTwo : Scalar := ⟨sqrtTwo, by
  change sqrtTwo.isReal = true
  rw [AlgebraicNumber.isReal_iff, sqrtTwo_semantics]
  rw [Complex.sqrt_of_nonneg (by norm_num : (0 : ℂ) ≤ 2)]
  simp⟩

/-- The subtype retains the exact square-root identity. -/
theorem realSqrtTwo_sq : realSqrtTwo ^ 2 = 2 := by
  apply Subtype.ext
  exact sqrtTwo_sq

/-- The positive real branch has its expected interpretation. -/
theorem realSqrtTwo_toReal : Scalar.toReal realSqrtTwo = Real.sqrt 2 := by
  change sqrtTwo.toComplex.re = _
  rw [sqrtTwo_semantics]
  simpa using (Complex.re_sqrt_ofReal (a := 2))

example : (0 : Scalar) < realSqrtTwo := by
  rw [← Scalar.toReal_lt, Scalar.toReal_zero, realSqrtTwo_toReal]
  positivity

-- Arithmetic proofs work on variables, without executing Hex's root search.
example (a b : Scalar) : Scalar.realHom (a / b) = Scalar.realHom a / Scalar.realHom b := by
  exact map_div₀ Scalar.realHom a b

example (a : Scalar) (h : a ≠ 0) : a * a⁻¹ = 1 := by
  exact mul_inv_cancel₀ (G₀ := Scalar) (a := a) h
example : (2 / 3 : Scalar) + 1 / 3 = 1 := by norm_num
example (q : ℚ) : Scalar.realHom (q : Scalar) = (q : ℝ) := map_ratCast Scalar.realHom q

-- An irrational coefficient is permitted, with no slope restriction.
example : (Line.normalize (1 : Scalar) realSqrtTwo 0 (by norm_num)).Contains
    (realSqrtTwo, -1) := by simp

-- Reflection at an irrational horizontal coordinate remains exact.
example : (Line.normalize (1 : Scalar) 0 realSqrtTwo (by norm_num)).reflect (0, 0) =
    (2 * realSqrtTwo, 0) := by
  simp [Line.normalize, Line.reflect, Line.residual, Line.normalSq]

example (l : Line Scalar) (p : Point Scalar) : (l.reflect p).toReal.toPlane =
    EuclideanGeometry.reflection l.toReal.affine p.toReal.toPlane :=
  l.exact_reflect_eq_mathlib p

#print axioms realSqrtTwo_sq
#print axioms realSqrtTwo_toReal
#print axioms Line.exact_reflect_eq_mathlib
#print axioms exact_intersection_legal
#print axioms Scalar.toReal_injective
#print axioms Scalar.toReal_lt
#print axioms sqrtTwo_sq
#print axioms irrational_sequence
#print axioms sqrtTwo_semantics
#print axioms algebraic_root_membership
#print axioms approximation_contains

end LeanOrigamiTests.Feasibility
