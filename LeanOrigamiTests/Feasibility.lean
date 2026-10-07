import HexNumberFieldMathlib

/-!
# Phase 0: exact arithmetic and semantic correspondence

These experiments establish the dependency interfaces before geometry is
implemented. The real subtype here is a feasibility probe, not a second
algebraic-number implementation or the final public geometry API.

Theorems reuse verified correspondence results. Runtime experiments are
separate: passing an executable check is not used as a proof premise.
-/

namespace LeanOrigamiTests.Feasibility

open Hex

/-- The released complex backend restricted by its exact reality test. -/
abbrev RealValue := { a : AlgebraicNumber // a.isReal = true }

/-- Interpretation of the real subtype in Mathlib's reals. -/
noncomputable def RealValue.toReal (a : RealValue) : ℝ := a.val.toComplex.re

/-- No information is lost when interpreting a real backend value. -/
theorem RealValue.toReal_injective : Function.Injective RealValue.toReal := by
  intro a b h
  apply Subtype.ext
  apply AlgebraicNumber.toComplex_injective
  apply Complex.ext h
  rw [(AlgebraicNumber.isReal_iff a.val).mp a.property,
    (AlgebraicNumber.isReal_iff b.val).mp b.property]

/-- The executable order becomes the ordinary real order on this subtype. -/
theorem RealValue.lt_iff (a b : RealValue) :
    a.val < b.val ↔ a.toReal < b.toReal := by
  rw [AlgebraicNumber.lt_iff]
  simp [RealValue.toReal, (AlgebraicNumber.isReal_iff a.val).mp a.property,
    (AlgebraicNumber.isReal_iff b.val).mp b.property]

/-- Executable addition stays within the real subtype. -/
theorem add_isReal (a b : RealValue) : (a.val + b.val).isReal = true := by
  rw [AlgebraicNumber.isReal_iff, AlgebraicNumber.add_toComplex]
  simp [(AlgebraicNumber.isReal_iff a.val).mp a.property,
    (AlgebraicNumber.isReal_iff b.val).mp b.property]

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

#print axioms RealValue.toReal_injective
#print axioms RealValue.lt_iff
#print axioms sqrtTwo_sq
#print axioms irrational_sequence
#print axioms sqrtTwo_semantics
#print axioms algebraic_root_membership
#print axioms approximation_contains

end LeanOrigamiTests.Feasibility
