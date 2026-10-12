import LeanOrigami.Scalar
import HexNumberFieldMathlib.Exact
import HexNumberFieldMathlib.Orientation

/-!
# Scalar certificates in one real number field

An isolation and a checked irreducible polynomial specify one real embedding.
Coordinates are rational polynomials modulo that polynomial. Exactification is
used for execution; its correctness theorem lets proofs check only reduced
coordinates, without repeating isolation or canonicalization.
-/

namespace LeanOrigami.Scalar
open Hex
open scoped Hex.PolyQuot.QAdjoinField

/-- Self-contained certificate for a real number field. No discovery history is
required: the kernel checks irreducibility, isolation, and the real-axis test. -/
structure Presentation where
  polynomial : ZPoly
  checked : ZPoly.CheckedIrreducible polynomial
  isolation : RefinedIsolation polynomial
  real : isolation.1.square.meetsRealAxis = true

namespace Presentation

instance (s : Presentation) : ZPoly.CheckedIrreducible s.polynomial := s.checked

/-- Reduced rational coordinates at the saved root. -/
abbrev Coordinates (s : Presentation) :=
  PolyQuot s.polynomial (SimpleRoot.mk s.isolation)

private theorem coordinates_real (s : Presentation) (a : s.Coordinates) :
    (PolyQuot.toComplex a s.isolation rfl).im = 0 := by
  have hr := (HexRootsMathlib.RefinedIsolation.meetsRealAxis_iff s.isolation).mp s.real
  have hv : s.isolation.root = (s.isolation.root.re : ℂ) := Complex.ext rfl (by simpa using hr)
  change ((HexPolyMathlib.toPolynomial a.coeffs).eval₂ (algebraMap Rat ℂ) s.isolation.root).im = 0
  induction HexPolyMathlib.toPolynomial a.coeffs using Polynomial.induction_on' with
  | add p q hp hq => simp [Polynomial.eval₂_add, hp, hq]
  | monomial n q =>
    rw [Polynomial.eval₂_monomial, hv, ← Complex.ofReal_pow]
    change ((q : ℂ) * ((s.isolation.root.re ^ n : ℝ) : ℂ)).im = 0
    simp only [Complex.mul_im, Complex.ofReal_im, Complex.ratCast_im, mul_zero, zero_mul, add_zero]

/-- Executable interpretation of saved coordinates as the existing scalar type. -/
def scalar (s : Presentation) (a : s.Coordinates) : Scalar :=
  ⟨a.toAlgebraicNumber s.isolation rfl, by
    change (a.toAlgebraicNumber s.isolation rfl).isReal = true
    rw [AlgebraicNumber.isReal_iff, PolyQuot.toAlgebraicNumber_toComplex]
    exact coordinates_real s a⟩

/-- Exactification agrees with the saved polynomial coordinates. -/
theorem scalar_toComplex (s : Presentation) (a : s.Coordinates) :
    (s.scalar a).val.toComplex = PolyQuot.toComplex a s.isolation rfl :=
  PolyQuot.toAlgebraicNumber_toComplex a s.isolation rfl

/-- The certificate interpretation preserves field arithmetic. Its underlying
function is executable; the ring laws are used only in proofs. -/
noncomputable def hom (s : Presentation) : s.Coordinates →+* Scalar where
  toFun := s.scalar
  map_zero' := by
    apply Subtype.ext
    apply AlgebraicNumber.toComplex_injective
    change (s.scalar 0).val.toComplex = (0 : AlgebraicNumber).toComplex
    rw [scalar_toComplex, AlgebraicNumber.zero_toComplex, PolyQuot.map_zero]
  map_one' := by
    apply Subtype.ext
    apply AlgebraicNumber.toComplex_injective
    change (s.scalar 1).val.toComplex = (1 : AlgebraicNumber).toComplex
    rw [scalar_toComplex, AlgebraicNumber.one_toComplex, PolyQuot.map_one]
  map_add' a b := by
    apply Subtype.ext
    apply AlgebraicNumber.toComplex_injective
    change (s.scalar (a + b)).val.toComplex = ((s.scalar a).val + (s.scalar b).val).toComplex
    rw [AlgebraicNumber.add_toComplex, scalar_toComplex, scalar_toComplex,
      scalar_toComplex, PolyQuot.map_add]
  map_mul' a b := by
    apply Subtype.ext
    apply AlgebraicNumber.toComplex_injective
    change (s.scalar (a * b)).val.toComplex = ((s.scalar a).val * (s.scalar b).val).toComplex
    rw [AlgebraicNumber.mul_toComplex, scalar_toComplex, scalar_toComplex,
      scalar_toComplex, PolyQuot.map_mul]

/-- Expose the field embedding without evaluating exactification. -/
theorem scalar_eq_hom (s : Presentation) (a : s.Coordinates) : s.scalar a = s.hom a := rfl

end Presentation
end LeanOrigami.Scalar
