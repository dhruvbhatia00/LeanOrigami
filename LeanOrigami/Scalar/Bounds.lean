import LeanOrigami.Scalar.Presentation
import HexNumberFieldMathlib.Approx

/-!
# Checked signs of number-field coordinates

Rational ball evaluation bounds a coordinate without constructing another
canonical algebraic number. These theorems certify branch inequalities; native
root selection and rendering remain untrusted. Precision is explicit so callers
can refine a certificate when a coarse enclosure overlaps zero.
-/

namespace LeanOrigami.Scalar.Presentation

/-- The lower endpoint of a rational enclosure bounds the interpreted scalar. -/
theorem coordinate_lower (field : Presentation) (value : field.Coordinates) (precision : Nat) :
    let ball := Hex.PolyQuot.evalRatBall value.coeffs field.isolation.1.square precision
    HexRootsMathlib.Dyadic.toReal ball.re - HexRootsMathlib.Dyadic.toReal ball.radius ≤
      Scalar.toReal (field.scalar value) := by
  let ball := Hex.PolyQuot.evalRatBall value.coeffs field.isolation.1.square precision
  have mem : Hex.PolyQuot.toComplex value field.isolation rfl ∈ ball.set :=
    Hex.DyadicComplexBall.evalRatBall_mem _ _ _
      (Hex.DyadicComplexBall.mem_toBall
        (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc field.isolation))
  have norm : ‖Hex.PolyQuot.toComplex value field.isolation rfl - ball.center‖ ≤
      ball.realRadius := by
    simpa only [Hex.DyadicComplexBall.set, Metric.mem_closedBall, dist_eq_norm] using mem
  have bound := (Complex.abs_re_le_norm _).trans norm
  have lower := (abs_le.mp bound).1
  change HexRootsMathlib.Dyadic.toReal ball.re - HexRootsMathlib.Dyadic.toReal ball.radius ≤
    (field.scalar value).val.toComplex.re
  rw [scalar_toComplex]
  change -HexRootsMathlib.Dyadic.toReal ball.radius ≤
    (Hex.PolyQuot.toComplex value field.isolation rfl).re -
      HexRootsMathlib.Dyadic.toReal ball.re at lower
  linarith

/-- A nonnegative rational lower endpoint certifies nonnegativity. -/
theorem coordinate_nonneg (field : Presentation) (value : field.Coordinates) (precision : Nat)
    (h : (Hex.PolyQuot.evalRatBall value.coeffs field.isolation.1.square precision).radius ≤
      (Hex.PolyQuot.evalRatBall value.coeffs field.isolation.1.square precision).re) :
    0 ≤ field.scalar value := by
  have bound := field.coordinate_lower value precision
  have positive := HexRootsMathlib.Dyadic.toReal_le_toReal_iff.mpr h
  apply (Scalar.toReal_le 0 _).mp
  rw [Scalar.toReal_zero]
  linarith

/-- A strictly positive rational lower endpoint certifies a strict root branch. -/
theorem coordinate_pos (field : Presentation) (value : field.Coordinates) (precision : Nat)
    (h : (Hex.PolyQuot.evalRatBall value.coeffs field.isolation.1.square precision).radius <
      (Hex.PolyQuot.evalRatBall value.coeffs field.isolation.1.square precision).re) :
    0 < field.scalar value := by
  have bound := field.coordinate_lower value precision
  have positive := HexRootsMathlib.Dyadic.toReal_lt_toReal_iff.mpr h
  apply (Scalar.toReal_lt 0 _).mp
  rw [Scalar.toReal_zero]
  linarith

end LeanOrigami.Scalar.Presentation
