import LeanOrigami.Text.Exact
import HexNumberFieldMathlib.Approx
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum

/-!
# Identify a submitted coordinate with a named real target

Arithmetic certificates prove equations in the selected number field. Root
identification additionally proves the branch condition for square roots.
Supported goal forms are rational expressions, square roots of nonnegative
rationals, and real powers `q ^ (1 / 3)` for nonnegative rational `q`, including
reducible names for these expressions. Unsupported targets remain open.
-/

namespace LeanOrigami.Widget

/-- Goal matching is separate from evidence that the coordinate was constructed. -/
theorem submit {x : ℝ} (value : Scalar)
    (constructed : ConstructibleNumber (Scalar.toReal value))
    (identified : Scalar.toReal value = x) : ConstructibleNumber x :=
  identified ▸ constructed

/-- A rational coordinate denotes the same rational in the real field. -/
theorem rational_identity (value : Scalar) (q : Rat) (h : value = (q : Scalar)) :
    Scalar.toReal value = (q : ℝ) := by
  subst value
  change Scalar.realHom (q : Scalar) = (q : ℝ)
  exact map_ratCast Scalar.realHom q

/-- The square equation and nonnegative branch identify Mathlib's square root. -/
theorem sqrt_identity (value : Scalar) (q : Rat)
    (h : value ^ 2 = (q : Scalar)) (nonneg : 0 ≤ value) :
    Scalar.toReal value = Real.sqrt (q : ℝ) := by
  have equation := congrArg Scalar.realHom h
  simp only [map_pow, map_ratCast] at equation
  have positive : 0 ≤ Scalar.toReal value := by
    simpa using (Scalar.toReal_le 0 value).mpr nonneg
  rw [← equation]
  exact (Real.sqrt_sq positive).symm

/-- Cubing is injective on the reals, so there is no ambiguous cube-root branch. -/
theorem cube_identity (value : Scalar) (q : Rat)
    (h : value ^ 3 = (q : Scalar)) (nonneg : (0 : ℝ) ≤ (q : ℝ)) :
    Scalar.toReal value = (q : ℝ) ^ (1 / (3 : ℝ)) := by
  apply (show Odd (3 : Nat) from by decide).pow_injective
  have equation : (Scalar.toReal value) ^ (3 : Nat) = (q : ℝ) := by
    change (Scalar.realHom value) ^ (3 : Nat) = (q : ℝ)
    rw [← map_pow, h, map_ratCast]
  have root : ((q : ℝ) ^ (1 / (3 : ℝ))) ^ (3 : Nat) = (q : ℝ) := by
    simpa using Real.rpow_inv_natCast_pow nonneg (by decide : (3 : Nat) ≠ 0)
  exact equation.trans root.symm

/-- A cheap rational enclosure certifies the sign without canonicalizing the
coordinate into a new algebraic-number representation. -/
theorem coordinate_nonneg (field : Scalar.Presentation) (value : field.Coordinates)
    (h : (Hex.PolyQuot.evalRatBall value.coeffs field.isolation.1.square 64).radius ≤
      (Hex.PolyQuot.evalRatBall value.coeffs field.isolation.1.square 64).re) :
    0 ≤ field.scalar value := by
  let ball := Hex.PolyQuot.evalRatBall value.coeffs field.isolation.1.square 64
  have mem : Hex.PolyQuot.toComplex value field.isolation rfl ∈ ball.set :=
    Hex.DyadicComplexBall.evalRatBall_mem _ _ _
      (Hex.DyadicComplexBall.mem_toBall
        (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc field.isolation))
  have bound : |(Hex.PolyQuot.toComplex value field.isolation rfl).re -
      HexRootsMathlib.Dyadic.toReal ball.re| ≤ ball.realRadius := by
    have norm : ‖Hex.PolyQuot.toComplex value field.isolation rfl - ball.center‖ ≤
        ball.realRadius := by
      simpa only [Hex.DyadicComplexBall.set, Metric.mem_closedBall, dist_eq_norm] using mem
    exact (Complex.abs_re_le_norm _).trans norm
  have radius := HexRootsMathlib.Dyadic.toReal_le_toReal_iff.mpr h
  apply (Scalar.toReal_le 0 _).mp
  rw [Scalar.toReal_zero]
  change 0 ≤ (field.scalar value).val.toComplex.re
  rw [Scalar.Presentation.scalar_toComplex]
  have lower := (abs_le.mp bound).1
  change HexRootsMathlib.Dyadic.toReal ball.radius ≤
    HexRootsMathlib.Dyadic.toReal ball.re at radius
  change -HexRootsMathlib.Dyadic.toReal ball.radius ≤ _ at lower
  linarith

open Lean Meta Elab Tactic Qq

/-- The supported named-target forms, used only to choose a proof strategy. -/
inductive Target where
  | rational (value : Rat)
  | squareRoot (value : Rat)
  | cubeRoot (value : Rat)

private def rationalValue (expression : Expr) : MetaM Rat := do
  let divisionRing ← synthInstance q(DivisionRing ℝ)
  let result ← Mathlib.Meta.NormNum.deriveRat (α := q(ℝ)) expression divisionRing
  return result.1

/-- Unfold reducible user names with a bounded search; never evaluate real arithmetic. -/
def classifyTarget (expression : Expr) (fuel : Nat := 16) : MetaM Target := do
  try return .rational (← rationalValue expression) catch _ => pure ()
  if expression.isAppOfArity ``Real.sqrt 1 then
    let q ← rationalValue expression.appArg!
    unless q ≥ 0 do throwError "Square-root goals currently require a nonnegative rational input."
    return .squareRoot q
  if expression.isAppOfArity ``Real.rpow 2 || expression.isAppOf ``HPow.hPow then
    let q ← rationalValue expression.getAppArgs[expression.getAppNumArgs - 2]!
    let exponent ← rationalValue expression.getAppArgs[expression.getAppNumArgs - 1]!
    unless q ≥ 0 && exponent == (1/3 : Rat) do
      throwError "Supported real-power goals have the form q ^ (1 / 3), with q nonnegative rational."
    return .cubeRoot q
  if fuel > 0 then
    if let some unfolded ← unfoldDefinition? expression then
      return ← classifyTarget unfolded (fuel - 1)
  throwError "Unsupported target. Use a rational expression, Real.sqrt q, or q ^ (1 / 3), with nonnegative rational q for roots."
termination_by fuel

/-- Close the exact identity obligation using the same arithmetic certificate as
construction checking. Native discovery supplies no proof of this identity. -/
elab "origami_identify " value:term " using " arithmetic:tacticSeq : tactic =>
  focus <| withMainContext do
    let goal ← getMainTarget
    let some (_, _, wanted) := goal.eq? | throwError "Expected a coordinate identity goal."
    let target ← classifyTarget wanted
    let q := match target with | .rational q | .squareRoot q | .cubeRoot q => q
    let numerator ← if q.num < 0 then `(-($(quote q.num.natAbs) : Rat))
      else `(($(quote q.num.natAbs) : Rat))
    let rational ← `($numerator / $(quote q.den))
    let rhs ← match target with
      | .rational _ => `((($rational : Rat) : ℝ))
      | .squareRoot _ => `(Real.sqrt (($rational : Rat) : ℝ))
      | .cubeRoot _ => `((($rational : Rat) : ℝ) ^ (1 / (3 : ℝ)))
    let theoremName := match target with
      | .rational _ => ``rational_identity
      | .squareRoot _ => ``sqrt_identity
      | .cubeRoot _ => ``cube_identity
    evalTactic (← `(tactic|
      suffices h : Scalar.toReal $value = $rhs from by convert h using 1 <;> norm_num))
    evalTactic (← `(tactic| apply $(mkIdent theoremName) $value $rational))
    evalTactic (← `(tactic| · dsimp only [$value:term]; ($arithmetic)))
    match target with
    | .rational _ => pure ()
    | .squareRoot _ =>
      evalTactic (← `(tactic|
        (dsimp only [$value:term]
         first
         | apply coordinate_nonneg; decide +kernel
         | norm_num)))
    | .cubeRoot _ => evalTactic (← `(tactic| norm_num))

end LeanOrigami.Widget
