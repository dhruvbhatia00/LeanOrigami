import LeanOrigami.Widget

/-!
# Goal matching and panel registration

Nontrivial irrational examples are exported by WidgetRuntime and replayed
independently. These small examples check the public tactic's basic behavior.
-/

namespace LeanOrigamiTests.Widget
open LeanOrigami LeanOrigami.Widget

example : Scalar.toReal (1 : Scalar) = (1 : ℝ) := by
  let target : Scalar := 1
  change Scalar.toReal target = _
  origami_identify target using norm_num

example : Scalar.toReal (1 : Scalar) = Real.sqrt 1 := by
  let target : Scalar := 1
  change Scalar.toReal target = _
  origami_identify target using norm_num

example : Scalar.toReal (1 : Scalar) = (1 : ℝ) ^ (1 / (3 : ℝ)) := by
  let target : Scalar := 1
  change Scalar.toReal target = _
  origami_identify target using norm_num

example : True := by
  let target : Scalar := 1
  fail_if_success
    have : Scalar.toReal target = (2 : ℝ) := by
      origami_identify target using norm_num
  trivial

/-- Local names for a supported target are interpreted in the goal's context. -/
example : True := by
  let wanted : ℝ := 1 / 2
  let target : Scalar := 1 / 2
  have _identified : Scalar.toReal target = wanted := by
    origami_identify target using norm_num
  trivial

example : True := by
  let target : Scalar := 1
  fail_if_success
    have : Scalar.toReal target = Real.pi := by
      origami_identify target using unreachable!
  trivial

/-- The submission gate checks the expression's actual type before insertion. -/
example : True := by
  run_tac do
    let goal ← Lean.Elab.Tactic.getMainTarget
    checkProof goal "True.intro"
    let accepted ← try
        checkProof goal "(0 : Nat)"
        pure true
      catch _ => pure false
    if accepted then throwError "The submission gate accepted a proof of the wrong type."
    Lean.Elab.Tactic.evalTactic (← `(tactic| trivial))

/-- Opening the panel does not discharge the goal; the ordinary proof is still needed. -/
theorem panel_registration : ConstructibleNumber (1 : ℝ) := by
  origami
  all_goals exact ConstructibleNumber.one

#print axioms rational_identity
#print axioms sqrt_identity
#print axioms cube_identity
#print axioms coordinate_nonneg
#print axioms panel_registration

end LeanOrigamiTests.Widget
