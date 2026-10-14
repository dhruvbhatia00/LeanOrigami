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

/-- RPC proof checking restores auxiliary names under a named theorem's
asynchronous environment and starts a fresh construction budget. A captured
context may have exhausted its original budget before the user submits. -/
theorem captured_context : True := by
  run_tac do
    let context : Lean.Elab.ContextInfo := { ← Lean.Elab.CommandContextInfo.save with }
    let locals ← Lean.getLCtx
    let goal ← Lean.Elab.Tactic.getMainTarget
    context.runMetaM locals <| checkProof goal "by decide +kernel"
    context.runMetaM locals <|
      withTheReader Lean.Core.Context
        (fun context => { context with initHeartbeats := 0, maxHeartbeats := 1 })
        (checkProof goal "by decide +kernel")
    Lean.Elab.Tactic.evalTactic (← `(tactic| trivial))

/-- Opening the panel does not discharge the goal; the ordinary proof is still needed. -/
theorem panel_registration : ConstructibleNumber (1 : ℝ) := by
  origami
  all_goals exact ConstructibleNumber.one

/-- The real division is intentionally noncomputable: reopening must extract
only the program and selection, never evaluate the real target. -/
def savedSeed : SavedConstruction (0 / (1 : ℝ)) where
  program := []
  point := ⟨1⟩
  coordinate := .y
  target := 0
  accepted := by
    simp [Program.accepts, Program.submit, Program.run, Program.execute, Program.initial,
      Program.point, Coordinate.get, Bind.bind, Except.bind, Pure.pure, Except.pure]
  identified := by simp [Scalar.toReal_zero]

/-- A saved tactic closes its goal, while retaining its source-attached panel. -/
theorem saved_seed : ConstructibleNumber (0 / (1 : ℝ)) := by
  origami saved savedSeed

/-- A certificate for a different target cannot discharge the current goal. -/
example : ConstructibleNumber (1 : ℝ) := by
  fail_if_success origami saved savedSeed
  exact ConstructibleNumber.one

/-- Reopening restores data only. Re-saving still uses the ordinary proof gate.
Also exercise reopening in a captured named-theorem context. -/
theorem saved_reopens : True := by
  run_tac do
    let context : Lean.Elab.ContextInfo := { ← Lean.Elab.CommandContextInfo.save with }
    let restored ← context.runMetaM (← Lean.getLCtx) (reopen (Lean.mkConst ``savedSeed))
    let .ok (session, point, coordinate) := restored
      | throwError "Could not reopen the saved seed."
    unless session.program.isEmpty && session.objects.length == 2 && point == 1 do
      throwError "Saved construction data changed on reopening."
    match coordinate with
    | .y => pure ()
    | .x => throwError "The saved coordinate selection was lost."
    Lean.Elab.Tactic.evalTactic (← `(tactic| trivial))

#print axioms rational_identity
#print axioms sqrt_identity
#print axioms cube_identity
#print axioms coordinate_nonneg
#print axioms captured_context
#print axioms panel_registration
#print axioms SavedConstruction.sound
#print axioms saved_seed
#print axioms saved_reopens

end LeanOrigamiTests.Widget
