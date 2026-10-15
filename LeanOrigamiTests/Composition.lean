import LeanOrigami.Widget.Certificate

/-!
# Public outputs and theorem reuse

Two midpoint calls expose one point each, then an ordinary A1 fold consumes the
second output. Caller indices are 2 and 3, not indices into the private folds.
The certificate applies the midpoint rule twice without replaying either body.
-/

namespace LeanOrigami.Tests.Composition
open LeanOrigami Composition

private def library : Registry ℚ := fun identity =>
  if identity = "midpoint" then some (Midpoint.rule ℚ) else none

private def half : Point ℚ := (1/2, 0)
private def quarter : Point ℚ := (1/4, 0)
private def axis : Line ℚ := ⟨0, 1, 0, Or.inr ⟨rfl, rfl⟩⟩

/-- Two retained recipe calls and one ordinary fold. -/
def nested : Construction ℚ := [
  .call "midpoint" [0, 1] [.point half],
  .call "midpoint" [0, 2] [.point quarter],
  .primitive (.fold (.axiom1 ⟨0⟩ ⟨3⟩) axis)]

private def final : Program.State ℚ :=
  [.point (0, 0), .point (1, 0), .point half, .point quarter, .line axis]

/-- Each call uses the already proved rule; the last fold uses primitive checking. -/
theorem nested_certified : Certified library Program.initial nested final := by
  refine .cons (.call "midpoint" [0, 1] _ _ (Midpoint.rule ℚ) rfl rfl ?_) ?_
  · exact ⟨(0, 0), (1, 0), rfl, by decide +kernel, by norm_num [half, Midpoint.point]⟩
  refine .cons (.call "midpoint" [0, 2] _ _ (Midpoint.rule ℚ) rfl rfl ?_) ?_
  · exact ⟨(0, 0), half, rfl, by decide +kernel, by norm_num [half, quarter, Midpoint.point]⟩
  exact .cons (.primitive _ _ (by decide +kernel)) (.nil _)

/-- Independent kernel proof of the selected real coordinate. -/
theorem quarter_constructible : ConstructibleNumber (1/4 : ℝ) := by
  have h := nested_certified.coordinate_sound (Rat.castHom ℝ) 3 quarter .x (1/4) rfl rfl
  simpa using h

-- Reopening produces only five public objects, including the original seeds.
example : replay (Program.initial : Program.State ℚ) nested = .ok final :=
  nested_certified.replay_eq

-- No private crease is available at the next public index after the two calls.
example : select ([.point (0,0), .point (1,0), .point half, .point quarter] : Program.State ℚ)
    [4] = .error (.missingReference 4) := by decide +kernel

-- A recipe label cannot certify an arbitrary point or a coincident-input call.
example : ¬ Midpoint.Produces ([.point (0,0), .point (1,0)] : Program.State ℚ)
    [.point (3,0)] := by
  norm_num [Midpoint.Produces, Midpoint.point, Object.point.injEq, Prod.mk.injEq]
example : ¬ Midpoint.Produces ([.point (0,0), .point (0,0)] : Program.State ℚ)
    [.point (0,0)] := by
  simp [Midpoint.Produces]

-- Editing a recipe's identity removes access to the built-in theorem.
example : ∀ outputs final, ¬ Checked library (Program.initial : Program.State ℚ)
    (.call "edited-midpoint" [0,1] outputs) final := by
  intro outputs final checked
  cases checked with
  | call identity arguments inputs outputs rule registered references produces =>
    simp [library] at registered

-- An unregistered/edited body can instead use the ordinary primitive proof.
private def customBody : Program ℚ := [.fold (.axiom1 ⟨0⟩ ⟨1⟩) axis]
private def customRule : RecipeRule ℚ := RecipeRule.primitive customBody [2]

example : customRule.Produces Program.initial [.line axis] := by
  refine ⟨[.point (0,0), .point (1,0), .line axis], ?_, rfl⟩
  decide +kernel

-- The same public-output relation cannot be forged with a different crease.
example : ¬ customRule.Produces Program.initial [.line (⟨1, 0, 0, Or.inl rfl⟩ : Line ℚ)] := by
  intro h
  obtain ⟨state, executed, selected⟩ := h
  have actual : Program.execute Program.initial customBody =
      .ok [.point (0,0), .point (1,0), .line axis] := by decide +kernel
  rw [actual] at executed
  cases executed
  have impossible : select ([.point (0,0), .point (1,0), .line axis] : Program.State ℚ) [2] ≠
      .ok [.line (⟨1, 0, 0, Or.inl rfl⟩ : Line ℚ)] := by decide +kernel
  exact impossible selected

open Widget

/-- The actual saved call tree chooses its registry from its definitions. -/
def retained : Execution.History ℚ := [
  Execution.Step.call "First" midpointRecipe #[0,1] [.point half] [],
  Execution.Step.call "Second" midpointRecipe #[0,2] [.point quarter] [],
  Execution.Step.primitive (.fold (.axiom1 ⟨0⟩ ⟨3⟩) axis)]

/-- The saved-format registry uses the midpoint theorem twice, without bodies. -/
theorem retained_certified : Certified (Execution.registry retained) Program.initial
    (Execution.construction retained) final := by
  refine .cons (.call _ _ _ _ _ rfl rfl ?_) ?_
  · refine Or.inl ⟨rfl, ?_⟩
    exact ⟨(0,0), (1,0), rfl, by decide +kernel, by norm_num [half, Midpoint.point]⟩
  refine .cons (.call _ _ _ _ _ rfl rfl ?_) ?_
  · refine Or.inl ⟨rfl, ?_⟩
    exact ⟨(0,0), half, rfl, by decide +kernel, by norm_num [half, quarter, Midpoint.point]⟩
  exact .cons (.primitive _ _ (by decide +kernel)) (.nil _)

#print axioms retained_certified
#print axioms Execution.callRule

#print axioms Midpoint.constructible
#print axioms Composition.Certified.sound
#print axioms quarter_constructible

end LeanOrigami.Tests.Composition
