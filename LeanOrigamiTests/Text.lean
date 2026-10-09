import LeanOrigami.Text

/-!
# Named programs and rejected certificates

All seven primitives share one program representation. Exact rational cases
also compare symbolic certification with kernel evaluation of the checker.
-/

namespace LeanOrigamiTests.Text
open LeanOrigami

-- Assert rejection and its location without leaving a failed declaration behind.
elab (name := rejectWith) "reject_with " expected:str " in " body:tacticSeq : tactic => do
  let state ← Lean.Elab.Tactic.saveState
  let oldMessages := (← Lean.Core.getMessageLog).toArray.size
  let failure ← try
    Lean.Elab.Term.withoutErrToSorry <| Lean.Elab.Tactic.withoutRecover do
      Lean.Elab.Tactic.evalTactic body
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let messages := (← Lean.Core.getMessageLog).toArray
      if let some error := (messages.extract oldMessages messages.size).find?
          (·.severity == .error) then throwError error.data
    pure none
  catch error => pure (some (← error.toMessageData.toString))
  state.restore
  unless failure.any (·.startsWith expected.getString) do
    throwError "expected rejection starting with {expected.getString}; got {repr failure}"

-- Like `fail_if_success`, this test assertion deliberately preserves the goal.
#allow_unused_tactic LeanOrigamiTests.Text.rejectWith
run_elab do Mathlib.Linter.UnusedTactic.addIgnoreTacticKind ``rejectWith

-- Certifying one goal must not consume an unrelated sibling goal.
example : Program.accepts ([] : Program ℚ) ⟨1⟩ .x 1 = true ∧ True := by
  constructor
  origami_check
  trivial

/-- Ordinary local names stand for references, not proof-bearing objects. -/
def allRules : Recipe ℚ 2 := RecipeBuilder.build 2 do
  let origin : PointRef := ⟨0⟩
  let unit : PointRef := ⟨1⟩
  let axis ← RecipeBuilder.fold (.axiom1 origin unit) (Line.horizontal 0)
  let vertical ← RecipeBuilder.fold (.axiom4 origin axis) (Line.chart 0 0)
  let unitVertical ← RecipeBuilder.fold (.axiom4 unit axis) (Line.chart 0 1)
  let upper ← RecipeBuilder.fold (.axiom5 unit origin vertical) (Line.chart (-1) 0)
  let upperRight ← RecipeBuilder.intersect unitVertical upper (1, 1)
  let upperLevel ← RecipeBuilder.fold (.axiom4 upperRight vertical) (Line.horizontal 1)
  let upperUnit ← RecipeBuilder.intersect vertical upperLevel (0, 1)
  let lower ← RecipeBuilder.fold (.axiom5 unit origin vertical) (Line.chart 1 0)
  let lowerRight ← RecipeBuilder.intersect unitVertical lower (1, -1)
  let lowerLevel ← RecipeBuilder.fold (.axiom4 lowerRight vertical) (Line.horizontal (-1))
  let lowerUnit ← RecipeBuilder.intersect vertical lowerLevel (0, -1)
  let _ ← RecipeBuilder.fold (.axiom6 upperUnit lowerUnit lowerLevel vertical) (Line.chart 1 (-1))
  let _ ← RecipeBuilder.fold (.axiom3 axis vertical) (Line.chart 1 0)
  let alignment ← RecipeBuilder.fold (.axiom7 unit vertical axis) (Line.chart 0 (1/2))
  let _ ← RecipeBuilder.intersect alignment axis (1/2, 0)
  let midpoint ← RecipeBuilder.fold (.axiom2 origin unit) (Line.chart 0 (1/2))
  RecipeBuilder.intersect midpoint axis (1/2, 0)

/-- The symbolic certificate concerns the ordinary executable acceptance flag. -/
theorem all_rules_accept : Program.accepts allRules.steps allRules.output .x (1/2) = true := by
  origami_check

/-- Evaluation of that same saved record agrees in this small rational example. -/
example : Program.accepts allRules.steps allRules.output .x (1/2) = true := by decide +kernel

/-- Submission converts the acceptance certificate into real constructibility. -/
theorem all_rules : ConstructibleNumber (1/2 : ℝ) := by
  simpa using Program.accepts_sound (Rat.castHom ℝ) _ _ .x _ all_rules_accept

private def positiveCandidate (reverse : Bool) : ℤ :=
  ((if reverse then [1, -1] else [-1, 1]).find? (· == 1)).getD 0

/-- Choice identity, not its position in a displayed candidate list, is saved. -/
def reorderedChoice (reverse : Bool) : Program ℚ :=
  Basis.program ℚ (positiveCandidate reverse == 1)

example : reorderedChoice false = reorderedChoice true := rfl
example (reverse : Bool) : Program.accepts (reorderedChoice reverse) ⟨8⟩ .y 1 = true := by
  cases reverse <;> origami_check using
    norm_num [Basis.height, positiveCandidate]
    all_goals origami_geometry

/-- Each bad instruction is checked even though the submitted seed already exists. -/
def badFold (request : FoldRequest) (choice : Line ℚ) : Program ℚ := [.fold request choice]

/-- A missing name cannot become a reference. -/
example : Program.accepts (badFold (.axiom1 ⟨0⟩ ⟨99⟩) (Line.horizontal 0)) ⟨1⟩ .x 1 = false := by
  reject_with "Origami instruction 1:" in
    have : Program.accepts (badFold (.axiom1 ⟨0⟩ ⟨99⟩) (Line.horizontal 0)) ⟨1⟩ .x 1 = true := by origami_check
  decide +kernel

/-- A forward reference is not an existing point. -/
example : Program.accepts (badFold (.axiom1 ⟨0⟩ ⟨2⟩) (Line.horizontal 0)) ⟨1⟩ .x 1 = false := by
  reject_with "Origami instruction 1:" in
    have : Program.accepts (badFold (.axiom1 ⟨0⟩ ⟨2⟩) (Line.horizontal 0)) ⟨1⟩ .x 1 = true := by origami_check
  decide +kernel

/-- Forging a line reference to a seed does not bypass the kind check. -/
example : Program.accepts (badFold (.axiom4 ⟨0⟩ ⟨1⟩) (Line.horizontal 0)) ⟨1⟩ .x 1 = false := by
  reject_with "Origami instruction 1:" in
    have : Program.accepts (badFold (.axiom4 ⟨0⟩ ⟨1⟩) (Line.horizontal 0)) ⟨1⟩ .x 1 = true := by origami_check
  decide +kernel

/-- A wrong crease is rejected, including when it is unused. -/
example : Program.accepts (badFold (.axiom1 ⟨0⟩ ⟨1⟩) (Line.horizontal 1)) ⟨1⟩ .x 1 = false := by
  reject_with "Origami instruction 1:" in
    have : Program.accepts (badFold (.axiom1 ⟨0⟩ ⟨1⟩) (Line.horizontal 1)) ⟨1⟩ .x 1 = true := by origami_check
  decide +kernel

/-- Incidence alone does not legalize an underconstrained fold. -/
example : Program.accepts (badFold (.axiom1 ⟨0⟩ ⟨0⟩) (Line.horizontal 0)) ⟨1⟩ .x 1 = false := by
  reject_with "Origami instruction 1:" in
    have : Program.accepts (badFold (.axiom1 ⟨0⟩ ⟨0⟩) (Line.horizontal 0)) ⟨1⟩ .x 1 = true := by origami_check
  decide +kernel

/-- The right construction with the wrong final target is still rejected. -/
example : Program.accepts allRules.steps allRules.output .x 2 = false := by
  reject_with "Origami submission:" in
    have : Program.accepts allRules.steps allRules.output .x 2 = true := by origami_check
  decide +kernel

/-- Selected intersection coordinates must equal the actual intersection. -/
example : Program.accepts
    [.fold (.axiom1 ⟨0⟩ ⟨1⟩) (Line.horizontal (0 : ℚ)),
     .fold (.axiom2 ⟨0⟩ ⟨1⟩) (Line.chart 0 (1/2)),
     .intersect ⟨2⟩ ⟨3⟩ (2, 0)] ⟨4⟩ .x 2 = false := by
  reject_with "Origami instruction 3:" in
    have : Program.accepts
        [.fold (.axiom1 ⟨0⟩ ⟨1⟩) (Line.horizontal (0 : ℚ)),
         .fold (.axiom2 ⟨0⟩ ⟨1⟩) (Line.chart 0 (1/2)),
         .intersect ⟨2⟩ ⟨3⟩ (2, 0)] ⟨4⟩ .x 2 = true := by origami_check
  decide +kernel

/-- Root recipes reject the artificial zero of a cubic-encoded quadratic. -/
example : RootRecipe.quadratic (1 : ℚ) 0 (-1) 0 (by decide) = none := by decide +kernel
example : RootRecipe.squareRoot (1 : ℚ) (-1) = none := by decide +kernel

-- Nonzero hypotheses remain mandatory at the ordinary Lean API boundary.
example : True := by
  reject_with "unsolved goals" in
    have := ArithmeticRecipe.div (1 : ℚ) 0 (by norm_num)
  reject_with "unsolved goals" in
    have := RootRecipe.cubic (0 : ℚ) 0 0 0 1 (by norm_num)
  trivial

#print axioms all_rules_accept
#print axioms all_rules
#print axioms Program.accepts_sound

end LeanOrigamiTests.Text
