import LeanOrigami.Widget.Arithmetic

/-!
Small contract regressions. The symbolic theorems cover all ordered fields;
these examples exercise their public interface and the declarative output data.
-/

open LeanOrigami LeanOrigami.Widget

-- Zero and equal operands are part of the advertised arithmetic domain.
example : ArithmeticRecipe.Computes (ArithmeticRecipe.sub (3 : ℚ) 3) 3 3 0 := by
  simpa using ArithmeticRecipe.sub_computes (3 : ℚ) 3

example : ArithmeticRecipe.Computes (ArithmeticRecipe.mul (0 : ℚ) (-2)) 0 (-2) 0 := by
  simpa using ArithmeticRecipe.mul_computes (0 : ℚ) (-2)

-- Old, positional single-output history data remains readable.
example : (⟨"old", 0, 1, #[0], 2⟩ : RecipeGroup).outputs = #[] := rfl

private def twoOutputs : RecipeTemplate := {
  parameters := #[⟨"A", .point⟩, ⟨"B", .point⟩]
  steps := [.fold (.axiom1 ⟨0⟩ ⟨1⟩)]
  output := 0
  outputs := #[⟨"Vertex", 0⟩, ⟨"Direction line", 2⟩] }

#eval show IO Unit from do
  unless twoOutputs.validate.isOk do throw (IO.userError "Valid named outputs rejected")
  unless !({ twoOutputs with outputs := #[⟨"Missing", 3⟩] }).validate.isOk do
    throw (IO.userError "Missing named output accepted")
  unless !({ twoOutputs with outputs := #[⟨"Same", 0⟩, ⟨"Same", 2⟩] }).validate.isOk do
    throw (IO.userError "Duplicate names accepted")

#print axioms ArithmeticRecipe.add_computes
#print axioms ArithmeticRecipe.sub_computes
#print axioms ArithmeticRecipe.mul_computes
#print axioms ArithmeticRecipe.div_computes
#print axioms ArithmeticRecipe.Computes.output_of_execute

-- A description cannot certify an incorrect recipe. This recipe returns zero,
-- so a contract saying its result equals one is impossible, even though the
-- underlying empty construction is perfectly legal.
private def incorrect : RecipeTemplate := { parameters := #[⟨"A", .point⟩] }
example : ¬RecipeContract incorrect (fun _ : Unit => [.point ((0 : ℚ), 0)])
    (fun _ => True) (.eq (.component 0 .x) (.constant 1 1)) := by
  intro contract
  obtain ⟨program, final, completion⟩ := contract.succeeds () trivial
  have empty : program = [] := by simpa [incorrect] using completion.shape
  subst program
  have state : final = [.point ((0 : ℚ), 0)] := by
    simpa [Program.execute] using completion.execution.symm
  have meaning := contract.sound () trivial [] final completion
  subst final
  norm_num [Condition.Satisfied, Condition.Holds, ConditionExpr.eval, Component.value] at meaning

-- Every operation, including unary aliases, has the same contract interface.
example (op : ArithmeticOperation) :
    RecipeContract (arithmeticTemplate op)
      (fun p : ℚ × ℚ => op.inputs p.1 p.2) (fun p => op.Valid p.1 p.2)
      (arithmeticPostcondition op (arithmeticTemplate op).output) :=
  arithmeticTemplate_contract op

#print axioms ArithmeticOperation.computes
#print axioms arithmeticTemplate_contract
#print axioms arithmetic_diagonal_policy
#print axioms RecipeRequirement.filterCreases_singleton

-- A replayable proof from the two permitted seeds, using the same primitive
-- arithmetic program whose template is offered in the visual menu.
private def two := (ArithmeticOperation.add.recipe (1 : ℚ) 1 trivial).append
  (Basis.program ℚ true) (ArithmeticRecipe.Arguments.mk ⟨0⟩ ⟨1⟩ ⟨2⟩ ⟨3⟩ ⟨8⟩ ⟨1⟩ ⟨1⟩).indices
example : Program.accepts two.1 two.2 .x (2 : ℚ) = true := by
  unfold two
  origami_check using
    origami_geometry
    all_goals norm_num [Basis.height]
