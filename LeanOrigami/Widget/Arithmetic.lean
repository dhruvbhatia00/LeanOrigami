import LeanOrigami.Construction.ArithmeticLibrary
import LeanOrigami.Widget.Frame

/-!
# Arithmetic templates for the visual library

Templates erase the coordinates of the proved primitive recipes. Their only
ambiguous intermediate fold is constrained to the diagonal x = y. Output
conditions independently reject a completed branch with the wrong meaning.
Frame objects are explicit parameters, never silently added as extra seeds.
-/

namespace LeanOrigami.Widget
open RecipeFrame

/-- Human-readable operation name, separate from its certified mathematical meaning. -/
def arithmeticName : ArithmeticOperation → String
  | .add => "Addition" | .sub => "Subtraction" | .neg => "Negation"
  | .mul => "Multiplication" | .inv => "Reciprocal" | .div => "Division"

/-- The exact promised scalar relation, together with the axis representation.
Reciprocal and division use multiplication equations, with nonzero input guards. -/
def arithmeticPostcondition (op : ArithmeticOperation) (output : Nat) : Condition :=
  let x := ConditionExpr.component 5 .x
  let y := ConditionExpr.component 6 .x
  let z := ConditionExpr.component output .x
  let scalar := match op with
    | .add => Condition.eq z (.add x y)
    | .sub => .eq z (.add x (.neg y))
    | .neg => .eq z (.neg x)
    | .mul => .eq z (.mul x y)
    | .inv => .eq (.mul z x) (.constant 1 1)
    | .div => .eq (.mul z y) x
  .and (.onXAxis output) scalar

/-- The arithmetic branch policy specifies one exact diagonal, rather than
its position in a solver list. Coupled with complete fold discovery and
`filterCreases_singleton`, it makes selection independent of enumeration. -/
theorem arithmetic_diagonal_policy {K : Type} [Field K] [LinearOrder K]
    (objects : Program.State K) (index : Nat) (crease : Line K)
    (reference : objects[index]? = some (.line crease)) :
    (lineIs index 1 (-1) 0).Satisfied objects ↔ crease = Line.chart (-1) 0 := by
  simp [lineIs, coordinateIs, Condition.Satisfied, Condition.valid, ConditionExpr.valid,
    Condition.Holds, ConditionExpr.eval, Component.isPoint, Component.lineAt,
    Component.value, reference, Line.ext_iff, Line.chart]

/-- The single source of arithmetic template structure. Coordinates from this
representative are erased; every invocation discovers new exact geometry. -/
def arithmeticTemplate (op : ArithmeticOperation) : RecipeTemplate := Id.run do
  let representative := op.recipe (1 : ℚ) 1 (by cases op <;> decide)
  let steps := representative.steps.map RecipeOperation.ofInstruction
  let parameters : Array RecipeParameter := RecipeFrame.parameters ++ #[
    ⟨"First scalar (x, 0)", .point⟩, ⟨"Second scalar (y, 0)", .point⟩]
  let mut requirements := RecipeFrame.requirements.push (.onXAxis 5)
  if op.arity == 7 then requirements := requirements.push (.onXAxis 6)
  match op with
  | .inv => requirements := requirements.push (.not (coordinateIs 5 .x 0))
  | .div => requirements := requirements.push (.not (coordinateIs 6 .x 0))
  | _ => pure ()
  let mut checks : Array RecipeRequirement := #[]
  for (step, i) in steps.zipIdx do
    if let .fold (.axiom5 ..) := step then
      checks := checks.push ⟨i + 1, 0, lineIs (op.arity + i) 1 (-1) 0⟩
  let output := representative.output.index
  checks := checks.push ⟨steps.length, 0, arithmeticPostcondition op output⟩
  return {
    parameters := parameters.extract 0 op.arity, steps, output, requirements, checks
    outputs := #[⟨"Result", output⟩] }

/-- Erasure is independent of operands, including zero and equal operands.
Thus the visual template really contains the operations proved by `computes`. -/
theorem arithmeticTemplate_steps {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (op : ArithmeticOperation) (x y : K) (h : op.Valid x y) :
    (op.recipe x y h).steps.map RecipeOperation.ofInstruction = (arithmeticTemplate op).steps := by
  cases op <;> rfl

/-- The visual result reference is the one used by the execution theorem. -/
theorem arithmeticTemplate_output {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (op : ArithmeticOperation) (x y : K) (h : op.Valid x y) :
    (op.recipe x y h).output.index = (arithmeticTemplate op).output := by
  cases op <;> rfl

/-- The exact conditions attached to the template accept its proved execution,
including the positive diagonal and the final arithmetic relation. -/
theorem arithmeticTemplate_checks {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (op : ArithmeticOperation) (x y : K) (h : op.Valid x y) :
    let recipe := op.recipe x y h
    let final := op.inputs x y ++ recipe.steps.map ArithmeticRecipe.selectedObject
    (arithmeticTemplate op).requirements.all (Condition.checkObjects (op.inputs x y)) = true ∧
      (arithmeticTemplate op).checks.all (fun check =>
        check.condition.checkObjects (final.take (op.arity + check.before))) = true := by
  cases op
  all_goals
    -- Reduce only finite data containers, not the algebraic propositions.
    -- Kernel conversion checks this normalization of recipe-builder output.
    run_tac Lean.Elab.Tactic.withMainContext do
      let goal ← Lean.Elab.Tactic.getMainGoal
      let target ← Lean.Meta.transform (← goal.getType) (pre := fun e => do
        let type ← Lean.Meta.whnf (← Lean.Meta.inferType e)
        if type.isAppOf ``List || type.isAppOf ``Array then
          return .done (← Lean.Meta.withTransparency .all (Lean.Meta.reduce e))
        return .continue)
      Lean.Elab.Tactic.replaceMainGoal [← goal.change target]
    norm_num [Condition.checkObjects, Condition.check, Condition.valid, ConditionExpr.valid,
      Condition.Holds, ConditionExpr.eval, Component.isPoint, Component.pointAt,
      Component.lineAt, Component.value, ArithmeticOperation.Valid] at *
    all_goals repeat' apply And.intro
    all_goals first
      | rfl
      | exact h
      | (change x - y = x + -y; exact sub_eq_add_neg x y)
      | (change 0 - x = -x; exact zero_sub x)
      | (change 1 / x * x = 1; simp [ArithmeticOperation.Valid] at h; simp [h])
      | (change x / y * y = x; simp [ArithmeticOperation.Valid] at h; simp [h])


/-- Each displayed arithmetic specification is supported by both a completed
primitive execution on every valid input and soundness of every completion
that satisfies the template's branch/output checks. -/
theorem arithmeticTemplate_contract {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (op : ArithmeticOperation) :
    RecipeContract (arithmeticTemplate op)
      (fun p : K × K => op.inputs p.1 p.2)
      (fun p => op.Valid p.1 p.2)
      (arithmeticPostcondition op (arithmeticTemplate op).output) := by
  constructor
  · intro parameters _ program final completion
    exact completion.final_condition
      ⟨(arithmeticTemplate op).steps.length, 0,
        arithmeticPostcondition op (arithmeticTemplate op).output⟩
      (by cases op <;> exact Array.mem_push_self) rfl
  · rintro ⟨x, y⟩ h
    let recipe := op.recipe x y h
    refine ⟨recipe.steps, op.inputs x y ++ recipe.steps.map ArithmeticRecipe.selectedObject,
      arithmeticTemplate_steps op x y h, (op.computes x y h).1, ?_,
      (arithmeticTemplate_checks op x y h).1, ?_, ?_⟩
    · have shape := congrArg List.length (arithmeticTemplate_steps op x y h)
      simpa [recipe] using congrArg (fun n => (op.inputs x y).length + n) shape
    · have checks := (arithmeticTemplate_checks op x y h).2
      cases op <;> simpa [ArithmeticOperation.inputs, ArithmeticOperation.arity,
        ArithmeticRecipe.inputs, recipe] using checks
    · cases op <;> constructor <;> rfl

/-- Built-in contracts are recognized by the entire serialized template, not
by its declaration name. Editing any operations, conditions, outputs, or groups
invalidates the association. Serialization is the same format used for saving. -/
def arithmeticSpecification (recipe : RecipeTemplate) : Option String := do
  let operations : List ArithmeticOperation := [.add, .sub, .neg, .mul, .inv, .div]
  let op ← operations.find? fun op => (arithmeticTemplate op).source == recipe.source
  let result := arithmeticPostcondition op recipe.output
  return conditionDescription (fun i => (recipe.parameters[i]?.map (·.name)).getD
    (if i == recipe.output then "Result" else s!"object {i}")) result

end LeanOrigami.Widget
