import LeanOrigami.Widget.Workspace

/-!
# Visual arithmetic and named-output regressions

A compact set exercises the exact editor path, distinct from the universal
kernel-checked contracts. Inputs here are workspace samples, not proof seeds.
-/
namespace LeanOrigamiTests.ArithmeticRecipes
open LeanOrigami LeanOrigami.Widget

private def get {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def require (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"FAIL: {label}")
  IO.println s!"PASS: {label}"

private def invoke (op : ArithmeticOperation) (x y expected : Scalar) : IO Session := do
  let objects := op.inputs x y
  let session ← get (({ seeds := objects, objects } : Session).useRecipe
    (arithmeticName op) (arithmeticTemplate op) (Array.range op.arity))
  require s!"{arithmeticName op}: completes without a sample branch index"
    (session.running.isNone && session.failure.isNone && session.pending.isNone)
  let some index := session.result | throw (IO.userError "Missing arithmetic result")
  require s!"{arithmeticName op}: exact result" ((← get (session.selected index .x)) == expected)
  return session

/-- Signed, equal, zero, and irrational inputs share one execution path. -/
private def arithmeticCases : IO Unit := do
  let _ ← invoke .add (-2) 2 0
  let _ ← invoke .sub 3 3 0
  let _ ← invoke .neg (-2) 0 2
  let _ ← invoke .mul 0 (-3) 0
  let _ ← invoke .inv (-2) 0 (-1 / 2)
  let _ ← invoke .div 0 2 0
  let .finite (root :: _) := Scalar.realRoots (Scalar.polynomial [-2, 0, 1])
    | throw (IO.userError "Expected an irrational quadratic root")
  let square ← invoke .mul root root 2
  let some squareIndex := square.result | throw (IO.userError "Missing product")
  let doubled ← get (square.useRecipe "Add square to itself" (arithmeticTemplate .add)
    #[0, 1, 2, 3, 4, squareIndex, squareIndex])
  let some doubleIndex := doubled.result | throw (IO.userError "Missing nested sum")
  require "nested arithmetic reuses constructed result references"
    ((← get (doubled.selected doubleIndex .x)) == (4 : Scalar))
  let undone ← get doubled.undo
  require "undo removes the nested call and its contract checks"
    (undone.program.length == square.program.length && undone.checks.size == square.checks.size)

#eval arithmeticCases

/-- Bad inputs and changed templates cannot retain certified status. -/
private def rejectionCases : IO Unit := do
  let zeroInputs := ArithmeticOperation.inputs .div (1 : Scalar) 0
  require "division rejects a zero divisor before executing"
    ((({ seeds := zeroInputs, objects := zeroInputs } : Session).useRecipe "Division"
      (arithmeticTemplate .div) (Array.range 7)).toOption.isNone)
  require "editing the output invalidates specification status"
    ((arithmeticSpecification { arithmeticTemplate .add with output := 0 }).isNone)
  require "editing requirements invalidates specification status"
    ((arithmeticSpecification { arithmeticTemplate .add with requirements := #[] }).isNone)

#eval rejectionCases

/-- Names survive nested calls, saving, and serialization. -/
private def outputCases : IO Unit := do
  let named : RecipeTemplate := { midpointRecipe with
    outputs := #[⟨"Midpoint", 4⟩, ⟨"Perpendicular bisector", 3⟩] }
  let points : Program.State Scalar := [.point (0, 0), .point (2, 0)]
  let used : Session ← get (({ seeds := points, objects := points } : Session).useRecipe "Two outputs" named #[0, 1])
  let some group := (used.groups[0]? : Option RecipeGroup) | throw (IO.userError "Missing named group")
  let some bisector := ((RecipeGroup.outputs group)[1]? : Option RecipeOutput) | throw (IO.userError "Missing line output")
  require "both named outputs survive grouping"
    (group.outputs.size == 2 && bisector.index == 3)
  let used : Session ← get (used.nameOutput "Centre" 4)
  let saved : RecipeTemplate ← get (used.template midpointRecipe.parameters 4)
  let reopened : Session ← get (({ seeds := points, objects := points } : Session).useRecipe "" saved #[0, 1])
  let some centre := (reopened.outputs[0]? : Option RecipeOutput) | throw (IO.userError "Missing named point")
  let some nested := (reopened.groups[0]? : Option RecipeGroup) | throw (IO.userError "Missing nested group")
  require "named outputs survive nested save and replay"
    (centre.name == "Centre" && centre.index == 4 && nested.outputs.size == 2)
  let decoded : RecipeGroup ← get (Lean.fromJson? (Lean.toJson group) : Except String RecipeGroup)
  require "named history JSON round-trip" (decoded.source == group.source)
  require "duplicate output names are rejected" ((used.nameOutput "Centre" 0).toOption.isNone)

#eval outputCases

-- Ordinary saved source keeps both contract identity and branch conditions.
example : True := by
  run_tac do
    for operation in [ArithmeticOperation.add, .sub, .neg, .mul, .inv, .div] do
      let recipe := arithmeticTemplate operation
      let parsed ← match Lean.Parser.runParserCategory (← Lean.getEnv) `term recipe.source with
        | .ok parsed => pure parsed | .error message => Lean.throwError "{message}"
      let expression ← Lean.Elab.Term.elabTermEnsuringType parsed (Lean.mkConst ``RecipeTemplate)
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let restored ← readRecipe (← Lean.instantiateMVars expression)
      unless restored.source == recipe.source && (arithmeticSpecification restored).isSome do
        Lean.throwError "Arithmetic contract changed on save/reopen"
    let named : RecipeTemplate := { midpointRecipe with
      outputs := #[⟨"Midpoint", 4⟩, ⟨"Bisector", 3⟩]
      groups := #[⟨"Named call", 0, 3, #[0, 1],
        { index := 4, names := #[⟨"Midpoint", 4⟩, ⟨"Bisector", 3⟩] }⟩] }
    let parsed ← match Lean.Parser.runParserCategory (← Lean.getEnv) `term named.source with
      | .ok parsed => pure parsed | .error message => Lean.throwError "{message}"
    let expression ← Lean.Elab.Term.elabTermEnsuringType parsed (Lean.mkConst ``RecipeTemplate)
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let restored ← readRecipe (← Lean.instantiateMVars expression)
    unless restored.source == named.source do Lean.throwError "Named outputs changed on save/reopen"
    Lean.Elab.Tactic.evalTactic (← `(tactic| trivial))

-- The actual complete Scalar solver supplies the positive diagonal, and the
-- exact policy leaves precisely that crease, regardless of enumeration order.
private def diagonalGuard : RecipeRequirement := ⟨0, 0,
  .and (.eq (.component 0 .a) (.constant 1 1))
    (.and (.eq (.component 0 .b) (.constant (-1) 1))
      (.eq (.component 0 .c) (.constant 0 1)))⟩

example : ∃ choices : List (Line Scalar),
    Scalar.folds (.axiom5 (1, 0) (0, 0) (Line.chart 0 0)) = some choices ∧
    RecipeRequirement.filterCreases #[diagonalGuard] 0 [] choices = [Line.chart (-1) 0] := by
  let input : FoldInput Scalar := .axiom5 (1, 0) (0, 0) (Line.chart 0 0)
  have finite : input.FiniteCondition := by dsimp [input]; origami_geometry
  have geometry : input.Satisfies (Line.chart (-1) 0) := by dsimp [input]; origami_geometry
  obtain ⟨choices, discovered, member⟩ := FoldInput.candidates_complete Scalar.rootList input
    finite (Scalar.rootsCover input finite) (Line.chart (-1) 0) geometry
  refine ⟨choices, discovered, ?_⟩
  have policy (crease : Line Scalar) : diagonalGuard.condition.Satisfied [.line crease] ↔
      crease = Line.chart (-1) 0 := arithmetic_diagonal_policy _ 0 crease rfl
  apply RecipeRequirement.filterCreases_singleton _ _ _ _ _ (Scalar.folds_nodup _ _ discovered)
  · apply (RecipeRequirement.mem_filterCreases _ _ _ _ _).mpr
    refine ⟨member, ?_⟩
    intro check hc _
    have equal : check = diagonalGuard := by simpa using hc
    subst check
    exact (policy _).mpr rfl
  · intro crease hc
    have conditions := (RecipeRequirement.mem_filterCreases _ _ _ _ _).mp hc
    exact (policy crease).mp (conditions.2 diagonalGuard (by simp) rfl)
end LeanOrigamiTests.ArithmeticRecipes
