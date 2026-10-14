import LeanOrigami.Widget.Workspace

/-!
# Requirements through authoring, nesting, saving, and replay

Run this focused file through Lean/LSP. Its small executable checks exercise
editor behavior; the general mathematical checker proofs live in the library.
-/
namespace LeanOrigamiTests.RecipeRequirements
open LeanOrigami LeanOrigami.Widget

private def get {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def require (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"FAIL: {label}")
  IO.println s!"PASS: {label}"

/-- A nested call requires its first point to lie on the horizontal axis. -/
def axisMidpoint : RecipeTemplate :=
  { midpointRecipe with requirements := midpointRecipe.requirements.push (.onXAxis 0) }

/-- Exercise exact runtime decisions and retained recipes with a few rational
samples plus one genuinely irrational root. -/
def run : IO Unit := do
  let empty : WorkspaceState := { name := "" }
  let seedless : Session := { seeds := [], objects := [] }
  let inputs : Array SampleInput := #[⟨"A", .point, #["0", "0"], false⟩,
    ⟨"B", .point, #["2", "0"], false⟩]
  let (state, session) ← get (empty.applySamples seedless "quarter" inputs 0)
  let first ← get (session.useRecipe "Midpoint" midpointRecipe #[0, 1])
  let second ← get (first.useRecipe "Axis midpoint" axisMidpoint #[4, 1])
  let recipe ← get (second.template midpointRecipe.parameters 7)
  require "nested guards retain shifted references and boundaries"
    (recipe.checks.size == 3 && recipe.checks[2]?.any (fun check => check.before == 3 && check.owner == 3))
  require "nested geometric result" ((← get (second.selected 7 .x)) == (3 / 2 : Scalar))
  let undone ← get second.undo
  require "undo removes just the latest call and its requirements"
    (undone.program.length == 3 && undone.checks.size == 1)
  let (_, failed) ← get (state.applySamples second "quarter"
    #[⟨"A", .point, #["0", "2"], false⟩, ⟨"B", .point, #["2", "0"], false⟩] 7)
  require "nested requirement is enforced after the first call on new samples"
    (failed.program.length == 3 && failed.failure.isSome && failed.running.isSome)

  let (requiredState, required) ← get (state.editRequirement first 4
    (some ⟨"onXAxis", #[0], #[]⟩) 0)
  require "author condition retained" (required.requirements.size == 1)
  let (badState, bad) ← get (requiredState.applySamples required "quarter"
    #[⟨"A", .point, #["0", "1"], false⟩, ⟨"B", .point, #["2", "0"], false⟩] 4)
  require "input failure retains the recipe but executes no steps"
    (badState.replaying && bad.program.isEmpty && bad.failure.isSome)
  let (_, recovered) ← get (badState.editRequirement bad 4 none 0)
  require "removing the requirement replays retained steps"
    (recovered.program.length == 3 && recovered.failure.isNone)
  let (stateOr, sessionOr) ← get (requiredState.editRequirement required 4
    (some ⟨"onYAxis", #[0], #[]⟩) 0)
  let (_, combined) ← get (stateOr.editRequirement sessionOr 4
    (some ⟨"or", #[0, 1], #[]⟩) 0)
  require "OR replaces both operands" (combined.requirements.size == 1)
  require "wrong-kind requirement is rejected by the shared API"
    ((state.editRequirement first 4 (some ⟨"parallel", #[0, 1], #[]⟩) 0).toOption.isNone)

  let polynomial ← get (RequirementInput.condition ⟨"polynomialEq", #[0], #["x", "-2, 0, 1"]⟩ #[])
  let .finite (root :: _) := Scalar.realRoots (Scalar.polynomial [-2, 0, 1])
    | throw (IO.userError "Expected a real quadratic root")
  require "irrational root satisfies the exact polynomial"
    (polynomial.checkObjects [.point (root, (0 : Scalar))])
  require "irrational root differs from rational 1"
    (!(Condition.eq (.component 0 .x) (.constant 1 1)).checkObjects [.point (root, (0 : Scalar))])

#eval run

-- Instantiate the proved real interpretation; no native results prove this theorem.
example (objects : List (Object Scalar)) (condition : Condition) :
    condition.checkObjects objects = true ↔
      condition.Satisfied (objects.map (Object.map Scalar.realHom)) :=
  Condition.checkObjects_map_iff Scalar.realHom Scalar.toReal_le Scalar.toReal_lt objects condition

-- Source round-trip includes both editable requirements and inherited timed checks.
example : True := by
  run_tac do
    let recipe : RecipeTemplate := { axisMidpoint with checks := #[⟨1, 0, .onLine 0 2⟩] }
    let parsed ← match Lean.Parser.runParserCategory (← Lean.getEnv) `term recipe.source with
      | .ok parsed => pure parsed | .error message => Lean.throwError "{message}"
    let expression ← Lean.Elab.Term.elabTermEnsuringType parsed (Lean.mkConst ``RecipeTemplate)
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let restored ← readRecipe (← Lean.instantiateMVars expression)
    unless restored.source == recipe.source do Lean.throwError "Requirements changed on save/reopen"
    Lean.Elab.Tactic.evalTactic (← `(tactic| trivial))

end LeanOrigamiTests.RecipeRequirements
