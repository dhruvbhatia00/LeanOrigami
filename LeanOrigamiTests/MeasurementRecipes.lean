import LeanOrigami.Widget.Workspace

/-!
# Coordinate, magnitude, and root recipe examples

These small executable checks cover discovery and sample replay, which are
separate from the universal proofs in `Widget.Measurements`. They deliberately
compare exact coordinates rather than rendered approximations.
-/
namespace LeanOrigamiTests.MeasurementRecipes
open LeanOrigami LeanOrigami.Widget

private def get {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def require (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"FAIL: {label}")
  IO.println s!"PASS: {label}"

private def invoke (op : MeasurementOperation) (p q : Point Scalar)
    (check : Scalar → Scalar → Bool) : IO Session := do
  let objects : Program.State Scalar := op.inputs p q
  let session : Session ← get (({ seeds := objects, objects } : Session).useRecipe
    op.name (measurementTemplate op) (Array.range op.arity))
  require s!"{op.name}: automatic exact branch selection"
    (session.running.isNone && session.failure.isNone && session.pending.isNone)
  let some index := session.result | throw (IO.userError "Missing result")
  require s!"{op.name}: exact output"
    (check (← get (session.selected index .x)) (← get (session.selected index .y)))
  return session

/-- Signed coordinates, zero distance, and irrational roots use the same menu API. -/
private def runCases : IO Unit := do
  let _ ← invoke .projectX (-2, 3) (0, 0) (fun x y => x == -2 && y == 0)
  let _ ← invoke .projectY (-2, 3) (0, 0) (fun x y => x == 0 && y == 3)
  let _ ← invoke .transferX (-2, 3) (0, 0) (fun x y => x == 0 && y == -2)
  let _ ← invoke .transferY (-2, 3) (0, 0) (fun x y => x == 3 && y == 0)
  let _ ← invoke .distanceX (-2, 3) (1, 7) (fun x y => x == 5 && y == 0)
  let _ ← invoke .distanceY (-2, 3) (-2, 3) (fun x y => x == 0 && y == 0)
  let _ ← invoke .sqrt (0, 0) (0, 0) (fun x y => x == 0 && y == 0)
  let root ← invoke .sqrt (2, 0) (0, 0) (fun x y => decide (0 ≤ x) && x*x == 2 && y == 0)
  let some index := root.result | throw (IO.userError "Missing square root")
  let squared : Session ← get (root.useRecipe "Square the root" (arithmeticTemplate .mul)
    #[0, 1, 2, 3, 4, index, index])
  let some result := squared.result | throw (IO.userError "Missing nested product")
  require "nested multiplication recovers the radicand" ((← get (squared.selected result .x)) == 2)
  let _ ← invoke .cbrt (-8, 0) (0, 0) (fun x y => x == -2 && y == 0)
  let _ ← invoke .cbrt (-2, 0) (0, 0) (fun x y => x*x*x == -2 && y == 0)
  for (op, p) in [(MeasurementOperation.sqrt, (-1, 0)), (.sqrt, (2, 1)), (.cbrt, (2, 1))] do
    let objects : Program.State Scalar := op.inputs p (0, 0)
    require "invalid root input rejected before execution"
      ((({ seeds := objects, objects } : Session).useRecipe op.name
        (measurementTemplate op) (Array.range op.arity)).toOption.isNone)
  require "edited measurement loses specification badge"
    ((librarySpecification { measurementTemplate .sqrt with requirements := #[] }).isNone)

#eval runCases

/-- Changing a root sample rediscovers its branch, including a repeated zero root. -/
private def sampleReplay : IO Unit := do
  let template : RecipeTemplate := measurementTemplate .sqrt
  let values : Array (Array String) :=
    #[#["0", "0"], #["1", "0"], #["0", "1", "0"],
      #["1", "0", "0"], #["0", "1"], #["4", "0"]]
  let inputs : Array SampleInput := template.parameters.zipIdx.map fun (p, i) =>
    ⟨p.name, p.kind, values[i]!, false⟩
  let (state, session) ← get (({ name := "" } : WorkspaceState).applySamples
    ({ seeds := [], objects := [] } : Session) "root" inputs 0)
  let built : Session ← get (session.useRecipe "Square root" template (Array.range 6))
  let some index := built.result | throw (IO.userError "Missing initial root")
  let zeroInputs := inputs.set! 5 ⟨"Scalar (x, 0)", .point, #["0", "0"], false⟩
  let (state, zero) ← get (state.applySamples built "root" zeroInputs index)
  require "changed sample selects the zero root automatically"
    (zero.pending.isNone && zero.failure.isNone && (← get (zero.selected index .x)) == 0)
  let negativeInputs := inputs.set! 5 ⟨"Scalar (x, 0)", .point, #["-1", "0"], false⟩
  let (failed, invalid) ← get (state.applySamples zero "root" negativeInputs index)
  require "negative sample reports an unmet requirement" invalid.failure.isSome
  let (_, recovered) ← get (failed.applySamples invalid "root" inputs index)
  require "valid sample recovers the retained construction"
    (recovered.failure.isNone && (← get (recovered.selected index .x)) == 2)

#eval sampleReplay

-- Saved source preserves the branch checks and its proved specification.
example : True := by
  run_tac do
    for operation in [MeasurementOperation.sqrt, .distanceY] do
      let recipe := measurementTemplate operation
      let parsed ← match Lean.Parser.runParserCategory (← Lean.getEnv) `term recipe.source with
        | .ok parsed => pure parsed | .error message => Lean.throwError "{message}"
      let expression ← Lean.Elab.Term.elabTermEnsuringType parsed (Lean.mkConst ``RecipeTemplate)
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let restored ← readRecipe (← Lean.instantiateMVars expression)
      unless restored.source == recipe.source && (librarySpecification restored).isSome do
        Lean.throwError "Measurement contract changed on save/reopen"
    Lean.Elab.Tactic.evalTactic (← `(tactic| trivial))

-- Verify transitive trust, including the proof-producing `cbv` template bridge.
#print axioms MeasurementOperation.computes
#print axioms measurementTemplate_steps
#print axioms measurementTemplate_contract
#print axioms square_root_policy
#print axioms cube_root_policy
#print axioms DistanceRecipe.eq_distance_iff
end LeanOrigamiTests.MeasurementRecipes
