import LeanOrigami.Widget.Workspace
import LeanOrigami.Widget.Export

/-!
# Exact sample setup and replay

These executable regressions exercise untrusted exploration. Saved construction
proofs are checked separately; samples never extend the proof's permitted seeds.
-/

namespace LeanOrigamiTests.SampleWorkspace
open LeanOrigami LeanOrigami.Widget

private def get {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def require (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"FAIL: {label}")
  IO.println s!"PASS: {label}"

private def pointInput (name x y : String) : SampleInput := ⟨name, .point, #[x, y], false⟩
private def lineInput (name : String) (values : Array String) : SampleInput := ⟨name, .line, values, false⟩

/-- Exercise setup, exact replacements, replay recovery, and baseline reset. -/
def run : IO Unit := do
  require "exact signed fractions" ((← get (sampleRational " -2 / -3 ")) == (2 / 3 : Rat))
  for text in ["1/0", "0.5", "NaN", "1/2/3", ""] do
    require s!"reject invalid rational {text}" (sampleRational text).toOption.isNone
  require "zero normal rejected" ((lineInput "L" #["0", "0", "1"]).replacement.toOption.isNone)
  require "coincident placement points rejected"
    ((lineInput "L" #["1", "2", "1", "2"]).replacement.toOption.isNone)
  let (placed, _) ← get ((lineInput "L" #["0", "2", "3", "2"]).replacement)
  require "two clicks produce the exact line" (match placed with
    | .line l => l == Line.horizontal 2 | _ => false)
  let empty : WorkspaceState := { name := "" }
  let noSeeds : Session := { seeds := [], objects := [] }
  let a := pointInput "A" "0" "0"
  let b := pointInput "B" "1" "0"
  let inputs := #[a, b]
  require "blank input names rejected"
    ((empty.applySamples noSeeds "midpoint" #[pointInput " " "0" "0"] 0).toOption.isNone)
  require "duplicate input names rejected"
    ((empty.applySamples noSeeds "midpoint" #[a, a] 0).toOption.isNone)
  let (state, session) ← get (empty.applySamples noSeeds "midpoint" inputs 0)
  require "setup uses only chosen samples" (session.objects.length == 2 && session.program.isEmpty)
  let built ← get (session.useRecipe "Midpoint" midpointRecipe #[0, 1])
  let (moved, preview) ← get (state.applySamples built "midpoint"
    #[pointInput "A" "2" "4", pointInput "B" "6" "8"] 2)
  require "new samples recompute midpoint"
    ((← get (preview.selected 2 .x)) == 4 && (← get (preview.selected 2 .y)) == 6)
  require "sample proof seeds are not accepted" ((← prepareComposition preview 2 .x).toOption.isNone)
  let (_, unchanged) ← get (moved.applySamples preview "midpoint" moved.inputs 2)
  require "keep retains exact current samples" ((← get (unchanged.selected 2 .x)) == 4)
  let (_, reset) ← get (moved.resetSamples preview 2)
  require "reset restores initial samples and retains instructions"
    ((← get (reset.selected 2 .x)) == (1 / 2 : Scalar) && reset.program.length == 1)
  require "parameter identities cannot change"
    ((state.applySamples built "midpoint" #[pointInput "C" "0" "0", b] 2).toOption.isNone)

  -- A valid recipe whose third step fails only for the changed samples.
  let three := inputs.push (pointInput "C" "0" "1")
  let (state, session) ← get (empty.applySamples noSeeds "crossing" three 0)
  let crossing : RecipeTemplate := {
    parameters := three.map fun p => ⟨p.name, p.kind⟩
    steps := [.fold (.axiom1 ⟨0⟩ ⟨1⟩), .fold (.axiom1 ⟨0⟩ ⟨2⟩), .intersect ⟨3⟩ ⟨4⟩]
    output := 5 }
  let built ← get (session.useRecipe "Crossing" crossing #[0, 1, 2])
  let (failed, partialReplay) ← get (state.applySamples built "crossing"
    (three.set! 2 (pointInput "C" "2" "0")) 3)
  require "failure retains valid prefix and identifies its step"
    (partialReplay.active.program.length == 2 && partialReplay.failure.any (·.startsWith "Step 3:"))
  require "full instructions survive a failed preview"
    (failed.replaying && failed.template.any (fun r => r.steps.length == 1 && r.output == 3))
  require "partial preview cannot be recorded as a complete recipe"
    ((partialReplay.template crossing.parameters 0).toOption.isNone)
  let (recovered, complete) ← get (failed.applySamples partialReplay "crossing"
    (three.set! 2 (pointInput "C" "0" "2")) 0)
  require "recovery restores the retained output and groups"
    (!recovered.replaying && complete.result == some 3 && complete.groups.size == 1)
  require "recovery preserves all steps" (complete.program.length == 1 && complete.failure.isNone)
  let (_, restored) ← get (failed.resetSamples partialReplay 0)
  require "reset also recovers from failure" (restored.result == some 3 && restored.failure.isNone)

  let axes := #[lineInput "L" #["1", "0", "0"], lineInput "M" #["0", "1", "0"]]
  let (state, session) ← get (empty.applySamples noSeeds "bisectors" axes 0)
  let bisect : RecipeTemplate := {
    parameters := axes.map fun p => ⟨p.name, p.kind⟩
    steps := [.fold (.axiom3 ⟨0⟩ ⟨1⟩)], output := 2 }
  let paused ← get (session.useRecipe "Bisectors" bisect #[0, 1])
  let chosen ← get (paused.choose 0)
  let (state, fresh) ← get (state.applySamples chosen "bisectors" state.inputs 2)
  require "sample replay asks for a fresh branch"
    (state.replaying && fresh.active.pending.any (fun p => p.2.length == 2))
  let selected ← get (fresh.choose 1 (retainFailure := true))
  require "fresh branch completes the retained recipe" (selected.running.isNone && selected.result == some 2)

  IO.FS.createDirAll ".lake/samples"
  IO.FS.writeFile ".lake/samples/Samples.txt" moved.sampleSource
  IO.println "PASS: edited exact sample source exported"

/-- An existing workspace may use genuinely nonrational exact sample values. -/
def algebraicSamples : RecipeSamples :=
  match Scalar.realRoots (Scalar.polynomial [-2, 0, 1]) with
  | .finite (x :: _) => [("First point", .point (x, 0)), ("Second point", .point (1, 0))]
  | _ => []

/-- Check names and re-elaborate saved sample expressions, including an untouched
input. These checks run in Lean's elaborator, independently of browser state. -/
example : True := by
  run_tac do
    let sampleExpr ← Lean.Elab.Term.elabTerm (← `(([] : RecipeSamples))) none
    let context : WorkspaceContext := {
      name := "", namespaceName := `LeanOrigamiTests.SampleWorkspace
      sampleSource := "[]", samples := sampleExpr, recipe := Lean.mkConst ``midpointRecipe
      parameters := #[], draft := true }
    let _ ← validateRecipeName context "newRecipe"
    for name in ["", "bad name", "by", "run", "A.B"] do
      let accepted ← try
        let _ ← validateRecipeName context name
        pure true
      catch _ => pure false
      if accepted then Lean.throwError "Unexpectedly accepted recipe name {name}"
    let sourceContext : WorkspaceContext := { context with
      name := "sampleRecipe", draft := false
      samples := Lean.mkConst ``algebraicSamples
      sampleSource := "LeanOrigamiTests.SampleWorkspace.algebraicSamples"
      parameters := midpointRecipe.parameters }
    let (state, session) ← match ← openWorkspace sourceContext with
      | .ok value => pure value
      | .error message => Lean.throwError "{message}"
    let first ← match Program.point session.objects ⟨0⟩ with
      | .ok value => pure value
      | .error _ => Lean.throwError "Missing algebraic input"
    unless first.1 ^ 2 == (2 : Scalar) do Lean.throwError "Expected an irrational quadratic root"
    let (changed, _) ← match state.applySamples session "sampleRecipe"
        #[⟨"First point", .point, #[], true⟩, pointInput "Second point" "3/2" "-2"] 4 with
      | .ok value => pure value
      | .error message => Lean.throwError "{message}"
    let parsed ← match Lean.Parser.runParserCategory (← Lean.getEnv) `term changed.sampleSource with
      | .ok value => pure value
      | .error message => Lean.throwError "{message}"
    let expression ← Lean.Elab.Term.elabTermEnsuringType parsed (Lean.mkConst ``RecipeSamples)
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let restored ← readSamples (← Lean.instantiateMVars expression)
    unless decide (restored = changed.samples) do Lean.throwError "Saved samples changed exact values."
    Lean.Elab.Tactic.evalTactic (← `(tactic| trivial))

end LeanOrigamiTests.SampleWorkspace

def main : IO Unit := LeanOrigamiTests.SampleWorkspace.run
