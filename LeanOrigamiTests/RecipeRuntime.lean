import LeanOrigami.Widget.Export
import LeanOrigami.Widget.Workspace

/-!
# Parameterized recipe integration

Run through `scripts/validate.sh` or the focused commands in docs/recipes.md.
These executable assertions test exploration, not proof certification. The
emitted Replay.lean independently checks the saved proof in the kernel.
-/

namespace LeanOrigamiTests.RecipeRuntime
open LeanOrigami LeanOrigami.Widget

/-- A declaration registered outside the command is available by the same API. -/
@[«origami_recipe»] def registeredMidpoint : RecipeTemplate := midpointRecipe

/-- Serialization is ordinary Lean data, including quoted names and groups. -/
example : True := by
  run_tac do
    let recipe : RecipeTemplate := { midpointRecipe with
      parameters := #[⟨"A \"quoted\"", .point⟩, ⟨"B", .point⟩]
      groups := #[⟨"Nested midpoint", 0, 3, #[0, 1], 4⟩] }
    -- Parse after a long declaration header too: multiline record indentation
    -- must not depend on where the widget inserts the generated expression.
    let embedded := "def aDeliberatelyLongRecipeDeclarationName : LeanOrigami.Widget.RecipeTemplate := " ++ recipe.source
    match Lean.Parser.runParserCategory (← Lean.getEnv) `command embedded with
    | .ok _ => pure ()
    | .error message => throwError "Embedded recipe source failed: {message}"
    let parsed ← match Lean.Parser.runParserCategory (← Lean.getEnv) `term recipe.source with
      | .ok parsed => pure parsed
      | .error message => throwError "{message}"
    let value ← Lean.Elab.Term.elabTermEnsuringType parsed (Lean.mkConst ``RecipeTemplate)
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let restored ← readRecipe (← Lean.instantiateMVars value)
    unless restored.source == recipe.source do throwError "Recipe source round-trip changed the data."
    let library ← recipeLibrary
    unless library.any (fun (r : NamedRecipe) => r.id == "recipe:LeanOrigamiTests.RecipeRuntime.registeredMidpoint") do
      throwError "The registered recipe is missing."
    Lean.Elab.Tactic.evalTactic (← `(tactic| trivial))

private def get {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def require (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"FAIL: {label}")
  IO.println s!"PASS: {label}"

/-- Reuse, branches, rollback, arbitrary samples, and independent proof export. -/
def run : IO Unit := do
  require "valid midpoint template"
    (midpointRecipe.validate.toOption.map (· == ObjectKind.point) == some true)
  require "missing recipe output rejected" ((RecipeTemplate.validate { midpointRecipe with output := 99 }).toOption.isNone)
  require "wrong reference kind rejected"
    ((RecipeTemplate.validate { midpointRecipe with steps := [.intersect ⟨0⟩ ⟨1⟩] }).toOption.isNone)
  require "forward reference rejected"
    ((RecipeTemplate.validate { midpointRecipe with steps := [.fold (.axiom1 ⟨0⟩ ⟨2⟩)] }).toOption.isNone)
  let half ← get (({} : Session).useRecipe "Midpoint" midpointRecipe #[0, 1])
  require "midpoint on proof seeds" ((← get (half.selected 2 .x)) == (1 / 2 : Scalar))
  require "one retained call" (half.groups.size == 1 && half.program.length == 1)
  require "atomic recipe undo" ((← get half.undo).program.isEmpty)
  require "duplicate inputs reject geometrically"
    ((({} : Session).useRecipe "Midpoint" midpointRecipe #[0, 0]).toOption.isNone)
  require "missing input rejected"
    ((({} : Session).useRecipe "Midpoint" midpointRecipe #[0, 99]).toOption.isNone)
  require "wrong arity rejected"
    ((({} : Session).useRecipe "Midpoint" midpointRecipe #[0]).toOption.isNone)
  let withLine ← get ((← get (half.preview (.axiom1 ⟨0⟩ ⟨1⟩))).choose 0)
  require "wrong object kind rejected" ((withLine.useRecipe "Midpoint" midpointRecipe #[0, 3]).toOption.isNone)

  let seeds : Program.State Scalar := [.point (2, 4), .point (6, 8)]
  let changed ← get (({ seeds, objects := seeds } : Session).useRecipe "Midpoint" midpointRecipe #[1, 0])
  require "changed, rotated inputs recompute both coordinates"
    ((← get (changed.selected 2 .x)) == 4 && (← get (changed.selected 2 .y)) == 6)
  require "sample workspace cannot pass the standard-seed checker" ((← prepareComposition changed 2 .x).toOption.isNone)

  let quarter ← get (half.useRecipe "Midpoint" midpointRecipe #[0, 2])
  let nested ← get (quarter.template midpointRecipe.parameters 3)
  let expanded ← get (({} : Session).useRecipe "Quarter" nested #[0, 1])
  require "nested recipe retains its private scope" ((← get (expanded.selected 2 .x)) == (1 / 4 : Scalar) &&
    expanded.groups.size == 1 && expanded.program.length == 1)
  require "nested call undo is atomic" ((← get expanded.undo).program.isEmpty)
  let changedNested ← get (({ seeds, objects := seeds } : Session).useRecipe "Quarter" nested #[0, 1])
  require "nested recipe recomputes on new samples"
    ((← get (changedNested.selected 2 .x)) == 3 && (← get (changedNested.selected 2 .y)) == 5)

  let perpendicular : RecipeTemplate := {
    parameters := #[⟨"Through", .point⟩, ⟨"Reference", .line⟩]
    steps := [.fold (.axiom4 ⟨0⟩ ⟨1⟩)], output := 2 }
  let mixed : Program.State Scalar := [.point (3, 2), .line (Line.chart 0 7)]
  let lineResult ← get (({ seeds := mixed, objects := mixed } : Session).useRecipe
    "Perpendicular" perpendicular #[0, 1])
  let crease ← get ((Program.line lineResult.objects ⟨2⟩).mapError errorMessage)
  require "point/line parameters and line output" (crease == Line.horizontal 2)

  let bisect : RecipeTemplate := {
    parameters := #[⟨"First line", .line⟩, ⟨"Second line", .line⟩]
    steps := [.fold (.axiom3 ⟨0⟩ ⟨1⟩)], output := 2 }
  let axes : Program.State Scalar := [.line (Line.chart 0 0), .line (Line.horizontal 0)]
  let paused ← get (({ seeds := axes, objects := axes } : Session).useRecipe "Bisect" bisect #[0, 1])
  require "ambiguous fold pauses with two current choices"
    (paused.running.isSome && paused.active.pending.any (fun p => p.2.length == 2))
  require "pending recipe cannot be saved" ((paused.template bisect.parameters 0).toOption.isNone)
  require "out-of-range branch rejected" ((paused.choose 99).toOption.isNone)
  let first ← get (paused.choose 0)
  let second ← get (paused.choose 1)
  let firstLine ← get ((Program.line first.objects ⟨2⟩).mapError errorMessage)
  let secondLine ← get ((Program.line second.objects ⟨2⟩).mapError errorMessage)
  require "both branches are valid and different" (firstLine != secondLine && first.running.isNone && second.running.isNone)
  let recorded ← get (first.template bisect.parameters 2)
  let replayed ← get (({ seeds := axes, objects := axes } : Session).useRecipe "Replay" recorded #[0, 1])
  require "recording forgets the sample branch" replayed.running.isSome
  require "cancel restores arbitrary workspace seeds" ((← get paused.undo).objects.length == 2)
  let prefixed : RecipeTemplate := { bisect with
    parameters := bisect.parameters.push ⟨"Through", .point⟩
    steps := .fold (.axiom4 ⟨2⟩ ⟨0⟩) :: bisect.steps, output := 4 }
  let threeSeeds : Program.State Scalar := axes ++ [.point (1, 1)]
  let partialCall ← get (({ seeds := threeSeeds, objects := threeSeeds } : Session).useRecipe
    "Pause after a fold" prefixed #[0, 1, 2])
  require "cancellation rolls back completed prefix steps"
    (partialCall.active.program.length == 1 && (← get partialCall.undo).objects.length == 3)

  -- Fail after a branch, then verify that the still-available snapshot can be cancelled.
  let failing : RecipeTemplate := { bisect with steps := bisect.steps ++ [.intersect ⟨2⟩ ⟨2⟩], output := 3 }
  let waiting ← get (({ seeds := axes, objects := axes } : Session).useRecipe "Fails later" failing #[0, 1])
  require "later degeneracy rejects without committing the call" ((waiting.choose 0).toOption.isNone)
  require "failed continuation can still be cancelled" ((← get waiting.undo).program.isEmpty)

  IO.FS.createDirAll ".lake/recipes"
  let saved ← get (← prepareComposition half 2 .x)
  let history := "#[" ++ String.intercalate ", " (half.groups.toList.map RecipeGroup.source) ++ "]"
  let source := "import LeanOrigami.Widget\nopen LeanOrigami LeanOrigami.Widget\n\n" ++
    "origami_recipe recorded samples ([(\"First point\", .point (2, 4)), (\"Second point\", .point (6, 8))]) saved (" ++
    nested.source ++ ")\n\n" ++
    "theorem recipe_half : ConstructibleNumber (1 / 2 : ℝ) := by\n" ++
    "  origami history (" ++ history ++ ") composed (" ++ saved.replace "\n" "\n  " ++ ")\n" ++
    "#print axioms recipe_half\n#print axioms SavedConstruction.sound\n"
  IO.FS.writeFile ".lake/recipes/Replay.lean" source
  IO.println "PASS: recipe and proof source exported; fresh kernel replay remains separate"

end LeanOrigamiTests.RecipeRuntime

def main : IO Unit := LeanOrigamiTests.RecipeRuntime.run

