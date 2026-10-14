import LeanOrigami.Widget.Session
import Lean

/-!
# Standalone recipe workspace data

A workspace's exact samples are for exploration only. Its registered template
contains no samples. Native evaluation here opens data for the editor; it is
never evidence for the construction checker or a theorem about a recipe.
-/

namespace LeanOrigami.Widget
open Lean Meta

/-- Named sample objects become the typed parameters of a standalone recipe. -/
abbrev RecipeSamples := List (String × Object Scalar)

/-- A recipe visible in the current Lean environment. -/
structure NamedRecipe where
  id : String
  name : String
  template : RecipeTemplate

/-- Menu data omits both sample coordinates and the executable template. -/
structure RecipeMenuItem where
  id : String
  name : String
  parameters : Array RecipeParameter
  requirements : Array String := #[]
  deriving ToJson, FromJson

/-- Capture the command's original spelling and elaborated data for reopening
and versioned replacement. The template declaration itself contains no samples. -/
structure WorkspaceContext where
  name : String
  namespaceName : Name
  sampleSource : String
  draft : Bool := false
  samples : Expr
  recipe : Expr
  parameters : Array RecipeParameter

initialize recipeAttribute : TagAttribute ←
  registerTagAttribute `origami_recipe "Offer a RecipeTemplate declaration in origami widgets."

private unsafe def readRecipeUnsafe (expression : Expr) : MetaM RecipeTemplate :=
  evalExpr RecipeTemplate (mkConst ``RecipeTemplate) expression

/-- Evaluate template data for discovery, never a proof. -/
@[implemented_by readRecipeUnsafe]
opaque readRecipe (expression : Expr) : MetaM RecipeTemplate

private unsafe def readSamplesUnsafe (expression : Expr) : MetaM RecipeSamples :=
  evalExpr RecipeSamples (mkConst ``RecipeSamples) expression

/-- Load exact sample objects outside the certification path. -/
@[implemented_by readSamplesUnsafe]
opaque readSamples (expression : Expr) : MetaM RecipeSamples

private unsafe def readGroupsUnsafe (expression : Expr) : MetaM (Array RecipeGroup) :=
  evalExpr (Array RecipeGroup) (mkApp (mkConst ``Array [0]) (mkConst ``RecipeGroup)) expression

/-- History annotations are display data, separate from a saved proof certificate. -/
@[implemented_by readGroupsUnsafe]
opaque readGroups (expression : Expr) : MetaM (Array RecipeGroup)

/-- Collect the built-in and earlier registered recipes, checking their types
and reference structure before presenting them as operations. -/
def recipeLibrary : MetaM (Array NamedRecipe) := do
  let mut library := #[NamedRecipe.mk "recipe:midpoint" "Midpoint (distinct points)" midpointRecipe]
  let env ← getEnv
  let mut names := (recipeAttribute.ext.getState env).toArray
  for i in [:env.header.moduleNames.size] do
    names := names ++ recipeAttribute.ext.getModuleEntries env i
  for name in names do
    let value := mkConst name
    unless ← isDefEq (← inferType value) (mkConst ``RecipeTemplate) do
      throwError "{name}: origami_recipe requires a RecipeTemplate declaration."
    let recipe ← readRecipe value
    match recipe.validate with
    | .error message => throwError "Invalid recipe {name}: {message}"
    | .ok _ => pure ()
    library := library.push ⟨s!"recipe:{name}", name.toString, recipe⟩
  return library

/-- Editable rational replacements. `keep` retains the server's exact object,
including algebraic values that have no rational input representation. -/
structure SampleInput where
  name : String
  kind : ObjectKind
  values : Array String := #[]
  keep : Bool := true
  deriving ToJson, FromJson

/-- A recipe and its sample baseline survive partial or failed execution. Source
patches are indexed by parameter, so repeated dragging does not grow the source. -/
structure WorkspaceState where
  name : String
  ready : Bool := false
  initialSamples : RecipeSamples := []
  initialSource : String := "[]"
  samples : RecipeSamples := []
  inputs : Array SampleInput := #[]
  initialInputs : Array SampleInput := #[]
  edits : Array (Option String) := #[]
  template : Option RecipeTemplate := none
  replaying : Bool := false

/-- Sample status is separate from any universal correctness claim. -/
structure RequirementView where
  description : String
  status : String
  deriving ToJson, FromJson

/-- Only display/setup data crosses the RPC boundary. -/
structure WorkspaceView where
  name : String
  ready : Bool
  nameLocked : Bool
  inputs : Array SampleInput
  replaying : Bool
  requirements : Array RequirementView := #[]
  nestedRequirements : Array RequirementView := #[]
  deriving ToJson, FromJson

private def ratSource (q : Rat) : String := s!"({q.num} / {q.den} : LeanOrigami.Scalar)"

/-- Validate a complete replacement and return both its exact value and source.
Line placement uses four coordinates; equation entry uses a nonzero normal. -/
def SampleInput.replacement (input : SampleInput) : Except String (Object Scalar × String) := do
  let values ← input.values.toList.mapM sampleRational
  match input.kind, values with
  | .point, [x, y] =>
    return (.point ((x : Scalar), (y : Scalar)), s!".point ({ratSource x}, {ratSource y})")
  | .line, values =>
    let (a, b, c) ← match values with
      | [a, b, c] => pure (a, b, c)
      | [x, y, u, v] => pure (y - v, u - x, (y - v) * x + (u - x) * y)
      | _ => throw "A line needs three coefficients or two distinct placement points."
    if a == 0 && b == 0 then throw "A line needs a nonzero normal; its placement points must be distinct."
    if a == 0 then
      return (.line (Line.horizontal ((c / b : Rat) : Scalar)), s!".line (LeanOrigami.Line.horizontal {ratSource (c / b)})")
    else
      return (.line (Line.chart ((b / a : Rat) : Scalar) ((c / a : Rat) : Scalar)),
        s!".line (LeanOrigami.Line.chart {ratSource (b / a)} {ratSource (c / a)})")
  | _, _ => throw "A point needs both coordinates."

private def sampleEntry (name value : String) : String :=
  "(" ++ Json.compress (toJson name) ++ ", " ++ value ++ ")"

/-- Preserve a complete replay even when only its prefix has been executed. -/
def WorkspaceState.record (state : WorkspaceState) (session : Session) (output : Nat) :
    Except String RecipeTemplate := do
  if state.replaying then
    let some recipe := state.template | throw "The preview has no retained recipe."
    return recipe
  session.template (state.inputs.map fun p => ⟨p.name, p.kind⟩)
    (if session.objects[output]?.isSome then output else 0)

private def WorkspaceState.replay (state : WorkspaceState) (recipe : RecipeTemplate) :
    Except String (WorkspaceState × Session) := do
  let seeds := state.samples.map Prod.snd
  let session ← ({ seeds, objects := seeds } : Session).useRecipe "" recipe
    (Array.range seeds.length) (retainFailure := true)
  return ({ state with template := some recipe, replaying := session.running.isSome }, session)

/-- Edit only author-declared input conditions. Inherited conditions belong to
calls, and remain attached to them. Boolean combinations replace their operands
so OR does not accidentally keep enforcing both original conditions. -/
def WorkspaceState.editRequirement (state : WorkspaceState) (session : Session) (output : Nat)
    (input : Option RequirementInput) (removeIndex : Nat) : Except String (WorkspaceState × Session) := do
  if session.running.isSome && !state.replaying then
    throw "Finish or cancel the nested recipe before editing requirements."
  let recipe ← state.record session output
  let requirements ← match input with
    | none => do
      unless removeIndex < recipe.requirements.size do throw "This requirement no longer exists."
      pure (recipe.requirements.eraseIdxIfInBounds removeIndex)
    | some input => do
      let condition ← input.condition recipe.requirements
      let selected := input.references.extract 0 (if input.family == "not" then 1 else 2)
      let old : Array Condition := if ["and", "or", "not"].contains input.family then
        recipe.requirements.zipIdx.filterMap (fun (condition, i) =>
          if selected.contains i then none else some condition) else recipe.requirements
      pure (old.push condition)
  let recipe := { recipe with requirements }
  let _ ← recipe.validate
  state.replay recipe

/-- Exact statuses for the applied samples. Later inherited checks remain
pending until their referenced construction objects have been produced. -/
def WorkspaceState.requirementViews (state : WorkspaceState) (session : Session) :
    Array RequirementView × Array RequirementView := Id.run do
  let recipe := if state.replaying then state.template else none
  let requirements := recipe.map (·.requirements) |>.getD session.requirements
  let checks := recipe.map (·.checks) |>.getD session.checks
  let name (i : Nat) := (state.inputs[i]?.map (·.name)).getD s!"object {i}"
  let status (condition : Condition) (objects : List (Object Scalar)) :=
    if condition.checkObjects objects then "Satisfied" else "Not satisfied"
  return (requirements.map (fun condition =>
    ⟨conditionDescription name condition, status condition session.seeds⟩),
    checks.map (fun check => ⟨conditionDescription name check.condition,
      if check.before > session.program.length then "Not reached" else status check.condition session.objects⟩))

/-- Apply rational replacements, preserving untouched exact inputs. Parameter
identity is fixed after setup; arbitrary samples never become proof seeds. -/
def WorkspaceState.applySamples (state : WorkspaceState) (session : Session)
    (name : String) (inputs : Array SampleInput) (output : Nat) : Except String (WorkspaceState × Session) := do
  if state.ready then
    unless inputs.map (fun p => (p.name, p.kind)) == state.inputs.map (fun p => (p.name, p.kind)) do
      throw "Keep the existing input names, kinds, and order when previewing a recipe."
  if inputs.any (fun p => p.name.trimAscii.toString.isEmpty) then
    throw "Give each input a nonblank name."
  let parameters := inputs.map fun p => RecipeParameter.mk p.name p.kind
  let _ ← RecipeTemplate.validate { parameters }
  let mut samples : RecipeSamples := []
  let mut edits := if state.ready then state.edits else Array.replicate inputs.size none
  let mut entries : Array String := #[]
  for i in [:inputs.size] do
    let some input := inputs[i]? | throw "Missing sample input."
    if input.keep then
      let some original := state.samples[i]? | throw "Place each new sample or enter all of its coordinates."
      samples := samples ++ [original]
    else
      let (value, source) ← input.replacement.mapError fun message => s!"Input {i} ({input.name}): {message}"
      samples := samples ++ [(input.name, value)]
      let entry := sampleEntry input.name source
      entries := entries.push entry
      edits := edits.set! i (some entry)
  let acceptedInputs := inputs.map fun p => { p with keep := true }
  if !state.ready then
    let state : WorkspaceState := {
      name, ready := true, samples, inputs := acceptedInputs
      initialSamples := samples, initialInputs := acceptedInputs
      initialSource := "[" ++ String.intercalate ", " entries.toList ++ "]"
      edits := Array.replicate inputs.size none }
    return (state, { seeds := samples.map Prod.snd, objects := samples.map Prod.snd })
  let recipe ← state.record session output
  WorkspaceState.replay { state with name, samples, inputs := acceptedInputs, edits } recipe

/-- Restore saved (or initial draft) samples without discarding the instructions. -/
def WorkspaceState.resetSamples (state : WorkspaceState) (session : Session) (output : Nat) :
    Except String (WorkspaceState × Session) := do
  let recipe ← state.record session output
  WorkspaceState.replay { state with
    samples := state.initialSamples, inputs := state.initialInputs
    edits := Array.replicate state.inputs.size none } recipe

/-- Replace only changed entries in the original exact sample expression. -/
def WorkspaceState.sampleSource (state : WorkspaceState) : String := Id.run do
  let mut source := "(" ++ state.initialSource ++ " : LeanOrigami.Widget.RecipeSamples)"
  for i in [:state.edits.size] do
    if let some entry := state.edits[i]! then source := "(" ++ source ++ s!").set {i} ({entry})"
  return source

/-- Require one ordinary declaration identifier and reject existing names.
The current saved declaration may keep its own name. -/
def validateRecipeName (workspace : WorkspaceContext) (text : String) : MetaM String := do
  let name := text.trimAscii.toString
  let parsed ← match Parser.runParserCategory (← getEnv) `term name with
    | .ok parsed => pure parsed
    | .error _ => throwError "Enter a Lean declaration name, such as myMidpoint."
  unless parsed.isIdent && (parsed.getId.isAtomic || name == workspace.name) do
    throwError "Use a single Lean identifier for the recipe name."
  unless workspace.name.isEmpty || name == workspace.name do
    throwError "Keep this declaration's name; start a new workspace to create another recipe."
  if name != workspace.name && (← getEnv).contains (workspace.namespaceName ++ parsed.getId) then
    throwError "A declaration named {name} already exists."
  return name

/-- Open a setup draft or recompute a saved recipe, retaining failed prefixes. -/
def openWorkspace (workspace : WorkspaceContext) : MetaM (Except String (WorkspaceState × Session)) := do
  if workspace.draft then
    return .ok ({ name := "" }, { seeds := [], objects := [] })
  let samples ← readSamples workspace.samples
  let recipe ← readRecipe workspace.recipe
  return do
    unless recipe.parameters.map (fun p => (p.name, p.kind)) ==
        workspace.parameters.map (fun p => (p.name, p.kind)) do
      throw "The saved recipe parameters do not match the sample inputs."
    let inputs := workspace.parameters.map fun p => SampleInput.mk p.name p.kind #[] true
    WorkspaceState.replay {
      name := workspace.name, ready := true, samples, initialSamples := samples
      inputs, initialInputs := inputs, initialSource := workspace.sampleSource
      edits := Array.replicate inputs.size none } recipe

end LeanOrigami.Widget
