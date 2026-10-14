import LeanOrigami.Widget.Saved
import LeanOrigami.Widget.Goal
import LeanOrigami.Widget.Workspace
import ProofWidgets.Component.Panel.Basic
import ProofWidgets.Component.MakeEditLink

/-!
# Proof and recipe construction panels

`origami` starts an editor; `origami saved (...)` also proves its goal and
restores the saved construction when reopened. Immutable RPC snapshots
carry exact programs; the browser receives only references and approximations.
Submission elaborates and kernel-checks a persistent proof against the captured
goal before returning a versioned edit. The widget is not a proof oracle.
`origami_recipe` uses the same panel outside proofs, saving parameterized
operations whose exact results are discovered again for each invocation.
Declared requirements are edited and checked through the shared workspace API.
-/

namespace LeanOrigami.Widget
open Lean Meta Elab Tactic Server ProofWidgets

meta section

/-- The source context of either a proof editor or a standalone recipe editor. -/
structure PanelContext where
  id : Name
  context : ContextInfo
  locals : LocalContext
  goal : Option Expr := none
  range : Lsp.Range
  saved : Option Expr := none
  workspace : Option WorkspaceContext := none
  library : Array NamedRecipe := #[]
  groups : Array RecipeGroup := #[]
  deriving TypeName

/-- A session is valid only for its original editor and source version. -/
structure Snapshot where
  gate : Name
  document : DocumentMeta
  session : Session
  workspace : Option WorkspaceState := none
  deriving TypeName

/-- Browser properties contain an opaque context reference, never proof evidence. -/
structure PanelProps where
  gate : WithRpcRef PanelContext
  target : String
  saved : Bool := false
  workspace : Bool := false
  recipes : Array RecipeMenuItem := #[]
  parameters : Array RecipeParameter := #[]
  deriving RpcEncodable

/-- Every request refers to the exact preview snapshot it operates on. The
browser sends every field, including defaults required by RPC decoding. -/
structure Interaction where
  gate : WithRpcRef PanelContext
  session : Option (WithRpcRef Snapshot) := none
  action : String
  operation : String := "1"
  inputs : Array Nat := #[]
  choice : Nat := 0
  point : Nat := 1
  coordinate : String := "x"
  bits : Nat := 48
  recipeName : String := ""
  outputName : String := ""
  sampleInputs : Array SampleInput := #[]
  requirement : RequirementInput := {}
  deriving RpcEncodable

/-- A new immutable snapshot, with an optional already checked source edit. -/
structure Response where
  session : WithRpcRef Snapshot
  view : View
  edit : Option Lsp.TextDocumentEdit := none
  source : String := ""
  point : Nat := 1
  coordinate : String := "x"
  workspace : Option WorkspaceView := none
  deriving RpcEncodable

private def result {α : Type} (value : Except String α) : RequestM α :=
  match value with
  | .ok value => pure value
  | .error message => throw (.invalidParams message)

/-- Check a proposed ordinary Lean expression, including its transitive axioms.
The auxiliary theorem is created only in the captured, disposable environment. -/
def checkProof (goal : Expr) (source : String) : MetaM Unit := do
  -- An editor snapshot can retain an asynchronous theorem environment while
  -- losing its auxiliary-name generator. Kernel checks such as `decide +kernel`
  -- must create their temporary declarations under that theorem's prefix.
  let declPrefix := (← getEnv).asyncPrefix?.getD (← getDeclNGen).namePrefix
  withDeclNameForAuxNaming declPrefix do
    let parsed ← match Parser.runParserCategory (← getEnv) `term source with
      | .ok parsed => pure parsed
      | .error message => throwError "Could not parse the exported proof: {message}"
    let messagesBefore ← Core.getMessageLog
    let value ← Term.TermElabM.run' <| Term.withoutErrToSorry do
      let value ← Term.elabTermEnsuringType parsed goal
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars value
    if value.hasMVar || value.hasSorry then
      let errors := (← Core.getMessageLog).toList.drop messagesBefore.toList.length
        |>.filter (·.severity == .error)
      let details ← errors.mapM fun message => message.data.toString
      throwError "The exported proof is incomplete.\n{String.intercalate "\n" details}"
    if (← getEnv).hasUnsafe value then throwError "The exported proof contains unsafe constants."
    let checked ← mkAuxTheorem goal value (cache := false)
    let dependencies ← collectAxioms checked.getAppFn.constName!
    for dependency in dependencies do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "The exported proof depends on unsupported axiom {dependency}."

private def submission (gate : PanelContext) (session : Session) (point : Nat)
    (coordinate : Coordinate) : RequestM String := do
  let some goal := gate.goal | throw (.invalidParams "This workspace has no proof goal.")
  let target ← result (session.selected point coordinate)
  let kind ← try
      gate.context.runMetaM gate.locals (classifyTarget goal.appArg!)
    catch _ => throw (.invalidParams
      "Submission supports rational goals, Real.sqrt q, and q ^ (1 / 3), with nonnegative rational q for roots.")
  -- This fast feedback is untrusted. The identity is proved again below.
  let matchesTarget := match kind with
    | .rational q => decide (target = (q : Scalar))
    | .squareRoot q => decide (target ^ 2 = (q : Scalar) ∧ 0 ≤ target)
    | .cubeRoot q => decide (target ^ 3 = (q : Scalar))
  unless matchesTarget do throw (.invalidParams
    "The selected coordinate does not equal the goal. Check the point, x/y coordinate, and root branch.")
  let certificate ← result (← Text.prepareExact session.program ⟨point⟩ coordinate target)
  let saved := savedSource certificate point coordinate
  try
    gate.context.runMetaM gate.locals
      (checkProof goal s!"LeanOrigami.Widget.SavedConstruction.sound ({saved})")
  catch error => throw (.invalidParams s!"This coordinate could not close the goal. {error.message}")
  return saved

/-- Compute a view or operation without mutating any earlier session. -/
@[server_rpc_method]
def interact (request : Interaction) : RequestM (RequestTask Response) := RequestM.asTask do
  let document := (← RequestM.readDoc).meta
  let gate := request.gate.val
  unless document.text.source == gate.context.fileMap.source do
    throw (.invalidParams "The source changed. Reopen the construction at its current source location.")
  let mut point := request.point
  let mut coordinate := request.coordinate
  let snapshot : Snapshot ← match request.session with
    | none =>
      unless request.action == "start" do throw (.invalidParams "Open a construction first.")
      let mut session : Session := {}
      let mut workspaceState : Option WorkspaceState := none
      if let some workspace := gate.workspace then
        let (state, loaded) ← result (← gate.context.runMetaM gate.locals (openWorkspace workspace))
        workspaceState := some state
        session := loaded
        point := session.result.getD 0
      else if let some saved := gate.saved then
        let restored ← try
            gate.context.runMetaM gate.locals (reopen saved)
          catch error => throw (.invalidParams s!"Could not reopen this construction: {error.message}")
        let (loaded, selected, axis) ← result restored
        session := { loaded with groups := gate.groups }
        point := selected
        coordinate := match axis with | .x => "x" | .y => "y"
      pure { gate := gate.id, document, session, workspace := workspaceState }
    | some reference =>
      let saved := reference.val
      unless saved.gate == gate.id && saved.document.uri == document.uri &&
          saved.document.version == document.version do
        throw (.invalidParams "This construction belongs to an earlier editor or source version.")
      pure saved
  let mut session := snapshot.session
  let mut workspaceState : Option WorkspaceState := snapshot.workspace
  let mut source := ""
  let mut edit := none
  if workspaceState.any (fun state => !state.ready) &&
      !(["start", "render", "samples"].contains request.action) then
    throw (.invalidParams "Name the recipe and set up its inputs first.")
  if session.running.isSome && !(["start", "render", "choose", "undo", "samples", "resetSamples", "addRequirement", "removeRequirement"].contains request.action) then
    throw (.invalidParams "Finish or cancel the current recipe first.")
  match request.action with
  | "start" | "render" => pure ()
  | "preview" =>
    let some number := request.operation.toNat? | throw (.invalidParams "Unknown fold operation.")
    let fold ← result (foldRequest number request.inputs.toList)
    session ← result (session.preview fold)
  | "choose" => session ← result (session.choose request.choice
      (retainFailure := workspaceState.any (·.replaying)))
  | "intersect" =>
    let [left, right] := request.inputs.toList
      | throw (.invalidParams "Select two lines to intersect.")
    session ← result (session.intersect left right)
  | "recipe" =>
    let some recipe := gate.library.find? (·.id == request.operation)
      | throw (.invalidParams "This recipe is not available in the current context.")
    session ← result (session.useRecipe recipe.name recipe.template request.inputs)
  | "samples" =>
    let some workspace := gate.workspace | throw (.invalidParams "Samples can only be edited outside a proof.")
    let some state := workspaceState | throw (.invalidParams "Open a recipe workspace first.")
    let name ← try gate.context.runMetaM gate.locals (validateRecipeName workspace request.recipeName)
      catch error => throw (.invalidParams error.message)
    let (state, changed) ← result (state.applySamples session name request.sampleInputs request.point)
    workspaceState := some state
    session := changed
    point := session.result.getD 0
  | "resetSamples" =>
    let some state := workspaceState | throw (.invalidParams "Open a recipe workspace first.")
    let (state, changed) ← result (state.resetSamples session request.point)
    workspaceState := some state
    session := changed
    point := session.result.getD 0
  | "addRequirement" | "removeRequirement" =>
    let some state := workspaceState | throw (.invalidParams "Requirements can only be edited in a recipe workspace.")
    let input := if request.action == "addRequirement" then some request.requirement else none
    let (state, changed) ← result (state.editRequirement session request.point input request.choice)
    workspaceState := some state
    session := changed
    point := session.result.getD 0
  | "nameOutput" | "removeOutput" =>
    unless workspaceState.isSome do throw (.invalidParams "Name outputs in a recipe workspace.")
    if request.action == "nameOutput" then
      session ← result (session.nameOutput request.outputName request.point)
    else
      unless request.choice < session.outputs.size do throw (.invalidParams "This output name no longer exists.")
      session := { session with outputs := session.outputs.eraseIdxIfInBounds request.choice }
  | "undo" =>
    if workspaceState.any (·.replaying) then
      throw (.invalidParams "Edit or reset samples to recover the retained recipe.")
    session ← result session.undo
  | "submit" =>
    let replacement ← match gate.workspace with
      | some workspace => do
        let some state := workspaceState | throw (.invalidParams "Set up the recipe first.")
        if state.replaying then throw (.invalidParams "Complete the preview before saving the recipe.")
        let name ← try gate.context.runMetaM gate.locals (validateRecipeName workspace state.name)
          catch error => throw (.invalidParams error.message)
        let recipe ← result (session.template (state.inputs.map fun p => ⟨p.name, p.kind⟩) request.point)
        source := recipe.source
        pure ("origami_recipe " ++ name ++ " samples (" ++ state.sampleSource ++ ") saved (" ++ source ++ ")")
      | none => do
        let axis ← match request.coordinate with
          | "x" => pure Coordinate.x
          | "y" => pure Coordinate.y
          | _ => throw (.invalidParams "Choose the x or y coordinate.")
        source ← submission gate session request.point axis
        let history := if session.groups.isEmpty then "" else
          "history (#[" ++ String.intercalate ", " (session.groups.toList.map RecipeGroup.source) ++ "]) "
        pure ("origami " ++ history ++ "saved (" ++ source ++ ")")
    let indent := String.ofList (List.replicate gate.range.start.character ' ')
    let replacement := replacement.replace "\n" ("\n" ++ indent)
    edit := some (MakeEditLinkProps.ofReplaceRange document gate.range replacement).edit
  | _ => throw (.invalidParams "Unknown construction action.")
  workspaceState := workspaceState.map fun state =>
    { state with replaying := state.replaying && session.running.isSome }
  let workspaceView : Option WorkspaceView := workspaceState.map fun (state : WorkspaceState) =>
    let (requirements, nestedRequirements) := state.requirementViews session
    let currentRecipe := (state.record session point).toOption
    { name := state.name, ready := state.ready
      nameLocked := gate.workspace.any (fun w => !w.name.isEmpty)
      inputs := state.inputs, replaying := state.replaying, requirements, nestedRequirements
      specification := currentRecipe.bind arithmeticSpecification
      specificationOutput := currentRecipe.map (·.output) |>.getD 0 }
  return { session := ← WithRpcRef.mk { snapshot with session, workspace := workspaceState }
           view := session.view request.bits, edit, source, point, coordinate, workspace := workspaceView }

/-- Interactive SVG panel; JavaScript is source-controlled and needs no bundler. -/
@[widget_module]
def ConstructionPanel : ProofWidgets.Component PanelProps where
  javascript := include_str ".." / "widget" / "construction.js"

/-- Attach the same panel to a tactic or a declaration command. -/
private def registerPanel (stx : Syntax) (target : String) (goal saved : Option Expr)
    (workspace : Option WorkspaceContext) (groups : Array RecipeGroup := #[])
    (savedRecipe : Bool := false) : Term.TermElabM Unit := do
  let some range := (← getFileMap).lspRangeOfStx? stx
    | throwError "origami needs an editable source location."
  let library ← recipeLibrary
  let gate : PanelContext := {
    id := ← mkFreshId
    context := { ← CommandContextInfo.save with }
    locals := ← getLCtx
    goal, range, saved, workspace, library, groups }
  let props : PanelProps := {
    gate := ← WithRpcRef.mk gate
    target, saved := saved.isSome || savedRecipe
    workspace := workspace.isSome
    parameters := workspace.map (·.parameters) |>.getD #[]
    recipes := library.map fun r => ⟨r.id, r.name, r.template.parameters,
      r.template.requirements.map (conditionDescription (fun i =>
        (r.template.parameters[i]?.map (·.name)).getD s!"object {i}")),
      arithmeticSpecification r.template⟩ }
  Lean.Widget.savePanelWidgetInfo ConstructionPanel.javascriptHash (rpcEncode props) stx

/-- Open or prove a saved construction. History annotations are presentation
metadata; the certificate still checks only the expanded exact program. -/
syntax (name := origamiPanel) "origami" (ppSpace &"history" ppSpace "(" term ")")?
  (ppSpace &"saved" ppSpace term)? : tactic

@[tactic origamiPanel]
def elabOrigami : Tactic
  | stx@`(tactic| origami $[history ($annotations:term)]? $[saved $source:term]?) => withMainContext do
    let goal ← instantiateMVars (← getMainTarget)
    unless goal.isAppOfArity ``ConstructibleNumber 1 do
      throwError "origami requires a ConstructibleNumber goal."
    let saved ← source.mapM fun source => do
      let value ← Term.elabTermEnsuringType source (mkApp (mkConst ``SavedConstruction) goal.appArg!)
      Term.synthesizeSyntheticMVarsNoPostponing
      let value ← instantiateMVars value
      if value.hasMVar || value.hasSorry then
        throwError "The saved construction has incomplete certificates."
      return value
    let groups ← match annotations with
      | none => pure #[]
      | some annotations => do
        let value ← Term.elabTermEnsuringType annotations
          (mkApp (mkConst ``Array [0]) (mkConst ``RecipeGroup))
        Term.synthesizeSyntheticMVarsNoPostponing
        readGroups (← instantiateMVars value)
    registerPanel stx (← ppExpr goal.appArg!).pretty (some goal) saved none groups
    if let some saved := saved then
      let proof ← mkAppM ``SavedConstruction.sound #[saved]
      (← getMainGoal).assign proof
      replaceMainGoal []
  | _ => throwUnsupportedSyntax

-- Bare `origami` intentionally leaves the proof state unchanged.
#allow_unused_tactic! origamiPanel

/-- Define and visually edit a recipe without a theorem. Sample objects are
parameters; only a saved template is registered as an available operation. -/
syntax (name := origamiRecipeCommand) "origami_recipe"
  (ppSpace ident ppSpace &"samples" ppSpace "(" term ")"
    (ppSpace &"saved" ppSpace term)?)? : command

@[command_elab origamiRecipeCommand]
def elabRecipeCommand : Command.CommandElab
  | stx@`(origami_recipe) => do
    let namespaceName ← getCurrNamespace
    Command.runTermElabM fun _ => do
      let samples ← Term.elabTerm (← `(([] : LeanOrigami.Widget.RecipeSamples))) none
      let recipe ← Term.elabTerm (← `(({ parameters := #[] } : LeanOrigami.Widget.RecipeTemplate))) none
      let workspace : WorkspaceContext := {
        name := "", namespaceName, sampleSource := "[]", draft := true
        samples, recipe, parameters := #[] }
      registerPanel stx "New recipe" none none (some workspace)
  | stx@`(origami_recipe $name:ident samples ($sampleTerm:term) $[saved $source:term]?) => do
    let namespaceName ← getCurrNamespace
    let (sampleExpr, parameters) ← Command.runTermElabM fun _ => do
      let sampleExpr ← Term.elabTermEnsuringType sampleTerm (mkConst ``RecipeSamples)
      Term.synthesizeSyntheticMVarsNoPostponing
      let sampleExpr ← instantiateMVars sampleExpr
      let values ← readSamples sampleExpr
      let parameters := values.toArray.map fun (name, value) =>
        RecipeParameter.mk name (objectKind value)
      let draft : RecipeTemplate := { parameters }
      match draft.validate with
      | .error message => throwError "{message}"
      | .ok _ => pure ()
      return (sampleExpr, parameters)
    let body ← match source with
      | some source => pure source
      | none =>
        let draft : RecipeTemplate := { parameters }
        match Parser.runParserCategory (← getEnv) `term draft.source with
        | .ok body => pure ⟨body⟩
        | .error message => throwError "{message}"
    Command.elabCommand (← `(def $name : LeanOrigami.Widget.RecipeTemplate := $body))
    if source.isSome then Command.elabCommand (← `(attribute [«origami_recipe»] $name))
    Command.runTermElabM fun _ => do
      let recipe ← Term.elabTerm name (some (mkConst ``RecipeTemplate))
      let workspace : WorkspaceContext := {
        name := (name.raw.reprint.getD name.getId.toString).trimAscii.toString
        namespaceName, sampleSource := sampleTerm.raw.reprint.getD ""
        samples := sampleExpr, recipe, parameters }
      registerPanel stx name.getId.toString none none (some workspace) #[] source.isSome
  | _ => throwUnsupportedSyntax

end
end LeanOrigami.Widget
