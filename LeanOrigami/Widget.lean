import LeanOrigami.Widget.Saved
import LeanOrigami.Widget.Goal
import ProofWidgets.Component.Panel.Basic
import ProofWidgets.Component.MakeEditLink

/-!
# Goal-directed origami construction panel

`origami` starts an editor; `origami saved (...)` also proves its goal and
restores the saved construction when reopened. Immutable RPC snapshots
carry exact programs; the browser receives only references and approximations.
Submission elaborates and kernel-checks a persistent proof against the captured
goal before returning a versioned edit. The widget is not a proof oracle.
-/

namespace LeanOrigami.Widget
open Lean Meta Elab Tactic Server ProofWidgets

meta section

/-- The proof context and source location that opened this panel. -/
structure GoalContext where
  id : Name
  context : ContextInfo
  locals : LocalContext
  goal : Expr
  range : Lsp.Range
  saved : Option Expr := none
  deriving TypeName

/-- A session is valid only for its original goal and source version. -/
structure Snapshot where
  gate : Name
  document : DocumentMeta
  session : Session
  deriving TypeName

/-- Browser properties contain an opaque context reference, never proof evidence. -/
structure PanelProps where
  gate : WithRpcRef GoalContext
  target : String
  saved : Bool := false
  deriving RpcEncodable

/-- Every request refers to the exact preview snapshot it operates on. -/
structure Interaction where
  gate : WithRpcRef GoalContext
  session : Option (WithRpcRef Snapshot) := none
  action : String
  operation : String := "1"
  inputs : Array Nat := #[]
  choice : Nat := 0
  point : Nat := 1
  coordinate : String := "x"
  bits : Nat := 48
  deriving RpcEncodable

/-- A new immutable snapshot, with an optional already checked source edit. -/
structure Response where
  session : WithRpcRef Snapshot
  view : View
  edit : Option Lsp.TextDocumentEdit := none
  source : String := ""
  point : Nat := 1
  coordinate : String := "x"
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

private def submission (gate : GoalContext) (session : Session) (point : Nat)
    (coordinate : Coordinate) : RequestM String := do
  let target ← result (session.selected point coordinate)
  let kind ← try
      gate.context.runMetaM gate.locals (classifyTarget gate.goal.appArg!)
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
      (checkProof gate.goal s!"LeanOrigami.Widget.SavedConstruction.sound ({saved})")
  catch error => throw (.invalidParams s!"This coordinate could not close the goal. {error.message}")
  return saved

/-- Compute a view or operation without mutating any earlier session. -/
@[server_rpc_method]
def interact (request : Interaction) : RequestM (RequestTask Response) := RequestM.asTask do
  let document := (← RequestM.readDoc).meta
  let gate := request.gate.val
  unless document.text.source == gate.context.fileMap.source do
    throw (.invalidParams "The source changed. Reopen the construction at the current goal.")
  let mut point := request.point
  let mut coordinate := request.coordinate
  let snapshot ← match request.session with
    | none =>
      unless request.action == "start" do throw (.invalidParams "Open a construction first.")
      let mut session : Session := {}
      if let some saved := gate.saved then
        let restored ← try
            gate.context.runMetaM gate.locals (reopen saved)
          catch error => throw (.invalidParams s!"Could not reopen this construction: {error.message}")
        let (loaded, selected, axis) ← result restored
        session := loaded
        point := selected
        coordinate := match axis with | .x => "x" | .y => "y"
      pure { gate := gate.id, document, session }
    | some reference =>
      let saved := reference.val
      unless saved.gate == gate.id && saved.document.uri == document.uri &&
          saved.document.version == document.version do
        throw (.invalidParams "This construction belongs to an earlier goal or source version.")
      pure saved
  let mut session := snapshot.session
  let mut source := ""
  let mut edit := none
  match request.action with
  | "start" | "render" => pure ()
  | "preview" =>
    let some number := request.operation.toNat? | throw (.invalidParams "Unknown fold operation.")
    let fold ← result (foldRequest number request.inputs.toList)
    session ← result (session.preview fold)
  | "choose" => session ← result (session.choose request.choice)
  | "intersect" =>
    let [left, right] := request.inputs.toList
      | throw (.invalidParams "Select two lines to intersect.")
    session ← result (session.intersect left right)
  | "undo" => session ← result session.undo
  | "submit" =>
    let axis ← match request.coordinate with
      | "x" => pure Coordinate.x
      | "y" => pure Coordinate.y
      | _ => throw (.invalidParams "Choose the x or y coordinate.")
    source ← submission gate session request.point axis
    let indent := String.ofList (List.replicate gate.range.start.character ' ')
    let replacement := "origami saved (" ++ source.replace "\n" ("\n" ++ indent) ++ ")"
    edit := some (MakeEditLinkProps.ofReplaceRange document gate.range replacement).edit
  | _ => throw (.invalidParams "Unknown construction action.")
  return { session := ← WithRpcRef.mk { snapshot with session }
           view := session.view request.bits, edit, source, point, coordinate }

/-- Interactive SVG panel; JavaScript is source-controlled and needs no bundler. -/
@[widget_module]
def ConstructionPanel : Component PanelProps where
  javascript := include_str ".." / "widget" / "construction.js"

/-- Open an unfinished construction, or check and display a saved one. The
panel is attached to the tactic even when its certificate closes the goal. -/
syntax (name := origamiPanel) "origami" (ppSpace &"saved" ppSpace term)? : tactic

@[tactic origamiPanel]
def elabOrigami : Tactic
  | stx@`(tactic| origami $[saved $source:term]?) => withMainContext do
    let goal ← instantiateMVars (← getMainTarget)
    unless goal.isAppOfArity ``ConstructibleNumber 1 do
      throwError "origami requires a ConstructibleNumber goal."
    let some range := (← getFileMap).lspRangeOfStx? stx
      | throwError "origami needs an editable source location."
    let saved ← source.mapM fun source => do
      let value ← Term.elabTermEnsuringType source (mkApp (mkConst ``SavedConstruction) goal.appArg!)
      Term.synthesizeSyntheticMVarsNoPostponing
      let value ← instantiateMVars value
      if value.hasMVar || value.hasSorry then
        throwError "The saved construction has incomplete certificates."
      return value
    let gate : GoalContext := {
      id := ← mkFreshId
      context := { ← CommandContextInfo.save with }
      locals := ← getLCtx
      goal, range, saved }
    let props : PanelProps := {
      gate := ← WithRpcRef.mk gate
      target := (← ppExpr goal.appArg!).pretty
      saved := saved.isSome }
    Lean.Widget.savePanelWidgetInfo ConstructionPanel.javascriptHash (rpcEncode props) stx
    if let some saved := saved then
      let proof ← mkAppM ``SavedConstruction.sound #[saved]
      (← getMainGoal).assign proof
      replaceMainGoal []
  | _ => throwUnsupportedSyntax

-- Bare `origami` intentionally leaves the proof state unchanged.
#allow_unused_tactic! origamiPanel

end
end LeanOrigami.Widget
