import LeanOrigami.Widget.Session
import LeanOrigami.Widget.Goal
import ProofWidgets.Component.Panel.Basic
import ProofWidgets.Component.MakeEditLink

/-!
# Goal-directed origami construction panel

`origami` displays the editor without solving its goal. Immutable RPC snapshots
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
  proof : String := ""
  deriving RpcEncodable

private def result {α : Type} (value : Except String α) : RequestM α :=
  match value with
  | .ok value => pure value
  | .error message => throw (.invalidParams message)

/-- Check a proposed ordinary Lean expression, including its transitive axioms.
The auxiliary theorem is created only in the captured, disposable environment. -/
def checkProof (goal : Expr) (source : String) : MetaM Unit := do
  let parsed ← match Parser.runParserCategory (← getEnv) `term source with
    | .ok parsed => pure parsed
    | .error message => throwError "Could not parse the exported proof: {message}"
  let value ← Term.TermElabM.run' do
    let value ← Term.elabTermEnsuringType parsed goal
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars value
  if value.hasMVar || value.hasSorry then throwError "The exported proof is incomplete."
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
  let finish := "refine LeanOrigami.Widget.submit target constructed ?_\n" ++
    s!"origami_identify target using {certificate.arithmetic}"
  let proof := certificate.proof finish
  try
    gate.context.runMetaM gate.locals (checkProof gate.goal proof)
  catch error => throw (.invalidParams s!"This coordinate could not close the goal. {error.message}")
  return proof

/-- Compute a view or operation without mutating any earlier session. -/
@[server_rpc_method]
def interact (request : Interaction) : RequestM (RequestTask Response) := RequestM.asTask do
  let document := (← RequestM.readDoc).meta
  let gate := request.gate.val
  unless document.text.source == gate.context.fileMap.source do
    throw (.invalidParams "The source changed. Reopen the construction at the current goal.")
  let snapshot ← match request.session with
    | none =>
      unless request.action == "start" do throw (.invalidParams "Open a construction first.")
      pure { gate := gate.id, document, session := {} }
    | some reference =>
      let saved := reference.val
      unless saved.gate == gate.id && saved.document.uri == document.uri &&
          saved.document.version == document.version do
        throw (.invalidParams "This construction belongs to an earlier goal or source version.")
      pure saved
  let mut session := snapshot.session
  let mut proof := ""
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
    let coordinate ← match request.coordinate with
      | "x" => pure Coordinate.x
      | "y" => pure Coordinate.y
      | _ => throw (.invalidParams "Choose the x or y coordinate.")
    proof ← submission gate session request.point coordinate
    let indent := String.ofList (List.replicate gate.range.start.character ' ')
    let replacement := "exact (" ++ proof.replace "\n" ("\n" ++ indent) ++ ")"
    edit := some (MakeEditLinkProps.ofReplaceRange document gate.range replacement).edit
  | _ => throw (.invalidParams "Unknown construction action.")
  return { session := ← WithRpcRef.mk { snapshot with session }
           view := session.view request.bits, edit, proof }

/-- Interactive SVG panel; JavaScript is source-controlled and needs no bundler. -/
@[widget_module]
def ConstructionPanel : Component PanelProps where
  javascript := include_str ".." / "widget" / "construction.js"

/-- Open a visual construction for the current goal. It stays open until a
checked persistent proof is inserted; exploration itself never proves a goal. -/
elab (name := origamiPanel) stx:"origami" : tactic => withMainContext do
  let goal ← instantiateMVars (← getMainTarget)
  unless goal.isAppOfArity ``ConstructibleNumber 1 do
    throwError "origami requires a ConstructibleNumber goal."
  let some range := (← getFileMap).lspRangeOfStx? stx
    | throwError "origami needs an editable source location."
  let gate : GoalContext := {
    id := ← mkFreshId
    context := { ← CommandContextInfo.save with }
    locals := ← getLCtx
    goal, range }
  let props : PanelProps := {
    gate := ← WithRpcRef.mk gate
    target := (← ppExpr goal.appArg!).pretty }
  Lean.Widget.savePanelWidgetInfo ConstructionPanel.javascriptHash (rpcEncode props) stx

-- Opening a panel intentionally leaves the proof state unchanged.
#allow_unused_tactic! origamiPanel

end
end LeanOrigami.Widget
