import ProofWidgets.Component.MakeEditLink
import ProofWidgets.Component.OfRpcMethod
import ProofWidgets.Component.Panel.Basic

/-!
# Phase 0 submission prototype

Place the cursor on `origami_phase0` in the example below. The panel offers
a link replacing that tactic with the persistent proof `rfl`. The tactic
already verifies `rfl` before offering it; the widget is not a proof oracle.
This probes the editor boundary only, not origami geometry.
-/

open Lean Server ProofWidgets

namespace LeanOrigamiDemos

meta section

/-- The source location to replace, in addition to the standard panel context. -/
structure SubmissionProps extends PanelWidgetProps where
  replaceRange : Lsp.Range
  deriving RpcEncodable

/-- A versioned edit shared by the live panel and the interaction harness. -/
def submissionEdit (doc : DocumentMeta) (range : Lsp.Range) : MakeEditLinkProps :=
  .ofReplaceRange doc range "rfl"

/-- Produce the insertion link using the current document's version. -/
@[server_rpc_method]
def submissionRpc (props : SubmissionProps) : RequestM (RequestTask Html) :=
  RequestM.asTask do
    let doc ← RequestM.readDoc
    return .ofComponent MakeEditLink (submissionEdit doc.meta props.replaceRange)
      #[.text "Insert checked proof: rfl"]

/-- A minimal interactive panel using ProofWidgets' released RPC component. -/
@[widget_module]
def SubmissionPanel : Component SubmissionProps := mk_rpc_widget% submissionRpc

open Lean Elab Tactic in
open scoped Json in
elab stx:"origami_phase0" : tactic => do
  let some range := (← getFileMap).lspRangeOfStx? stx
    | throwError "submission prototype requires a source location"
  evalTactic (← `(tactic| rfl))
  Widget.savePanelWidgetInfo SubmissionPanel.javascriptHash
    (pure <| json% { replaceRange: $(range) }) stx

end

/-- Clicking the panel replaces the tactic with an ordinary persistent proof. -/
theorem submission_example : (1 : Nat) + 1 = 2 := by
  origami_phase0

#print axioms submission_example

end LeanOrigamiDemos
