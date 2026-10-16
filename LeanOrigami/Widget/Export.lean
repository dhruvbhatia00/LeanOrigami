import LeanOrigami.Widget.Saved
import LeanOrigami.Widget.LibraryCertificate

/-!
# Exporting compositional visual proofs

Native execution records exact arithmetic and proposes a certificate. Its source
contains the same scoped call tree as the editor. Library calls need only
public equations and branch witnesses; fallback bodies retain recursively checked
primitive choices. The ordinary Lean elaborator and kernel must check the returned source.
-/

namespace LeanOrigami.Widget
open Text

private def values : Object Scalar → List Scalar
  | .point point => [point.1, point.2]
  | .line line => [line.a, line.b, line.c]

private def get {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error message => throw (IO.userError message)

-- Record only arithmetic actually used by the certificate. A proved call does
-- not discover, record, or serialize its auxiliary geometry.
private partial def recordHistory (log : IO.Ref ArithmeticLog) (initial : Program.State Scalar)
    (history : Execution.History Scalar) : IO (Program.State Scalar × List (List Scalar) × List (LibraryRecipe × LibraryRecipe.Discovery Scalar)) := do
  let mut state := initial
  let mut blocks := [initial.flatMap values]
  let mut prepared := []
  for step in history do
    match step with
    | .primitive instruction =>
      let next ← ArithmeticLog.step log state instruction
      let inputs ← match instruction with
        | .fold request _ => do
          let input ← get ((Program.resolve state request).mapError errorMessage)
          pure input.objects
        | .intersect left right _ => do
          let first ← get ((Program.line state left).mapError errorMessage)
          let second ← get ((Program.line state right).mapError errorMessage)
          pure [Object.line first, Object.line second]
      blocks := (inputs.flatMap values ++ (Execution.Step.outputs step).flatMap values) :: blocks
      state := next
    | .library _ recipe arguments outputs =>
      let some known := LibraryRecipe.recognize recipe
        | throw (IO.userError "A compact call must match a proved library definition.")
      let inputs ← get ((Composition.select state arguments.toList).mapError errorMessage)
      let found ← known.record log inputs
      unless found.outputs = outputs do throw (IO.userError "Recipe public outputs changed.")
      blocks := (inputs.flatMap values ++ outputs.flatMap values ++
        found.witnesses ++ found.signs) :: blocks
      prepared := prepared ++ [(known, found)]
      state := state ++ outputs
    | .call _ recipe arguments outputs body =>
      let inputs ← get ((Composition.select state arguments.toList).mapError errorMessage)
      let actual ← if Execution.isMidpoint recipe then do
          pure (← LibraryRecipe.record .midpoint log inputs).outputs
        else do
          unless (body.map Execution.Step.operation).map reprStr == recipe.steps.map reprStr do
            throw (IO.userError "Recipe history does not match its saved definition.")
          let (final, innerBlocks, innerPrepared) ← recordHistory log inputs body
          blocks := innerBlocks ++ blocks
          prepared := prepared ++ innerPrepared
          get ((Composition.select final recipe.publicOutputs.toList).mapError errorMessage)
      unless actual = outputs do throw (IO.userError "Recipe public outputs changed.")
      blocks := (inputs.flatMap values ++ outputs.flatMap values) :: blocks
      state := state ++ outputs
  return (state, blocks, prepared)

private def stateSource (table : CoordinateTable) (state : Program.State Scalar) : Except String String := do
  return "[" ++ String.intercalate ", " (← state.mapM table.objectSource) ++ "]"

private partial def historySource (table : CoordinateTable) (history : Execution.History Scalar) :
    Except String String := do
  let steps ← history.mapM fun step => do
    match step with
    | .primitive instruction => return s!"Execution.Step.primitive ({← table.instructionSource instruction})"
    | .library name recipe arguments outputs =>
      return s!"Execution.Step.library {repr name} ({LibraryRecipe.templateSource recipe}) " ++
        s!"({repr arguments}) ({← stateSource table outputs})"
    | .call name recipe arguments outputs body =>
      let template := LibraryRecipe.templateSource recipe
      return s!"Execution.Step.call {repr name} ({template}) ({repr arguments}) " ++
        s!"({← stateSource table outputs}) ({← historySource table body})"
  return "[" ++ String.intercalate ",\n" steps ++ "]"

private def indent (text : String) : String := "  " ++ text.replace "\n" "\n  "

-- Emit one certificate per public node. Only an unregistered call recursively
-- supplies a body certificate; its nested registered calls still reuse theorems.
private partial def proofSource (table : CoordinateTable) (arithmetic : String) (bits : Nat)
    (initial : Program.State Scalar) (history : Execution.History Scalar)
    (prepared : List (LibraryRecipe × LibraryRecipe.Discovery Scalar)) :
    Except String (String × List (LibraryRecipe × LibraryRecipe.Discovery Scalar)) := do
  let mut state := initial
  let mut proofs := []
  let mut remaining := prepared
  for step in history do
    let head ← match step with
      | .primitive instruction => do
        let output ← (Program.step state instruction).mapError errorMessage
        state := state ++ [output]
        pure s!"exact Composition.Checked.primitive _ _ (by origami_step using {arithmetic})"
      | .library _ recipe arguments outputs => do
        let some known := LibraryRecipe.recognize recipe
          | throw "The compact recipe definition changed."
        let (identity, found) :: rest := remaining | throw "Missing prepared library witnesses."
        unless identity = known do throw "Prepared library witnesses are out of order."
        remaining := rest
        let inputs ← (Composition.select state arguments.toList).mapError errorMessage
        let inputSource ← stateSource table inputs
        let produces ← known.certificateSource table arithmetic bits inputs found
        state := state ++ outputs
        pure (s!"refine Composition.Checked.call _ _ ({inputSource}) _ _ rfl rfl ?_\n" ++
          s!"refine ⟨({repr known}), rfl, ?_⟩\n" ++ produces)
      | .call _ recipe arguments outputs body => do
        let inputs ← (Composition.select state arguments.toList).mapError errorMessage
        let inputSource ← stateSource table inputs
        let produces ← if Execution.isMidpoint recipe then do
            pure ("refine Or.inl ⟨rfl, ?_⟩\n" ++
              "refine ⟨_, _, rfl, ?_, ?_⟩\n" ++
              s!"· {arithmetic}\n" ++
              "· simp only [Midpoint.point, List.cons.injEq, Object.point.injEq, and_true, Prod.ext_iff]\n" ++
              s!"  {arithmetic}")
          else do
            let final ← (Execution.replay inputs body).mapError errorMessage
            let (child, rest) ← proofSource table arithmetic bits inputs body remaining
            remaining := rest
            let selected := s!"by\n  conv_lhs => arg 2; tactic => exact " ++
              s!"(show _ = {repr recipe.publicOutputs.toList} from by decide +kernel)\n  rfl"
            pure (s!"refine Or.inr ⟨{← stateSource table final}, rfl, ?_, {selected}⟩\n" ++ child)
        state := state ++ outputs
        pure (s!"refine Composition.Checked.call _ _ ({inputSource}) _ _ rfl rfl ?_\n" ++ produces)
    proofs := proofs ++ ["apply Composition.Certified.cons\n· " ++ head.replace "\n" "\n  "]
  return (String.intercalate "\n" (proofs ++ ["exact Composition.Certified.nil _"]), remaining)

/-- Prepare a persistent proof expression. Success here is only a proposal:
submission elaborates it and checks its transitive axiom dependencies. -/
def prepareComposition (session : Session) (point : Nat) (coordinate : Coordinate) :
    IO (Except String String) := do
  try
    if session.running.isSome || session.pending.isSome then
      return .error "Finish or cancel the current operation before submitting."
    unless session.seeds = Program.initial do
      return .error "Proof constructions must start from the standard seed points."
    let target ← get (session.selected point coordinate)
    let log ← IO.mkRef (#[] : ArithmeticLog)
    ArithmeticLog.seed log [0,1]
    let (final, blocks, prepared) ← recordHistory log Program.initial session.program
    unless final = session.objects do return .error "The public history and drawing disagree."
    let recorded ← log.get
    return do
      let table ← CoordinateTable.prepareBlocks recorded blocks target
      let targetNonneg := decide (0 ≤ target)
      let signs := prepared.flatMap (fun entry => entry.2.signs) ++
        (if targetNonneg then [target] else [])
      let (table, bits) ← LibraryRecipe.refineSigns table signs
      let history ← historySource table session.program
      let state ← stateSource table final
      let scalar ← table.scalarSource target
      let fields := table.fieldSources
      let arithmetic := "origami_library_arithmetic [" ++
        String.intercalate ", " (fields.map Prod.fst) ++ "]"
      let (proof, remaining) ← proofSource table arithmetic bits Program.initial session.program prepared
      unless remaining.isEmpty do throw "Unused prepared library witnesses."
      let targetSign ← if targetNonneg then do
          let sign ← LibraryRecipe.signSource table arithmetic bits target false
          pure ("  have _target_nonneg : 0 ≤ target := by\n" ++ indent (indent ("dsimp only [target]\n" ++ sign)) ++ "\n")
        else pure ""
      let axis := match coordinate with | .x => "x" | .y => "y"
      let declarations := String.join (fields.map fun (name, value) =>
        s!"  let {name} : Scalar.Presentation := {value}\n")
      pure (s!"set_option maxRecDepth 8192 in\nset_option maxHeartbeats {certificateHeartbeats} in\n" ++
        "set_option exponentiation.threshold 8192 in\nopen LeanOrigami LeanOrigami.Text LeanOrigami.Widget Hex in\nby\n" ++
        declarations ++ s!"  let history : Execution.History Scalar := {history}\n" ++
        s!"  let final : Program.State Scalar := {state}\n  let target : Scalar := {scalar}\n" ++
        targetSign ++ s!"  refine ⟨history, final, ⟨{point}⟩, .{axis}, target, ?_, ?_, ?_⟩\n" ++
        "  · dsimp only [history, final]\n" ++ indent (indent proof) ++ "\n" ++
        "  · exact ⟨_, rfl, rfl⟩\n" ++
        s!"  · origami_identify target using {arithmetic}\n")
  catch error => return .error error.toString

end LeanOrigami.Widget
