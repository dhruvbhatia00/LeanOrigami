import LeanOrigami.Scalar.FoldDiscovery
import LeanOrigami.Widget.Execution
import Lean.Data.Json.FromToJson

/-!
# Exact construction editing

An immutable session holds scoped calls and primitive selections.
Candidate indices are meaningful only within one session snapshot; committing
one stores its exact crease. Display coordinates never enter the program.
-/

namespace LeanOrigami.Widget

mutual

/-- An editing snapshot contains only public objects in its current scope.
A running recipe owns a separate child session for its private construction. -/
structure Session where
  program : Execution.History Scalar := []
  objects : Program.State Scalar := Program.initial
  pending : Option (FoldRequest × List (Line Scalar)) := none
  seeds : Program.State Scalar := Program.initial
  groups : Array RecipeGroup := #[]
  running : Option RecipeCursor := none
  result : Option Nat := none
  failure : Option String := none
  requirements : Array Condition := #[]
  checks : Array RecipeRequirement := #[]
  outputs : Array RecipeOutput := #[]

/-- Private continuation of a scoped call. Cancelling discards the child and
leaves the parent's public objects and history intact. -/
structure RecipeCursor where
  name : String
  recipe : RecipeTemplate
  arguments : Array Nat
  inner : Session
  remaining : List RecipeOperation

end

/-- Human-readable geometric failures, shared by all editing operations. -/
def errorMessage : ConstructionError → String
  | .missingReference i => s!"Object {i} no longer exists."
  | .expectedPoint i => s!"Object {i} must be a point."
  | .expectedLine i => s!"Object {i} must be a line."
  | .coincidentPoints => "Choose two distinct points."
  | .parallelLines => "These lines do not have a unique intersection."
  | .coincidentLines => "Choose two distinct lines."
  | .underconstrainedFold => "These inputs allow infinitely many folds. Choose other inputs."
  | .noFoldSolutions => "No real fold satisfies these inputs."
  | .incorrectOutput => "The selected result does not satisfy this operation."
  | .targetMismatch => "The selected coordinate does not equal the goal."

/-- Open a legacy primitive program in the scoped editor without renumbering
its original objects. Old source remains readable while new saves retain calls. -/
def Session.ofProgram (program : Program Scalar) : Except String Session := do
  let objects ← (Program.run program).mapError errorMessage
  return { program := Execution.ofProgram program, objects }

/-- Decode ordered object selections. The ordinary resolver checks their kinds. -/
def foldRequest (axiomNumber : Nat) (inputs : List Nat) : Except String FoldRequest :=
  match axiomNumber, inputs with
  | 1, [p, q] => .ok (.axiom1 ⟨p⟩ ⟨q⟩)
  | 2, [p, q] => .ok (.axiom2 ⟨p⟩ ⟨q⟩)
  | 3, [l, m] => .ok (.axiom3 ⟨l⟩ ⟨m⟩)
  | 4, [p, l] => .ok (.axiom4 ⟨p⟩ ⟨l⟩)
  | 5, [p, q, l] => .ok (.axiom5 ⟨p⟩ ⟨q⟩ ⟨l⟩)
  | 6, [p, q, l, m] => .ok (.axiom6 ⟨p⟩ ⟨q⟩ ⟨l⟩ ⟨m⟩)
  | 7, [p, l, m] => .ok (.axiom7 ⟨p⟩ ⟨l⟩ ⟨m⟩)
  | _, _ => .error "Choose the required inputs in the displayed order."

/-- Find all real creases without constructing proof expressions. -/
def Session.preview (session : Session) (request : FoldRequest) : Except String Session := do
  let input ← (Program.resolve session.objects request).mapError errorMessage
  let some choices := Scalar.folds input
    | throw (errorMessage .underconstrainedFold)
  if choices.isEmpty then throw (errorMessage .noFoldSolutions)
  return { session with pending := some (request, choices) }

private def Session.append (session : Session) (instruction : Instruction Scalar) :
    Except String Session := do
  let object ← (Program.step session.objects instruction).mapError errorMessage
  return { session with
    program := session.program ++ [Execution.Step.primitive instruction]
    objects := session.objects ++ [object], pending := none, result := none }

/-- Compute and append an exact intersection of two previously constructed lines. -/
def Session.intersect (session : Session) (left right : Nat) : Except String Session := do
  let l ← (Program.line session.objects ⟨left⟩).mapError errorMessage
  let r ← (Program.line session.objects ⟨right⟩).mapError errorMessage
  let p ← (Solver.intersect l r).mapError errorMessage
  session.append (.intersect ⟨left⟩ ⟨right⟩ p.val)

/-- The scope currently being explored, including a paused nested call. -/
partial def Session.active (session : Session) : Session :=
  match session.running with
  | none => session
  | some cursor => cursor.inner.active

/-- Record a completed call as one node and expose only its selected outputs. -/
private def Session.finishCall (session : Session) (cursor : RecipeCursor) : Except String Session := do
  let inner := cursor.inner
  if cursor.name.isEmpty then
    return { inner with result := some cursor.recipe.output }
  let outputs ← (Composition.select (K := Scalar) inner.objects cursor.recipe.publicOutputs.toList).mapError errorMessage
  let base := session.objects.length
  let program : Execution.History Scalar := session.program ++ [Execution.Step.call cursor.name cursor.recipe cursor.arguments outputs inner.program]
  return { session with
    program, objects := session.objects ++ outputs,
    groups := Execution.groups (K := Scalar) session.seeds.length program,
    running := none, pending := none, failure := none, result := some base }

/-- Validate inputs in the caller before entering a private recipe scope. -/
private def Session.startRecipe (session : Session) (name : String) (recipe : RecipeTemplate)
    (arguments : Array Nat) : Except String Session := do
  if session.running.isSome then throw "Finish or cancel the current recipe first."
  let _ ← recipe.validate
  unless arguments.size == recipe.parameters.size do throw "Select every recipe input."
  let inputs ← (Composition.select (K := Scalar) session.objects arguments.toList).mapError errorMessage
  for (object, parameter) in inputs.zip recipe.parameters.toList do
    unless objectKind object == parameter.kind do
      throw s!"Recipe input {parameter.name} has the wrong kind."
  let requirementsHold := recipe.requirements.all (Condition.checkObjects inputs)
  if requirementsHold && !name.isEmpty && Execution.isMidpoint recipe then
    let outputs ← Execution.midpointOutputs (K := Scalar) inputs
    let program : Execution.History Scalar := session.program ++ [Execution.Step.call name recipe arguments outputs []]
    return { session with
    program, objects := session.objects ++ outputs,
      groups := Execution.groups (K := Scalar) session.seeds.length program,
      result := some session.objects.length, pending := none, failure := none }
  let inner : Session := {
    seeds := inputs, objects := inputs,
    requirements := recipe.requirements, checks := recipe.checks, outputs := recipe.outputs }
  return { session with
    pending := none, failure := none,
    running := some ⟨name, recipe, arguments, inner, recipe.steps⟩ }

/-- Discover operations inside their own scope. A branch pause or failed
condition retains the private continuation; no intermediate leaks to the parent. -/
private partial def Session.advance (session : Session) : Session := Id.run do
  let some cursor := session.running | return session
  let inner := cursor.inner
  if inner.running.isSome then
    let inner := inner.advance
    let next := { session with running := some { cursor with inner } }
    if inner.running.isSome || inner.pending.isSome || inner.failure.isSome then
      return { next with failure := inner.failure }
    return next.advance
  if inner.pending.isSome || inner.failure.isSome then
    return { session with failure := inner.failure }
  if inner.program.isEmpty && !inner.requirements.all (Condition.checkObjects inner.objects) then
    let failure := some "The recipe's input requirements are not satisfied."
    return { session with failure, running := some { cursor with inner := { inner with failure } } }
  let failed := inner.checks.find? fun check => check.before == inner.program.length &&
    !check.condition.checkObjects inner.objects
  if let some check := failed then
    let failure := some ("Requirement failed: " ++
      conditionDescription (fun i => s!"object {i}") check.condition)
    return { session with failure, running := some { cursor with inner := { inner with failure } } }
  match cursor.remaining with
  | [] =>
    match session.finishCall cursor with
    | .ok finished => return finished
    | .error message => return { session with failure := some message }
  | step :: rest =>
    let attempt : Except String Session := do
      match step with
      | .intersect l r => inner.intersect l.index r.index
      | .call name recipe arguments => inner.startRecipe name recipe arguments
      | .fold request =>
        let preview ← inner.preview request
        let preview := { preview with pending := preview.pending.map fun (request, choices) =>
          (request, RecipeRequirement.filterCreases inner.checks (inner.program.length + 1)
            inner.objects choices) }
        match preview.pending with
        | some (_, []) => throw "No crease satisfies the next branch/output conditions."
        | some (_, [crease]) => preview.append (.fold request crease)
        | some _ => pure preview
        | none => throw "Recipe discovery did not produce a preview."
    match attempt with
    | .error message =>
      let failure := some s!"Step {inner.program.length + 1}: {message}"
      return { session with failure, running := some { cursor with inner := { inner with failure } } }
    | .ok inner =>
      let next := { session with running := some { cursor with inner, remaining := rest } }
      if inner.pending.isSome then return next else return next.advance

private def Session.replayResult (session : Session) (retainFailure : Bool) : Except String Session := do
  if !retainFailure then
    if let some message := session.failure then throw message
  return session

/-- Commit a crease in the active scope, then resume its containing calls. -/
partial def Session.choose (session : Session) (index : Nat) (retainFailure : Bool := false) :
    Except String Session := do
  if let some cursor := session.running then
    let inner ← cursor.inner.choose index retainFailure
    let next := { session with failure := none, running := some { cursor with inner } }
    return ← next.advance.replayResult retainFailure
  let some (request, choices) := session.pending | throw "Preview a fold first."
  let some crease := choices[index]? | throw "This fold choice is no longer available."
  session.append (.fold request crease)

/-- Apply a retained call to public inputs. Proved midpoint calls compute only
their output; other definitions use the same scoped discovery and fallback. -/
def Session.useRecipe (session : Session) (name : String) (recipe : RecipeTemplate)
    (arguments : Array Nat) (retainFailure : Bool := false) : Except String Session := do
  let started ← session.startRecipe name recipe arguments
  started.advance.replayResult retainFailure

/-- Undo one public node, or cancel a private continuation atomically. -/
def Session.undo (session : Session) : Except String Session := do
  if session.running.isSome then return { session with running := none, pending := none, failure := none }
  let stop := session.program.length - 1
  let program := session.program.take stop
  let objects ← (Execution.replay session.seeds program).mapError errorMessage
  return { session with
    program, objects, pending := none, result := none, failure := none,
    groups := Execution.groups (K := Scalar) session.seeds.length program,
    checks := session.checks.filter (fun check => check.owner < stop),
    outputs := session.outputs.filter (fun output => output.index < objects.length) }

/-- Save operations and nested definitions, never old sample coordinates. -/
def Session.template (session : Session) (parameters : Array RecipeParameter) (output : Nat) :
    Except String RecipeTemplate := do
  if session.running.isSome then throw "Finish or cancel the recipe before saving."
  unless parameters.size == session.seeds.length do throw "The workspace parameters changed."
  let recipe : RecipeTemplate := ⟨parameters, session.program.map Execution.Step.operation,
    output, session.groups, session.requirements, session.checks, session.outputs⟩
  let _ ← recipe.validate
  return recipe

/-- Name a public result. Private objects are absent from this scope. -/
def Session.nameOutput (session : Session) (name : String) (index : Nat) : Except String Session := do
  if session.running.isSome then throw "Finish or cancel the recipe before naming outputs."
  let name := name.trimAscii.toString
  if name.isEmpty then throw "Give this output a name."
  unless session.objects[index]?.isSome do throw "This output does not exist."
  if session.outputs.any (·.name == name) then throw "Use a distinct name for each output."
  return { session with outputs := session.outputs.push ⟨name, index⟩ }

/-- Read a public point's exact coordinate. -/
def Session.selected (session : Session) (point : Nat) (coordinate : Coordinate) : Except String Scalar := do
  return coordinate.get (← (Program.point session.objects ⟨point⟩).mapError errorMessage)

/-- Inspect a completed call in a separate local scope. Recorded choices are
preserved; optimized midpoint calls reconstruct their small explanation lazily. -/
def Session.inspect (session : Session) (index : Nat) : Except String Session := do
  let some (Execution.Step.call _ recipe arguments _ body) := session.program[index]?
    | throw "Choose a completed recipe call to inspect."
  let inputs ← (Composition.select (K := Scalar) session.objects arguments.toList).mapError errorMessage
  if body.isEmpty then
    ({ seeds := inputs, objects := inputs } : Session).useRecipe "" recipe (Array.range inputs.length)
  else
    let objects ← (Execution.replay inputs body).mapError errorMessage
    return {
      seeds := inputs, objects, program := body,
      groups := Execution.groups (K := Scalar) inputs.length body,
      result := some recipe.output, outputs := recipe.namedOutputs,
      requirements := recipe.requirements, checks := recipe.checks }

/-- A display approximation with its enclosing-ball radius, both decimal strings.
Conversion to machine numbers is exclusively a rendering concern. -/
structure Approximation where
  value : String
  error : String
  deriving Lean.ToJson, Lean.FromJson

/-- Refine Hex's exact root enclosure. Clamp requests to a practical display budget. -/
def approximate (value : Scalar) (bits : Nat) : Approximation :=
  let ball := value.val.approx (max 32 (min 512 bits) : Int)
  let decimal (q : Rat) := toString (q.num.toFloat / q.den.toFloat)
  ⟨decimal ball.re.toRat, decimal ball.radius.toRat⟩

/-- Stable object identity and either point coordinates or implicit line coefficients. -/
structure ObjectView where
  index : Nat
  kind : String
  values : Array Approximation
  deriving Lean.ToJson, Lean.FromJson

private def objectView (index bits : Nat) : Object Scalar → ObjectView
  | .point p => ⟨index, "point", #[approximate p.1 bits, approximate p.2 bits]⟩
  | .line l => ⟨index, "line", #[approximate l.a bits, approximate l.b bits,
      approximate l.c bits]⟩

/-- History display metadata refers to the same objects as the exact program.
Inputs retain their operation order; output is the appended object's index. -/
structure HistoryStep where
  description : String
  inputs : Array Nat
  output : Nat
  deriving Lean.ToJson, Lean.FromJson

/-- Describe a step and expose its references without parsing human-readable text. -/
def historyStep (output : Nat) : Instruction Scalar → HistoryStep
  | .intersect l r _ =>
    ⟨s!"Intersect lines {l.index} and {r.index}", #[l.index, r.index], output⟩
  | .fold request _ =>
    let (description, inputs) := match request with
      | .axiom1 p q =>
        (s!"Axiom 1: through points {p.index}, {q.index}", #[p.index, q.index])
      | .axiom2 p q =>
        (s!"Axiom 2: point {p.index} onto point {q.index}", #[p.index, q.index])
      | .axiom3 l m =>
        (s!"Axiom 3: line {l.index} onto line {m.index}", #[l.index, m.index])
      | .axiom4 p l =>
        (s!"Axiom 4: through point {p.index}, perpendicular to line {l.index}", #[p.index, l.index])
      | .axiom5 p q l =>
        (s!"Axiom 5: point {p.index} onto line {l.index}, fixing point {q.index}",
          #[p.index, q.index, l.index])
      | .axiom6 p q l m =>
        (s!"Axiom 6: points {p.index}, {q.index} onto lines {l.index}, {m.index}",
          #[p.index, q.index, l.index, m.index])
      | .axiom7 p l m =>
        (s!"Axiom 7: point {p.index} onto line {l.index}, perpendicular to line {m.index}",
          #[p.index, l.index, m.index])
    ⟨description, inputs, output⟩

/-- Display data contains no editable exact coordinates. -/
structure View where
  inspecting : Bool := false
  objects : Array ObjectView
  choices : Array ObjectView
  steps : Nat
  history : Array HistoryStep
  groups : Array RecipeGroup := #[]
  running : Bool := false
  result : Option Nat := none
  failure : Option String := none
  outputs : Array RecipeOutput := #[]
  deriving Lean.ToJson, Lean.FromJson

/-- Render a snapshot at the requested precision, preserving exact candidate identity. -/
def Session.view (session : Session) (bits : Nat) : View := Id.run do
  let active := session.active
  let choices := match active.pending with | none => [] | some (_, ls) => ls
  let mut base := active.seeds.length
  let mut history := #[]
  for step in active.program do
    let entry := match step with
      | .primitive instruction => historyStep base instruction
      | .call name _ arguments _ _ => ⟨"Recipe: " ++ name, arguments, base⟩
    history := history.push entry
    base := base + step.outputs.length
  return {
    objects := active.objects.toArray.mapIdx fun i o => objectView i bits o
    choices := choices.toArray.mapIdx fun i l => objectView i bits (.line l)
    steps := active.program.length, history, groups := active.groups,
    running := session.running.isSome, result := session.result,
    failure := session.failure, outputs := active.outputs }

end LeanOrigami.Widget
