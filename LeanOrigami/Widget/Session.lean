import LeanOrigami.Scalar.FoldDiscovery
import LeanOrigami.Widget.Recipe
import Lean.Data.Json.FromToJson

/-!
# Exact construction editing

An immutable session holds the same program consumed by the text exporter.
Candidate indices are meaningful only within one session snapshot; committing
one stores its exact crease. Display coordinates never enter the program.
-/

namespace LeanOrigami.Widget

/-- Continuation of a recipe call. Undo rolls back to `start`; every paused
branch still refers to the current exact snapshot. -/
structure RecipeCursor where
  remaining : List RecipeOperation
  group : RecipeGroup
  nested : Array RecipeGroup

/-- An editing snapshot. Undo and asynchronous requests can retain older snapshots. -/
structure Session where
  program : Program Scalar := []
  objects : Program.State Scalar := Program.initial
  pending : Option (FoldRequest × List (Line Scalar)) := none
  seeds : Program.State Scalar := Program.initial
  groups : Array RecipeGroup := #[]
  running : Option RecipeCursor := none
  result : Option Nat := none

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
    program := session.program ++ [instruction]
    objects := session.objects ++ [object], pending := none, result := none }

/-- Compute and append an exact intersection of two previously constructed lines. -/
def Session.intersect (session : Session) (left right : Nat) : Except String Session := do
  let l ← (Program.line session.objects ⟨left⟩).mapError errorMessage
  let r ← (Program.line session.objects ⟨right⟩).mapError errorMessage
  let p ← (Solver.intersect l r).mapError errorMessage
  session.append (.intersect ⟨left⟩ ⟨right⟩ p.val)

private def Session.advance (session : Session) (steps : List RecipeOperation) :
    Except String Session := do
  match steps with
  | [] =>
    let some cursor := session.running | return session
    let groups := if cursor.group.name.isEmpty || cursor.group.count == 0 then session.groups
      else session.groups.push cursor.group
    return { session with
      running := none, result := some cursor.group.output
      groups := groups ++ cursor.nested }
  | step :: rest =>
    let some cursor := session.running | throw "No recipe is running."
    let session := { session with running := some { cursor with remaining := rest } }
    match step with
    | .intersect l r => (← session.intersect l.index r.index).advance rest
    | .fold request =>
      let preview ← session.preview request
      match preview.pending with
      | some (_, [crease]) => (← preview.append (.fold request crease)).advance rest
      | some _ => return preview
      | none => throw "Recipe discovery did not produce a preview."

/-- Commit a current exact choice, then continue a paused recipe, if any. -/
def Session.choose (session : Session) (index : Nat) : Except String Session := do
  let some (request, choices) := session.pending | throw "Preview a fold first."
  let some crease := choices[index]? | throw "This fold choice is no longer available."
  let next ← session.append (.fold request crease)
  match session.running with
  | none => return next
  | some cursor => next.advance cursor.remaining

/-- Instantiate on existing exact objects. No sample coordinates or old branch
indices survive. Empty names replay a workspace without grouping its whole body. -/
def Session.useRecipe (session : Session) (name : String) (recipe : RecipeTemplate)
    (arguments : Array Nat) : Except String Session := do
  if session.running.isSome then throw "Finish or cancel the current recipe first."
  let _ ← recipe.validate
  unless arguments.size == recipe.parameters.size do throw "Select every recipe input."
  for (argument, parameter) in arguments.toList.zip recipe.parameters.toList do
    let some object := session.objects[argument]?
      | throw s!"Recipe input {parameter.name} does not exist."
    unless objectKind object == parameter.kind do
      throw s!"Recipe input {parameter.name} has the wrong kind."
  let base := session.objects.length
  let relocate (i : Nat) := if i < arguments.size then arguments[i]! else base + (i - arguments.size)
  let steps := recipe.steps.map (RecipeOperation.remap relocate)
  let group : RecipeGroup := ⟨name, session.program.length, steps.length, arguments, relocate recipe.output⟩
  let nested := recipe.groups.map fun g => { g with
    start := session.program.length + g.start, inputs := g.inputs.map relocate, output := relocate g.output }
  let session := { session with pending := none, running := some ⟨steps, group, nested⟩ }
  session.advance steps

/-- Remove one primitive or an entire completed/paused recipe call. -/
def Session.undo (session : Session) : Except String Session := do
  let stop := match session.running with
    | some cursor => cursor.group.start
    | none => (session.groups.toList.filter fun g => g.start + g.count == session.program.length)
        |>.foldl (fun n g => min n g.start) (session.program.length - 1)
  let program := session.program.take stop
  let objects ← (Program.execute session.seeds program).mapError errorMessage
  return { session with
    program, objects, pending := none, running := none, result := none
    groups := session.groups.filter (fun g => g.start + g.count ≤ stop) }

/-- Record operations, not the exact results on the workspace's sample inputs. -/
def Session.template (session : Session) (parameters : Array RecipeParameter) (output : Nat) :
    Except String RecipeTemplate := do
  if session.running.isSome then throw "Finish or cancel the recipe before saving."
  unless parameters.size == session.seeds.length do throw "The workspace parameters changed."
  let recipe : RecipeTemplate := ⟨parameters, session.program.map RecipeOperation.ofInstruction,
    output, session.groups⟩
  let _ ← recipe.validate
  return recipe

/-- Read the actual selected scalar; screen coordinates cannot supply it. -/
def Session.selected (session : Session) (point : Nat) (coordinate : Coordinate) :
    Except String Scalar := do
  return coordinate.get (← (Program.point session.objects ⟨point⟩).mapError errorMessage)

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
  objects : Array ObjectView
  choices : Array ObjectView
  steps : Nat
  history : Array HistoryStep
  groups : Array RecipeGroup := #[]
  running : Bool := false
  result : Option Nat := none
  deriving Lean.ToJson, Lean.FromJson

/-- Render a snapshot at the requested precision, preserving exact candidate identity. -/
def Session.view (session : Session) (bits : Nat) : View :=
  let choices := match session.pending with | none => [] | some (_, ls) => ls
  { objects := session.objects.toArray.mapIdx fun i o => objectView i bits o
    choices := choices.toArray.mapIdx fun i l => objectView i bits (.line l)
    steps := session.program.length
    history := session.program.toArray.mapIdx fun i step =>
      historyStep (session.seeds.length + i) step
    groups := session.groups, running := session.running.isSome, result := session.result }

end LeanOrigami.Widget
