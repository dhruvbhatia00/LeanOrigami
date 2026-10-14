import LeanOrigami.Widget.Requirements
import LeanOrigami.Construction.Recipe
import LeanOrigami.Construction.Checker
import Lean.Data.Json.FromToJson

/-!
# Parameterized visual recipes

Templates contain references and operations, never recorded coordinates or
branch numbers. Their expansion is discovered anew on concrete inputs. Groups
are presentation metadata for nested calls; certification uses only primitives.
-/

namespace LeanOrigami.Widget

/-- The kind required by a recipe parameter. -/
inductive ObjectKind where
  | point | line
  deriving BEq, Repr, Lean.ToJson, Lean.FromJson

/-- A human-readable, typed input role. -/
structure RecipeParameter where
  name : String
  kind : ObjectKind
  deriving Repr, Lean.ToJson, Lean.FromJson

/-- A fold requiring fresh discovery, or a unique intersection. -/
inductive RecipeOperation where
  | fold (request : FoldRequest)
  | intersect (left right : LineRef)
  deriving Repr

/-- A named span in a flattened program. Step offsets exclude seed objects. -/
structure RecipeGroup where
  name : String
  start : Nat
  count : Nat
  inputs : Array Nat
  output : Nat
  deriving Repr, Lean.ToJson, Lean.FromJson

/-- A reusable construction with local parameter indices followed by outputs.
Nested calls are flattened when recorded, retaining their inspectable groups.
No claim about the geometric meaning of the output is implicit in this data. -/
structure RecipeTemplate where
  parameters : Array RecipeParameter
  steps : List RecipeOperation := []
  output : Nat := 0
  groups : Array RecipeGroup := #[]
  requirements : Array Condition := #[]
  checks : Array RecipeRequirement := #[]
  deriving Repr

/-- Read a geometric object's kind without inspecting its coordinates. -/
def objectKind {K : Type*} [Field K] : Object K → ObjectKind
  | .point _ => .point
  | .line _ => .line

/-- Erase selected coordinates, so a recipe cannot reuse a sample's solution. -/
def RecipeOperation.ofInstruction {K : Type*} [Zero K] [One K] : Instruction K → RecipeOperation
  | .fold request _ => .fold request
  | .intersect l r _ => .intersect l r

/-- Required references and kinds in operation order. -/
def RecipeOperation.inputs : RecipeOperation → List (Nat × ObjectKind)
  | .fold (.axiom1 p q) | .fold (.axiom2 p q) => [(p.index, .point), (q.index, .point)]
  | .fold (.axiom3 l m) => [(l.index, .line), (m.index, .line)]
  | .fold (.axiom4 p l) => [(p.index, .point), (l.index, .line)]
  | .fold (.axiom5 p q l) => [(p.index, .point), (q.index, .point), (l.index, .line)]
  | .fold (.axiom6 p q l m) =>
      [(p.index, .point), (q.index, .point), (l.index, .line), (m.index, .line)]
  | .fold (.axiom7 p l m) => [(p.index, .point), (l.index, .line), (m.index, .line)]
  | .intersect l m => [(l.index, .line), (m.index, .line)]

/-- Validate reference order and kinds, including the selected result. Geometry
is deliberately checked later, on each invocation's actual arguments. -/
def RecipeTemplate.validate (recipe : RecipeTemplate) : Except String ObjectKind := do
  if recipe.parameters.isEmpty then throw "A recipe needs at least one parameter."
  let mut kinds := recipe.parameters.map (·.kind)
  let mut names : Array String := #[]
  for parameter in recipe.parameters do
    if parameter.name.isEmpty || names.contains parameter.name then
      throw "Recipe parameter names must be nonempty and distinct."
    names := names.push parameter.name
  let valid (available : Array ObjectKind) (condition : Condition) :=
    condition.valid (fun i => available[i]? == some .point) (fun i => available[i]? == some .line)
  for condition in recipe.requirements do
    unless valid kinds condition do
      throw "A requirement has a missing/wrong-kind input or a zero denominator."
  for step in recipe.steps do
    for (index, expected) in step.inputs do
      let some actual := kinds[index]? | throw s!"Recipe reference {index} is missing or forward."
      unless actual == expected do throw s!"Recipe reference {index} has the wrong kind."
    kinds := kinds.push (match step with | .fold _ => .line | .intersect _ _ => .point)
  for check in recipe.checks do
    unless check.owner ≤ check.before && check.before ≤ recipe.steps.length &&
        valid (kinds.extract 0 (recipe.parameters.size + check.before)) check.condition do
      throw "A nested requirement has invalid references or a misplaced check."
  let some output := kinds[recipe.output]? | throw "The recipe output does not exist."
  for group in recipe.groups do
    unless group.count > 0 && group.start + group.count ≤ recipe.steps.length &&
        group.inputs.all (· < recipe.parameters.size + group.start) &&
        group.output < recipe.parameters.size + group.start + group.count do
      throw "Invalid recipe history group."
  return output

/-- Relocate a template operation into a calling program. -/
def RecipeOperation.remap (f : Nat → Nat) : RecipeOperation → RecipeOperation
  | .fold request => .fold (request.remap f)
  | .intersect l r => .intersect ⟨f l.index⟩ ⟨f r.index⟩

private def arraySource (xs : Array String) := "#[" ++ String.intercalate ", " xs.toList ++ "]"

/-- Stable ordinary Lean source; strings use Lean-compatible escaped literals. -/
def RecipeGroup.source (group : RecipeGroup) : String :=
  s!"⟨{Lean.Json.compress (Lean.toJson group.name)}, {group.start}, {group.count}, " ++
    arraySource (group.inputs.map toString) ++ s!", {group.output}⟩"

/-- Serialize the small declarative format, without native values or opaque IDs. -/
def RecipeTemplate.source (recipe : RecipeTemplate) : String := Id.run do
  let parameters := arraySource (recipe.parameters.map fun p =>
    s!"⟨{Lean.Json.compress (Lean.toJson p.name)}, .{if p.kind == .point then "point" else "line"}⟩")
  let steps := recipe.steps.map fun step => match step with
    | .intersect l r => s!".intersect ⟨{l.index}⟩ ⟨{r.index}⟩"
    | .fold request =>
      let n := match request with
        | .axiom1 .. => 1 | .axiom2 .. => 2 | .axiom3 .. => 3 | .axiom4 .. => 4
        | .axiom5 .. => 5 | .axiom6 .. => 6 | .axiom7 .. => 7
      s!".fold (.axiom{n} " ++ String.intercalate " " (step.inputs.map fun (i, _) => s!"⟨{i}⟩") ++ ")"
  return "{ parameters := " ++ parameters ++ ", steps := [" ++
    String.intercalate ", " steps ++ s!"], output := {recipe.output}, groups := " ++
    arraySource (recipe.groups.map RecipeGroup.source) ++ ", requirements := " ++
    arraySource (recipe.requirements.map conditionSource) ++ ", checks := " ++
    arraySource (recipe.checks.map fun check =>
      s!"⟨{check.before}, {check.owner}, {conditionSource check.condition}⟩") ++ " }"

/-- Midpoint of distinct points: join, bisect, intersect. Coincident inputs
are rejected by the primitive guards; no arbitrary crease is chosen. -/
def midpointRecipe : RecipeTemplate := {
  parameters := #[⟨"First point", .point⟩, ⟨"Second point", .point⟩]
  steps := [.fold (.axiom1 ⟨0⟩ ⟨1⟩), .fold (.axiom2 ⟨0⟩ ⟨1⟩), .intersect ⟨2⟩ ⟨3⟩]
  output := 4
  requirements := #[.not (.samePoint 0 1)] }

end LeanOrigami.Widget
