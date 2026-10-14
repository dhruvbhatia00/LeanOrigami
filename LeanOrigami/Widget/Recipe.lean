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

/-- A named result refers to an existing object; it never introduces geometry.
The kind is determined from the referenced object during validation. -/
structure RecipeOutput where
  name : String
  index : Nat
  deriving Repr, Lean.ToJson, Lean.FromJson

/-- History keeps its original five-field constructor. The last field can
still be a plain index, or can carry named results in new saved constructions. -/
structure RecipeResults where
  index : Nat
  names : Array RecipeOutput := #[]
  deriving Repr

instance (n : Nat) : OfNat RecipeResults n := ⟨⟨n, #[]⟩⟩
instance : Coe Nat RecipeResults := ⟨fun index => ⟨index, #[]⟩⟩
instance : CoeOut RecipeResults Nat := ⟨RecipeResults.index⟩

/-- A named span in a flattened program. Step offsets exclude seed objects. -/
structure RecipeGroup where
  name : String
  start : Nat
  count : Nat
  inputs : Array Nat
  output : RecipeResults
  deriving Repr

/-- Named results of a history group, supplementing its default result. -/
def RecipeGroup.outputs (group : RecipeGroup) : Array RecipeOutput := group.output.names

-- The browser retains its flat representation, including old single-output
-- metadata. The Lean source representation above also accepts old tuples.
instance : Lean.ToJson RecipeGroup where
  toJson group := Lean.Json.mkObj [
    ("name", Lean.toJson group.name), ("start", Lean.toJson group.start),
    ("count", Lean.toJson group.count), ("inputs", Lean.toJson group.inputs),
    ("output", Lean.toJson group.output.index), ("outputs", Lean.toJson group.outputs)]

instance : Lean.FromJson RecipeGroup where
  fromJson? json := do
    let outputs ← match json.getObjVal? "outputs" with
      | .error _ => pure #[]
      | .ok value => Lean.fromJson? value
    return ⟨← json.getObjValAs? String "name", ← json.getObjValAs? Nat "start",
      ← json.getObjValAs? Nat "count", ← json.getObjValAs? (Array Nat) "inputs",
      ⟨← json.getObjValAs? Nat "output", outputs⟩⟩

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
  outputs : Array RecipeOutput := #[]
  deriving Repr

/-- Single-output source remains valid. Named outputs supplement the default
output used by existing callers and by automatic point selection. -/
def RecipeTemplate.namedOutputs (recipe : RecipeTemplate) : Array RecipeOutput :=
  if recipe.outputs.isEmpty then #[⟨"Result", recipe.output⟩] else recipe.outputs

/-- Read a geometric object's kind without inspecting its coordinates. -/
def objectKind {K : Type*} [Field K] : Object K → ObjectKind
  | .point _ => .point
  | .line _ => .line

/-- Erase selected coordinates, so a recipe cannot reuse a sample's solution. -/
def RecipeOperation.ofInstruction {K : Type*} [Zero K] [One K] : Instruction K → RecipeOperation
  | .fold request _ => .fold request
  | .intersect l r _ => .intersect l r

/-- A concrete completion uses exactly the template's primitives and passes
both the ordinary construction checker and every declared timed condition.
The final state length rules out referring to nonexistent future objects. -/
structure RecipeTemplate.Completion {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (recipe : RecipeTemplate) (inputs : Program.State K) (program : Program K)
    (final : Program.State K) : Prop where
  shape : program.map RecipeOperation.ofInstruction = recipe.steps
  execution : Program.execute inputs program = .ok final
  length : final.length = inputs.length + recipe.steps.length
  requirements : recipe.requirements.all (Condition.checkObjects inputs) = true
  checks : recipe.checks.all (fun check =>
    check.condition.checkObjects (final.take (inputs.length + check.before))) = true
  inputs_valid : inputs.length = recipe.parameters.size ∧
    (inputs.zip recipe.parameters.toList).all (fun (object, parameter) =>
      objectKind object == parameter.kind) = true

/-- A specification is tied to one exact template, a stated family of inputs,
and an exact output condition. Success is required in addition to soundness;
a recipe which always fails cannot acquire a useful contract this way. -/
structure RecipeContract {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {Parameters : Type} (recipe : RecipeTemplate) (inputs : Parameters → Program.State K)
    (domain : Parameters → Prop) (postcondition : Condition) : Prop where
  sound : ∀ parameters, domain parameters → ∀ program final,
    recipe.Completion (inputs parameters) program final → postcondition.Satisfied final
  succeeds : ∀ parameters, domain parameters → ∃ program final,
    recipe.Completion (inputs parameters) program final

/-- A final-boundary condition is a genuine statement about the final exact
objects of any completion, independent of candidate enumeration order. -/
theorem RecipeTemplate.Completion.final_condition {K : Type} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {recipe : RecipeTemplate} {inputs final : Program.State K}
    {program : Program K} (completion : recipe.Completion inputs program final)
    (check : RecipeRequirement) (member : check ∈ recipe.checks)
    (boundary : check.before = recipe.steps.length) : check.condition.Satisfied final := by
  have accepted := (Array.all_eq_true_iff_forall_mem.mp completion.checks) check member
  rw [boundary, ← completion.length, List.take_length] at accepted
  exact (Condition.checkObjects_iff _ _).mp accepted

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
  let mut outputNames : Array String := #[]
  for result in recipe.namedOutputs do
    if result.name.trimAscii.toString.isEmpty || outputNames.contains result.name then
      throw "Output names must be nonblank and distinct."
    unless kinds[result.index]?.isSome do throw s!"Output {result.name} does not exist."
    outputNames := outputNames.push result.name
  for group in recipe.groups do
    unless group.count > 0 && group.start + group.count ≤ recipe.steps.length &&
        group.inputs.all (· < recipe.parameters.size + group.start) &&
        group.output.index < recipe.parameters.size + group.start + group.count do
      throw "Invalid recipe history group."
    for result in group.outputs do
      unless result.index < recipe.parameters.size + group.start + group.count do
        throw "A named history output does not exist at the end of its call."
  return output

/-- Filter exact creases by the conditions whose objects become available at
this boundary. Later conditions remain continuation checks; no sample index is
reused, and multiple surviving creases still require a user choice. -/
def RecipeRequirement.filterCreases {K : Type} [Field K] [LinearOrder K]
    (checks : Array RecipeRequirement) (boundary : Nat) (objects : Program.State K)
    (choices : List (Line K)) : List (Line K) :=
  choices.filter fun crease => checks.all fun check =>
    check.before != boundary || check.condition.checkObjects (objects ++ [.line crease])

/-- Filtering neither invents creases nor loses any crease satisfying the
conditions that can be checked now. -/
theorem RecipeRequirement.mem_filterCreases {K : Type} [Field K] [LinearOrder K]
    (checks : Array RecipeRequirement) (boundary : Nat) (objects : Program.State K)
    (choices : List (Line K)) (crease : Line K) :
    crease ∈ filterCreases checks boundary objects choices ↔
      crease ∈ choices ∧ ∀ check ∈ checks, check.before = boundary →
        check.condition.Satisfied (objects ++ [.line crease]) := by
  simp only [filterCreases, List.mem_filter, Array.all_eq_true_iff_forall_mem,
    Bool.or_eq_true, bne_iff_ne, Condition.checkObjects_iff]
  constructor
  · rintro ⟨member, conditions⟩
    refine ⟨member, fun check hc hb => ?_⟩
    exact (conditions check hc).resolve_left (not_not_intro hb)
  · rintro ⟨member, conditions⟩
    refine ⟨member, fun check hc => ?_⟩
    by_cases hb : check.before = boundary
    · exact Or.inr (conditions check hc hb)
    · exact Or.inl hb

/-- Automatic selection is justified when a valid desired crease exists and
is the only one passing the policy. Candidate order has no role in the result. -/
theorem RecipeRequirement.filterCreases_singleton {K : Type} [Field K] [LinearOrder K]
    (checks : Array RecipeRequirement) (boundary : Nat) (objects : Program.State K)
    (choices : List (Line K)) (crease : Line K) (distinct : choices.Nodup)
    (present : crease ∈ filterCreases checks boundary objects choices)
    (unique : ∀ candidate ∈ filterCreases checks boundary objects choices, candidate = crease) :
    filterCreases checks boundary objects choices = [crease] := by
  apply List.Perm.eq_singleton
  apply (List.perm_ext_iff_of_nodup (distinct.filter _) (by simp)).mpr
  intro candidate
  simp only [List.mem_singleton]
  constructor
  · exact unique candidate
  · rintro rfl; exact present

/-- Relocate a template operation into a calling program. -/
def RecipeOperation.remap (f : Nat → Nat) : RecipeOperation → RecipeOperation
  | .fold request => .fold (request.remap f)
  | .intersect l r => .intersect ⟨f l.index⟩ ⟨f r.index⟩

private def arraySource (xs : Array String) := "#[" ++ String.intercalate ", " xs.toList ++ "]"

/-- Serialize output names as escaped literals and stable object references. -/
def RecipeOutput.source (output : RecipeOutput) : String :=
  s!"⟨{Lean.Json.compress (Lean.toJson output.name)}, {output.index}⟩"

/-- Stable ordinary Lean source; strings use Lean-compatible escaped literals. -/
def RecipeGroup.source (group : RecipeGroup) : String :=
  s!"⟨{Lean.Json.compress (Lean.toJson group.name)}, {group.start}, {group.count}, " ++
    arraySource (group.inputs.map toString) ++ ", " ++
    (if group.outputs.isEmpty then toString group.output.index else
      "{ index := " ++ toString group.output.index ++ ", names := " ++ arraySource (group.outputs.map RecipeOutput.source) ++ " }") ++ "⟩"

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
      s!"⟨{check.before}, {check.owner}, {conditionSource check.condition}⟩") ++
    ", outputs := " ++ arraySource (recipe.outputs.map RecipeOutput.source) ++ " }"

/-- Midpoint of distinct points: join, bisect, intersect. Coincident inputs
are rejected by the primitive guards; no arbitrary crease is chosen. -/
def midpointRecipe : RecipeTemplate := {
  parameters := #[⟨"First point", .point⟩, ⟨"Second point", .point⟩]
  steps := [.fold (.axiom1 ⟨0⟩ ⟨1⟩), .fold (.axiom2 ⟨0⟩ ⟨1⟩), .intersect ⟨2⟩ ⟨3⟩]
  output := 4
  requirements := #[.not (.samePoint 0 1)] }

end LeanOrigami.Widget
