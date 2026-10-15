import LeanOrigami.Construction.Checker

/-!
# Public-output constructions and compositional certificates

A recipe call appends only its public outputs. Internal objects have no indices
in the caller. A registry associates an exact recipe identity with a relation
and a proved constructibility theorem. Primitive execution and theorem-based
calls share the same certificate and soundness statement. Replaying data for
visualization is deliberately separate from certifying it.
-/

namespace LeanOrigami
namespace Composition
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Read ordered public references, rejecting nonexistent objects. -/
def select (state : Program.State K) : List Nat → Except ConstructionError (Program.State K)
  | [] => .ok []
  | index :: rest => do
    let some object := state[index]? | throw (.missingReference index)
    return object :: (← select state rest)

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Selection cannot introduce an object absent from the caller's state. -/
theorem select_mem {state : Program.State K} {refs : List Nat} {inputs : Program.State K}
    (h : select state refs = .ok inputs) : ∀ object ∈ inputs, object ∈ state := by
  induction refs generalizing inputs with
  | nil => simp [select] at h; subst inputs; simp
  | cons index rest ih =>
    simp only [select, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    cases lookup : state[index]? with
    | none => simp [lookup] at h
    | some object =>
      simp only [lookup] at h
      cases tail : select state rest with
      | error error => simp [tail] at h
      | ok objects =>
        simp only [tail, Except.ok.injEq] at h
        subst inputs
        intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact List.mem_of_getElem? lookup
        · exact ih tail value member

/-- A recipe relation includes its domain, output identity, and branch choices.
Its theorem certifies all public outputs together from the available inputs.
The registry is mathematical data: an untrusted name alone proves nothing. -/
structure RecipeRule (K : Type*) [Field K] where
  Produces : Program.State K → Program.State K → Prop
  sound : ∀ (f : K →+* ℝ) inputs outputs, Produces inputs outputs →
    (∀ object ∈ inputs, Constructible (object.map f)) →
    ∀ object ∈ outputs, Constructible (object.map f)

/-- Exact identities are chosen by the authoring layer from saved recipe data,
not from editable display labels. -/
abbrev Registry (K : Type*) [Field K] := String → Option (RecipeRule K)

/-- One primitive or one recipe call. A call stores selected exact public outputs;
its recipe body remains separate, scoped inspection data. -/
inductive Node (K : Type*) [Field K] where
  | primitive (instruction : Instruction K)
  | call (identity : String) (arguments : List Nat) (outputs : Program.State K)

/-- Retained calls allocate references by public output count. -/
abbrev Construction (K : Type*) [Field K] := List (Node K)

/-- Reconstruct a public state for display. Call outputs are untrusted until a
`Checked` certificate proves the registered relation for these exact objects. -/
def Node.replay (state : Program.State K) : Node K → Except ConstructionError (Program.State K)
  | .primitive instruction => do
    let object ← Program.step state instruction
    return state ++ [object]
  | .call _ arguments outputs => do
    let _ ← select state arguments
    return state ++ outputs

/-- Replay never opens a recipe's private construction. -/
def replay (state : Program.State K) : Construction K → Except ConstructionError (Program.State K)
  | [] => .ok state
  | node :: rest => do replay (← node.replay state) rest

/-- Evidence for one public-state transition. Calls require both registry
identity and the registered exact relation; primitives use the original checker. -/
inductive Checked (registry : Registry K) (state : Program.State K) :
    Node K → Program.State K → Prop where
  | primitive (instruction : Instruction K) (output : Object K)
      (accepted : Program.step state instruction = .ok output) :
      Checked registry state (.primitive instruction) (state ++ [output])
  | call (identity : String) (arguments : List Nat) (inputs outputs : Program.State K)
      (rule : RecipeRule K) (registered : registry identity = some rule)
      (references : select state arguments = .ok inputs)
      (produces : rule.Produces inputs outputs) :
      Checked registry state (.call identity arguments outputs) (state ++ outputs)

/-- A checked node preserves constructibility without inspecting the body of a
recipe theorem at its call site. -/
theorem Checked.sound {registry : Registry K} {state final : Program.State K} {node : Node K}
    (h : Checked registry state node final) (f : K →+* ℝ)
    (available : ∀ object ∈ state, Constructible (object.map f)) :
    ∀ object ∈ final, Constructible (object.map f) := by
  cases h with
  | primitive instruction output accepted =>
    intro object member
    rcases List.mem_append.mp member with member | member
    · exact available object member
    · have equal := List.mem_singleton.mp member
      subst object
      exact Program.step_sound f available accepted
  | call identity arguments inputs outputs rule registered references produces =>
    intro object member
    rcases List.mem_append.mp member with member | member
    · exact available object member
    · exact rule.sound f inputs outputs produces
        (fun value member => available value (select_mem references value member)) object member

/-- Certified objects and displayed objects are the same public state. -/
theorem Checked.replay_eq {registry : Registry K} {state final : Program.State K} {node : Node K}
    (h : Checked registry state node final) : node.replay state = .ok final := by
  cases h with
  | primitive instruction output accepted => simp [Node.replay, accepted]
  | call identity arguments inputs outputs rule registered references produces =>
    simp [Node.replay, references]

/-- A compositional proof follows public nodes, not the private folds of calls. -/
inductive Certified (registry : Registry K) :
    Program.State K → Construction K → Program.State K → Prop where
  | nil (state) : Certified registry state [] state
  | cons {state middle final node rest}
      (head : Checked registry state node middle)
      (tail : Certified registry middle rest final) :
      Certified registry state (node :: rest) final

/-- Every public object in a certified construction is constructible. -/
theorem Certified.sound {registry : Registry K} {state final : Program.State K}
    {construction : Construction K} (h : Certified registry state construction final)
    (f : K →+* ℝ) (available : ∀ object ∈ state, Constructible (object.map f)) :
    ∀ object ∈ final, Constructible (object.map f) := by
  induction h with
  | nil => exact available
  | cons head tail ih => exact ih (head.sound f available)

/-- Saved display replay agrees with the state established by the certificate. -/
theorem Certified.replay_eq {registry : Registry K} {state final : Program.State K}
    {construction : Construction K} (h : Certified registry state construction final) :
    replay state construction = .ok final := by
  induction h with
  | nil => rfl
  | cons head tail ih => simp [replay, head.replay_eq, Bind.bind, Except.bind, ih]

/-- Fallback for a concrete recipe body without a reusable output theorem.
The body executes with local input indices; only selected outputs cross the
boundary. Its ordinary execution proof is supplied once for this invocation. -/
def RecipeRule.primitive (body : Program K) (results : List Nat) : RecipeRule K where
  Produces inputs outputs := ∃ final,
    Program.execute inputs body = .ok final ∧ select final results = .ok outputs
  sound f inputs outputs h available := by
    obtain ⟨final, executed, selected⟩ := h
    exact fun object member => Program.execute_sound f available body final executed
      object (select_mem selected object member)

/-- Lift old primitive programs without changing their reference numbering. -/
def ofProgram (program : Program K) : Construction K := program.map Node.primitive

/-- Legacy program replay is preserved exactly by the structural embedding. -/
theorem replay_ofProgram (program : Program K) (state : Program.State K) :
    replay state (ofProgram program) = Program.execute state program := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction rest ih =>
    simp only [ofProgram, List.map_cons, replay, Node.replay, Program.execute]
    cases Program.step state instruction <;> simp_all [ofProgram, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- A selected coordinate of a certified public point solves the ordinary
constructibility goal. No primitive expansion of recipe calls is required. -/
theorem Certified.coordinate_sound {registry : Registry K} {final : Program.State K}
    {construction : Construction K}
    (h : Certified registry Program.initial construction final) (f : K →+* ℝ)
    (index : Nat) (point : Point K) (coordinate : Coordinate) (target : K)
    (selected : final[index]? = some (.point point))
    (equal : coordinate.get point = target) : ConstructibleNumber (f target) := by
  have seeds := Program.run_sound f ([] : Program K) Program.initial rfl
  have constructed := h.sound f seeds (.point point) (List.mem_of_getElem? selected)
  refine ⟨(f point.1, f point.2), constructed, ?_⟩
  cases coordinate with
  | x => exact Or.inl (congrArg f equal).symm
  | y => exact Or.inr (congrArg f equal).symm

end Composition
end LeanOrigami
