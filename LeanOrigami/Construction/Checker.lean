import LeanOrigami.Solvers.Certified

/-!
# Executable program checking and soundness

Execution stores plain exact objects. It checks references, finite-choice fold
conditions, selected intersections, and the submitted target. The soundness
proof follows this same execution separately; neither exploration nor symbolic
certification needs to carry previous construction proofs in the runtime state.
-/

namespace LeanOrigami.Program
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Append-only exact objects; indices remain stable during replay. -/
abbrev State (K : Type*) [Field K] := List (Object K)

/-- The only objects available without an instruction. -/
def initial : State K := [.point (0, 0), .point (1, 0)]

/-- Resolve a point, rejecting missing references and wrong object kinds. -/
def point (state : State K) (ref : PointRef) : Except ConstructionError (Point K) :=
  match state[ref.index]? with
  | some (.point p) => .ok p
  | some (.line _) => .error (.expectedPoint ref.index)
  | none => .error (.missingReference ref.index)

/-- Resolve a line, rejecting missing references and wrong object kinds. -/
def line (state : State K) (ref : LineRef) : Except ConstructionError (Line K) :=
  match state[ref.index]? with
  | some (.line l) => .ok l
  | some (.point _) => .error (.expectedLine ref.index)
  | none => .error (.missingReference ref.index)

/-- Resolve the actual inputs of the requested operation. -/
def resolve (state : State K) : FoldRequest → Except ConstructionError (FoldInput K)
  | .axiom1 p q => return .axiom1 (← point state p) (← point state q)
  | .axiom2 p q => return .axiom2 (← point state p) (← point state q)
  | .axiom3 l m => return .axiom3 (← line state l) (← line state m)
  | .axiom4 p l => return .axiom4 (← point state p) (← line state l)
  | .axiom5 p q l => return .axiom5 (← point state p) (← point state q) (← line state l)
  | .axiom6 p q l m =>
      return .axiom6 (← point state p) (← point state q) (← line state l) (← line state m)
  | .axiom7 p l m => return .axiom7 (← point state p) (← line state l) (← line state m)

/-- Check the exact selected output, without rerunning root discovery. -/
def step (state : State K) : Instruction K → Except ConstructionError (Object K)
  | .fold request selected => do
      let input ← resolve state request
      let _ ← Solver.fold input selected
      return .line selected
  | .intersect left right selected => do
      let l ← line state left
      let m ← line state right
      let solution ← Solver.intersect l m
      if selected = solution.val then return .point selected else throw .incorrectOutput

/-- Execute a suffix using the preceding objects. -/
def execute (state : State K) : Program K → Except ConstructionError (State K)
  | [] => .ok state
  | instruction :: rest => do
      let result ← step state instruction
      execute (state ++ [result]) rest

/-- Replay from the two fixed seeds. -/
def run (program : Program K) : Except ConstructionError (State K) := execute initial program

/-- Submit a point coordinate only after checking the whole saved program. -/
def submit (program : Program K) (ref : PointRef) (coordinate : Coordinate) (target : K) :
    Except ConstructionError (Point K) := do
  let state ← run program
  let p ← point state ref
  if coordinate.get p = target then return p else throw .targetMismatch

/-- Executable success flag, including exact target identification. -/
def accepts (program : Program K) (ref : PointRef) (coordinate : Coordinate) (target : K) : Bool :=
  match submit program ref coordinate target with
  | .ok _ => true
  | .error _ => false

/-- A fold certificate proves precisely the guards checked by executable replay. -/
theorem step_fold_eq {state : State K} {request : FoldRequest} {input : FoldInput K}
    {selected : Line K} (references : resolve state request = .ok input)
    (finite : input.FiniteCondition) (geometry : input.Satisfies selected) :
    step state (.fold request selected) = .ok (.line selected) := by
  simp only [step]
  rw [references]
  dsimp only [Bind.bind, Except.bind]
  unfold Solver.fold
  rw [dite_eq_left finite, dite_eq_left geometry]
  rfl

/-- An intersection certificate checks the actual selected point and denominator. -/
theorem step_intersect_eq {state : State K} {left right : LineRef} {l m : Line K}
    {selected : Point K} (first : line state left = .ok l) (second : line state right = .ok m)
    (determinant : l.determinant m ≠ 0) (geometry : selected = l.intersection m determinant) :
    step state (.intersect left right selected) = .ok (.point selected) := by
  simp only [step]
  rw [first]
  dsimp only [Bind.bind, Except.bind]
  rw [second]
  dsimp only [Bind.bind, Except.bind]
  unfold Solver.intersect
  rw [dite_eq_left determinant]
  dsimp only [Bind.bind, Except.bind]
  rw [ite_eq_left geometry]
  rfl

/-- Compose checked steps without reducing the remaining program. -/
theorem execute_cons_eq {state final : State K} {instruction : Instruction K}
    {rest : Program K} {result : Object K}
    (head : step state instruction = .ok result)
    (tail : execute (state ++ [result]) rest = .ok final) :
    execute state (instruction :: rest) = .ok final := by
  rw [execute, head]
  exact tail

/-- Certificates establish the same flag as executable replay. -/
theorem accepts_of_run {program : Program K} {state : State K}
    {ref : PointRef} {coordinate : Coordinate} {target : K} {p : Point K}
    (execution : run program = .ok state) (reference : point state ref = .ok p)
    (target_eq : coordinate.get p = target) : accepts program ref coordinate target = true := by
  unfold accepts submit
  rw [execution]
  dsimp only [Bind.bind, Except.bind]
  rw [reference]
  dsimp only [Bind.bind, Except.bind]
  rw [ite_eq_left target_eq]
  rfl

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem point_mem {state : State K} {ref : PointRef} {p : Point K}
    (h : point state ref = .ok p) : Object.point p ∈ state := by
  unfold point at h
  split at h
  · cases h; exact List.mem_of_getElem? (by assumption)
  · cases h
  · cases h

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem line_mem {state : State K} {ref : LineRef} {l : Line K}
    (h : line state ref = .ok l) : Object.line l ∈ state := by
  unfold line at h
  split at h
  · cases h; exact List.mem_of_getElem? (by assumption)
  · cases h
  · cases h

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem resolve_available (f : K →+* ℝ) {state : State K}
    (constructed : ∀ o ∈ state, Constructible (o.map f))
    {request : FoldRequest} {input : FoldInput K} (h : resolve state request = .ok input) :
    (input.map f).Available Constructible := by
  have hp {r p} (h : point state r = .ok p) := constructed _ (point_mem h)
  have hl {r l} (h : line state r = .ok l) := constructed _ (line_mem h)
  cases request <;> simp only [resolve, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  all_goals
    repeat first | (split at h) | (cases h)
    simp only [FoldInput.map, FoldInput.Available, FoldInput.objects, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    repeat' apply And.intro
    all_goals first | exact hp (by assumption) | exact hl (by assumption)

private theorem step_sound (f : K →+* ℝ) {state : State K}
    (constructed : ∀ o ∈ state, Constructible (o.map f))
    {instruction : Instruction K} {result : Object K} (h : step state instruction = .ok result) :
    Constructible (result.map f) := by
  cases instruction with
  | fold request selected =>
    simp only [step, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    split at h
    · cases h
    · rename_i input hi
      split at h
      · cases h
      · rename_i certificate hc
        cases h
        exact Constructible.fold _ _ (resolve_available f constructed hi) (certificate.legal f)
  | intersect left right selected =>
    simp only [step, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
    split at h
    · cases h
    · rename_i l hl
      split at h
      · cases h
      · rename_i m hm
        split at h
        · cases h
        · rename_i solution hs
          split at h
          · rename_i equal
            cases h
            subst selected
            exact Constructible.intersection _ _ _ (constructed _ (line_mem hl))
              (constructed _ (line_mem hm)) (solution.property f)
          · cases h

private theorem execute_sound (f : K →+* ℝ) {state : State K}
    (constructed : ∀ o ∈ state, Constructible (o.map f)) (program : Program K) (final : State K)
    (h : execute state program = .ok final) : ∀ o ∈ final, Constructible (o.map f) := by
  induction program generalizing state with
  | nil => cases h; exact constructed
  | cons instruction rest ih =>
    simp only [execute, Bind.bind, Except.bind] at h
    split at h
    · cases h
    · rename_i result hs
      apply ih _ h
      intro o ho
      rcases List.mem_append.mp ho with ho | ho
      · exact constructed o ho
      · simp only [List.mem_singleton] at ho
        subst o
        exact step_sound f constructed hs

/-- Every object in an accepted execution has a geometric construction history. -/
theorem run_sound (f : K →+* ℝ) (program : Program K) (objects : List (Object K))
    (h : run program = .ok objects) : ∀ o ∈ objects, Constructible (o.map f) := by
  apply execute_sound f (program := program) (final := objects) _ h
  intro o ho
  simp [initial] at ho
  rcases ho with rfl | rfl
  · simpa [Object.map] using Constructible.origin
  · simpa [Object.map] using Constructible.unit

/-- Kernel-checked acceptance proves constructibility of the exact submitted target. -/
theorem accepts_sound (f : K →+* ℝ) (program : Program K) (ref : PointRef)
    (coordinate : Coordinate) (target : K)
    (h : accepts program ref coordinate target = true) : ConstructibleNumber (f target) := by
  cases hs : run program with
  | error error => simp [accepts, submit, hs, Bind.bind, Except.bind] at h
  | ok state =>
    cases hp : point state ref with
    | error error => simp [accepts, submit, hs, hp, Bind.bind, Except.bind] at h
    | ok p =>
      by_cases equal : coordinate.get p = target
      · refine ⟨(f p.1, f p.2), run_sound f program state hs _ (point_mem hp), ?_⟩
        cases coordinate with
        | x => exact Or.inl (congrArg f equal).symm
        | y => exact Or.inr (congrArg f equal).symm
      · simp [accepts, submit, hs, hp, equal, Bind.bind, Except.bind] at h

end LeanOrigami.Program
