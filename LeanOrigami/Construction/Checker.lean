import LeanOrigami.Solvers.Certified

/-!
# Program checking and construction soundness

An append-only state stores exact objects with construction histories.
Resolution can only retrieve earlier certified objects. Each instruction
checks its saved output against the primitive relation before extending the
state. `run` exposes ordinary data; `run_sound` states its geometric guarantee.
Real embeddings occur only under proof quantifiers, never as runtime inputs.
-/

namespace LeanOrigami
namespace Program
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A stored object with a real construction history. Proofs are erased at runtime. -/
abbrev CertifiedObject (K : Type*) [Field K] :=
  {o : Object K // ∀ f : K →+* ℝ, Constructible (o.map f)}

/-- An append-only list, whose indices remain stable as instructions execute. -/
abbrev State (K : Type*) [Field K] := List (CertifiedObject K)

/-- The only objects available without performing an instruction. -/
def initial : State K :=
  [⟨.point (0, 0), by intro f; simpa [Object.map] using Constructible.origin⟩,
   ⟨.point (1, 0), by intro f; simpa [Object.map] using Constructible.unit⟩]

/-- Resolve a point reference and retain its construction evidence. -/
def point (state : State K) (ref : PointRef) :
    Except ConstructionError {p : Point K // ∀ f : K →+* ℝ, Constructible (.point (f p.1, f p.2))} :=
  match state[ref.index]? with
  | none => .error (.missingReference ref.index)
  | some ⟨.point p, hp⟩ => .ok ⟨p, hp⟩
  | some ⟨.line _, _⟩ => .error (.expectedPoint ref.index)

/-- Resolve a line reference and retain its construction evidence. -/
def line (state : State K) (ref : LineRef) :
    Except ConstructionError {l : Line K // ∀ f : K →+* ℝ, Constructible (.line (l.map f))} :=
  match state[ref.index]? with
  | none => .error (.missingReference ref.index)
  | some ⟨.line l, hl⟩ => .ok ⟨l, hl⟩
  | some ⟨.point _, _⟩ => .error (.expectedLine ref.index)

/-- Resolve every required input before checking the requested geometric relation. -/
def resolve (state : State K) (request : FoldRequest) :
    Except ConstructionError {input : FoldInput K // ∀ f : K →+* ℝ, (input.map f).Available Constructible} := do
  match request with
  | .axiom1 rp rq =>
      let p ← point state rp
      let q ← point state rq
      return ⟨.axiom1 p.val q.val, by
        intro f
        simpa [FoldInput.Available, FoldInput.objects, FoldInput.map, Prod.map] using
          And.intro (p.property f) (q.property f)⟩
  | .axiom2 rp rq =>
      let p ← point state rp
      let q ← point state rq
      return ⟨.axiom2 p.val q.val, by
        intro f
        simpa [FoldInput.Available, FoldInput.objects, FoldInput.map, Prod.map] using
          And.intro (p.property f) (q.property f)⟩
  | .axiom3 rl rm =>
      let l ← line state rl
      let m ← line state rm
      return ⟨.axiom3 l.val m.val, by
        intro f
        simpa [FoldInput.Available, FoldInput.objects, FoldInput.map, Prod.map] using
          And.intro (l.property f) (m.property f)⟩
  | .axiom4 rp rl =>
      let p ← point state rp
      let l ← line state rl
      return ⟨.axiom4 p.val l.val, by
        intro f
        simpa [FoldInput.Available, FoldInput.objects, FoldInput.map, Prod.map] using
          And.intro (p.property f) (l.property f)⟩
  | .axiom5 rp rq rl =>
      let p ← point state rp
      let q ← point state rq
      let l ← line state rl
      return ⟨.axiom5 p.val q.val l.val, by
        intro f
        simpa [FoldInput.Available, FoldInput.objects, FoldInput.map, Prod.map] using
          And.intro (p.property f) (And.intro (q.property f) (l.property f))⟩
  | .axiom6 rp rq rl rm =>
      let p ← point state rp
      let q ← point state rq
      let l ← line state rl
      let m ← line state rm
      return ⟨.axiom6 p.val q.val l.val m.val, by
        intro f
        simpa [FoldInput.Available, FoldInput.objects, FoldInput.map, Prod.map] using
          And.intro (p.property f) (And.intro (q.property f) (And.intro (l.property f) (m.property f)))⟩
  | .axiom7 rp rl rm =>
      let p ← point state rp
      let l ← line state rl
      let m ← line state rm
      return ⟨.axiom7 p.val l.val m.val, by
        intro f
        simpa [FoldInput.Available, FoldInput.objects, FoldInput.map, Prod.map] using
          And.intro (p.property f) (And.intro (l.property f) (m.property f))⟩

/-- Check one instruction, including the exact selected result. -/
def step (state : State K) (instruction : Instruction K) :
    Except ConstructionError (CertifiedObject K) := do
  match instruction with
  | .fold request selected =>
      let input ← resolve state request
      let certificate ← Solver.fold input.val selected
      return ⟨.line selected, by
        intro f
        exact Constructible.fold _ _ (input.property f) (certificate.legal f)⟩
  | .intersect left right selected =>
      let l ← line state left
      let m ← line state right
      let solution ← Solver.intersect l.val m.val
      if h : selected = solution.val then
        return ⟨.point selected, by
          intro f
          rw [h]
          exact Constructible.intersection _ _ _ (l.property f) (m.property f) (solution.property f)⟩
      else throw .incorrectOutput

/-- Execute a suffix using only the certified preceding state. -/
def execute (state : State K) : Program K → Except ConstructionError (State K)
  | [] => .ok state
  | instruction :: rest => do
      let result ← step state instruction
      execute (state ++ [result]) rest

/-- Certify a saved construction from the fixed seeds. -/
def certify (program : Program K) : Except ConstructionError (State K) :=
  execute initial program

/-- Ordinary execution result, with proof fields removed from the public data. -/
def run (program : Program K) : Except ConstructionError (List (Object K)) :=
  (certify program).map (List.map Subtype.val)

/-- Every object in any accepted program has an independent geometric construction history. -/
theorem run_sound (f : K →+* ℝ) (program : Program K) (objects : List (Object K))
    (h : run program = .ok objects) : ∀ o ∈ objects, Constructible (o.map f) := by
  unfold run at h
  cases hc : certify program with
  | error e => simp [hc, Except.map] at h
  | ok state =>
      simp [hc, Except.map] at h
      subst objects
      intro o ho
      obtain ⟨certified, _, rfl⟩ := List.mem_map.mp ho
      exact certified.property f

/-- Check a final point reference and exact coordinate claim. The result carries
both provenance and equality, so a valid unrelated construction cannot close the goal. -/
def submit (program : Program K) (ref : PointRef)
    (coordinate : Coordinate) (target : K) : Except ConstructionError
      {p : Point K // (∀ f : K →+* ℝ, Constructible (.point (f p.1, f p.2))) ∧
        coordinate.get p = target} := do
  let state ← certify program
  let p ← point state ref
  if h : coordinate.get p.val = target then
    return ⟨p.val, p.property, h⟩
  else throw .targetMismatch

/-- Proof-free success flag for a complete submission, including target identification. -/
def accepts (program : Program K) (ref : PointRef)
    (coordinate : Coordinate) (target : K) : Bool :=
  match submit program ref coordinate target with
  | .ok _ => true
  | .error _ => false

/-- Kernel-checkable acceptance establishes constructibility of the exact requested number. -/
theorem accepts_sound (f : K →+* ℝ) (program : Program K) (ref : PointRef)
    (coordinate : Coordinate) (target : K)
    (h : accepts program ref coordinate target = true) : ConstructibleNumber (f target) := by
  unfold accepts at h
  cases hs : submit program ref coordinate target with
  | error e => simp [hs] at h
  | ok p =>
      refine ⟨(f p.val.1, f p.val.2), p.property.1 f, ?_⟩
      rcases coordinate with _ | _
      · exact Or.inl (congrArg f p.property.2).symm
      · exact Or.inr (congrArg f p.property.2).symm

end Program
end LeanOrigami
