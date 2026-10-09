import LeanOrigami.Construction.Program

/-!
# Reusable primitive programs

A recipe numbers its arguments first, followed by its intermediate objects.
Expansion replaces argument references and shifts intermediate references to
the end of an existing program. It introduces no instruction or trusted rule:
the result is an ordinary program for the construction checker.
-/

namespace LeanOrigami

/-- Rename references without changing a fold operation or its input roles. -/
def FoldRequest.remap (f : Nat → Nat) : FoldRequest → FoldRequest
  | .axiom1 p q => .axiom1 ⟨f p.index⟩ ⟨f q.index⟩
  | .axiom2 p q => .axiom2 ⟨f p.index⟩ ⟨f q.index⟩
  | .axiom3 l m => .axiom3 ⟨f l.index⟩ ⟨f m.index⟩
  | .axiom4 p l => .axiom4 ⟨f p.index⟩ ⟨f l.index⟩
  | .axiom5 p q l => .axiom5 ⟨f p.index⟩ ⟨f q.index⟩ ⟨f l.index⟩
  | .axiom6 p q l m => .axiom6 ⟨f p.index⟩ ⟨f q.index⟩ ⟨f l.index⟩ ⟨f m.index⟩
  | .axiom7 p l m => .axiom7 ⟨f p.index⟩ ⟨f l.index⟩ ⟨f m.index⟩

/-- Rename all references while retaining the exact selected output. -/
def Instruction.remap {K : Type*} [Zero K] [One K] (f : Nat → Nat) : Instruction K → Instruction K
  | .fold request selected => .fold (request.remap f) selected
  | .intersect l m selected => .intersect ⟨f l.index⟩ ⟨f m.index⟩ selected

/-- Renaming a saved operation twice is the same as composing the substitutions. -/
theorem FoldRequest.remap_comp (f g : Nat → Nat) (request : FoldRequest) :
    (request.remap f).remap g = request.remap (g ∘ f) := by cases request <;> rfl

/-- Composed substitutions preserve the selected exact output. -/
theorem Instruction.remap_comp {K : Type*} [Zero K] [One K]
    (f g : Nat → Nat) (instruction : Instruction K) :
    (instruction.remap f).remap g = instruction.remap (g ∘ f) := by
  cases instruction with
  | fold request selected => simp only [remap, FoldRequest.remap_comp]
  | intersect l m selected => rfl

/-- A local program with a fixed number of externally supplied objects. -/
structure Recipe (K : Type*) [Zero K] [One K] (arity : Nat) where
  steps : Program K
  output : PointRef

namespace Recipe

/-- Map an argument to its supplied object and an intermediate to its new slot. -/
def relocate {arity : Nat} (arguments : Fin arity → Nat) (base index : Nat) : Nat :=
  if h : index < arity then arguments ⟨index, h⟩ else base + (index-arity)

/-- Every reference to an earlier local object remains an earlier reference,
provided the supplied arguments already exist. -/
theorem relocate_lt {arity : Nat} (arguments : Fin arity → Nat) (base step index : Nat)
    (ha : ∀ i, arguments i < base) (hi : index < arity+step) :
    relocate arguments base index < base+step := by
  unfold relocate
  split
  · have h := ha ⟨index, by assumption⟩
    omega
  · omega

/-- Expand a recipe at the next free object index. Argument kinds and values
are still checked by ordinary reference resolution and geometric replay. -/
def expand {K : Type*} [Zero K] [One K] {arity : Nat}
    (recipe : Recipe K arity) (arguments : Fin arity → Nat) (base : Nat) : Program K :=
  recipe.steps.map (Instruction.remap (relocate arguments base))

/-- Locate the result of an expanded recipe in the common object list. -/
def result {K : Type*} [Zero K] [One K] {arity : Nat}
    (recipe : Recipe K arity) (arguments : Fin arity → Nat) (base : Nat) : PointRef :=
  ⟨relocate arguments base recipe.output.index⟩

/-- Append a recipe to a program that starts from the two standard seeds,
returning both the expanded program and its relocated output reference. -/
def append {K : Type*} [Zero K] [One K] {arity : Nat}
    (recipe : Recipe K arity) (program : Program K) (arguments : Fin arity → Nat) :
    Program K × PointRef :=
  let base := program.length+2
  (program ++ recipe.expand arguments base, recipe.result arguments base)

/-- Expansion changes references, not the number of primitive steps. -/
theorem expand_length {K : Type*} [Zero K] [One K] {arity : Nat}
    (recipe : Recipe K arity) (arguments : Fin arity → Nat) (base : Nat) :
    (recipe.expand arguments base).length = recipe.steps.length := List.length_map _

end Recipe

/-- A small builder assigns the next object reference when emitting a primitive.
The accumulated list is reversed for constant-time insertion. -/
structure RecipeBuilder.State (K : Type*) [Zero K] [One K] where
  next : Nat
  reversed : Program K

/-- Pure recipe assembly; this does not execute or certify the saved geometry. -/
abbrev RecipeBuilder (K : Type) [Zero K] [One K] := StateM (RecipeBuilder.State K)

namespace RecipeBuilder
variable {K : Type} [Zero K] [One K]

/-- Append one exact selected fold and return its line reference. -/
def fold (request : FoldRequest) (selected : Line K) : RecipeBuilder K LineRef := do
  let state : State K ← get
  set ({next := state.next+1, reversed := .fold request selected :: state.reversed} : State K)
  return ⟨state.next⟩

/-- Append one exact selected intersection and return its point reference. -/
def intersect (l m : LineRef) (selected : Point K) : RecipeBuilder K PointRef := do
  let state : State K ← get
  set ({next := state.next+1, reversed := .intersect l m selected :: state.reversed} : State K)
  return ⟨state.next⟩

/-- Expand an existing recipe inside a larger recipe. Intermediate references
are relocated to the builder's next slot, just as when appending to a program. -/
def use {arity : Nat} (recipe : Recipe K arity) (arguments : Fin arity → Nat) :
    RecipeBuilder K PointRef := do
  let state : State K ← get
  let steps := recipe.expand arguments state.next
  set ({next := state.next + steps.length, reversed := steps.reverse ++ state.reversed} : State K)
  return recipe.result arguments state.next

/-- Finish assembly, reserving the initial local indices for arguments. -/
def build (arity : Nat) (body : RecipeBuilder K PointRef) : Recipe K arity :=
  let (output, state) := body.run ⟨arity, []⟩
  ⟨state.reversed.reverse, output⟩

end RecipeBuilder
end LeanOrigami
