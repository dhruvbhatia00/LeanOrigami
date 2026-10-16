import LeanOrigami.Widget.Arithmetic
import LeanOrigami.Widget.Trisection
import LeanOrigami.Construction.Midpoint

/-!
# Public-output rules for the proved recipe library

A library identity fixes the complete editable template. Its relation specifies
inputs, validity, root branches, and exact public outputs. Constructibility is
obtained from the existing execution theorems, without reducing their bodies at
call sites. This module connects templates to mathematics; it performs no root or fold discovery.
-/

namespace LeanOrigami.Widget

/-- Proved library definitions, independent of editable call labels. -/
inductive LibraryRecipe where
  | midpoint
  | arithmetic (operation : ArithmeticOperation)
  | measurement (operation : MeasurementOperation)
  | trisection
  deriving DecidableEq, Repr

namespace LibraryRecipe
variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The complete definition associated with a library theorem. -/
def template : LibraryRecipe → RecipeTemplate
  | .midpoint => midpointRecipe
  | .arithmetic op => arithmeticTemplate op
  | .measurement op => measurementTemplate op
  | .trisection => trisectionTemplate

/-- Recognize only unchanged definitions. The shape filter avoids serializing
large unrelated templates when applying a small recipe. -/
def recognize (recipe : RecipeTemplate) : Option LibraryRecipe :=
  let choices := [midpoint] ++
    ([.add, .sub, .neg, .mul, .inv, .div].map arithmetic) ++
    ([.projectX, .projectY, .transferX, .transferY, .distanceX, .distanceY,
      .sqrt, .cbrt].map measurement) ++ [trisection]
  choices.find? fun choice =>
    let expected := choice.template
    expected.parameters.size == recipe.parameters.size &&
    expected.steps.length == recipe.steps.length && expected.source == recipe.source

/-- Preserve known definitions by name, including inside editable outer recipes.
Recognition still compares the complete unabridged source. -/
def templateSource (recipe : RecipeTemplate) : String :=
  recipe.source fun nested => (recognize nested).map fun identity =>
    s!"LeanOrigami.Widget.LibraryRecipe.template ({repr identity})"

/-- Public trisection outputs, in the template's declared order. The witnesses
remain certificate data; they are not extra constructed inputs or public objects. -/
def trisectionOutputs (vertex first second : Point K) (roots : Trisection.Roots K)
    (valid : roots.Valid vertex first second) : Program.State K :=
  [.point (roots.firstPoint vertex first second),
   .point (roots.secondPoint vertex first second),
   .line (Line.through vertex (roots.firstPoint vertex first second)
     (roots.output_ne vertex first second valid).1),
   .line (Line.through vertex (roots.secondPoint vertex first second)
     (roots.output_ne vertex first second valid).2)]

/-- Exact output relations, including all applicability and root-branch evidence.
The standard frame is part of the input equality, never an additional seed. -/
def Produces : LibraryRecipe → Program.State K → Program.State K → Prop
  | .midpoint, inputs, outputs => Midpoint.Produces inputs outputs
  | .arithmetic op, inputs, outputs =>
    ∃ x y : K, inputs = op.inputs x y ∧ op.Valid x y ∧
      outputs = [.point (op.value x y, 0)]
  | .measurement op, inputs, outputs =>
    ∃ (p q : Point K) (root : K), inputs = op.inputs p q ∧ op.Valid p ∧
      op.Witness p q root ∧ outputs = [.point (op.value p root)]
  | .trisection, inputs, outputs =>
    ∃ (vertex first second : Point K) (roots : Trisection.Roots K)
      (valid : roots.Valid vertex first second),
      inputs = TrisectionRecipe.inputs vertex first second ∧
      outputs = trisectionOutputs vertex first second roots valid

/-- The existing execution proofs establish constructibility of exactly the
public results. Neither their private instructions nor their proof bodies are
replayed when this theorem is applied to a concrete invocation. -/
theorem produces_sound (recipe : LibraryRecipe) (f : K →+* ℝ)
    (inputs outputs : Program.State K) (produces : recipe.Produces inputs outputs)
    (available : ∀ object ∈ inputs, Constructible (object.map f)) :
    ∀ object ∈ outputs, Constructible (object.map f) := by
  cases recipe with
  | midpoint => exact (Midpoint.rule K).sound f inputs outputs produces available
  | arithmetic op =>
    obtain ⟨x, y, rfl, valid, rfl⟩ := produces
    have computed := op.computes x y valid
    intro object member
    obtain rfl := List.mem_singleton.mp member
    exact Program.execute_sound f available _ _ computed.1 _ (Program.point_mem computed.2)
  | measurement op =>
    obtain ⟨p, q, root, rfl, valid, witness, rfl⟩ := produces
    have computed := op.computes p q root valid witness
    intro object member
    obtain rfl := List.mem_singleton.mp member
    exact Program.execute_sound f available _ _ computed.1 _ (Program.point_mem computed.2)
  | trisection =>
    obtain ⟨vertex, first, second, roots, valid, rfl, rfl⟩ := produces
    have constructed := Program.execute_sound f available _ _
      (TrisectionRecipe.executes vertex first second roots valid)
    have selected := TrisectionRecipe.output_objects vertex first second roots valid
    intro object member
    simp only [trisectionOutputs, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact constructed _ (Program.point_mem selected.1)
    · exact constructed _ (Program.point_mem selected.2.1)
    · exact constructed _ (Program.line_mem selected.2.2.1)
    · exact constructed _ (Program.line_mem selected.2.2.2)

/-- The common compositional checker consumes every library family uniformly. -/
def rule (recipe : LibraryRecipe) : Composition.RecipeRule K where
  Produces := recipe.Produces
  sound := recipe.produces_sound

end LibraryRecipe
end LeanOrigami.Widget
