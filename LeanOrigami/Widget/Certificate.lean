import LeanOrigami.Widget.Execution
import LeanOrigami.Widget.LibraryRules

/-!
# Certificates tied to saved recipe definitions

Every call's rule is derived from its saved definition and private history.
Library calls prove equality with a complete known definition and reuse its
public-output theorem. Fallback calls certify their local execution, including
nested calls. The original midpoint rule remains readable in earlier saves. Editable names never select mathematical rules.
-/

namespace LeanOrigami.Widget.Execution
open LeanOrigami.Composition
section Generic
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A call either uses the registered midpoint theorem or certifies its recorded
body. The latter checks the operation sequence against the saved template;
arbitrary output specifications still require their own recipe theorems. -/
def callRule (recipe : RecipeTemplate) (body : History K)
    (children : Registry K) : RecipeRule K where
  Produces inputs outputs :=
    (recipe = midpointRecipe ∧ Midpoint.Produces inputs outputs) ∨
    ∃ final, body.map Step.operation = recipe.steps ∧
      Certified children inputs (construction body) final ∧
      select final recipe.publicOutputs.toList = .ok outputs
  sound f inputs outputs produced available := by
    rcases produced with ⟨_, midpoint⟩ | ⟨final, _, certified, selected⟩
    · exact (Midpoint.rule K).sound f inputs outputs midpoint available
    · exact fun object member => certified.sound f available object
        (select_mem selected object member)

/-- Lookup is deliberately simple and reducible for small structural proofs. -/
def lookupRules (rules : List (String × RecipeRule K)) : Registry K :=
  fun identity => (rules.find? (fun entry => entry.1 == identity)).map Prod.snd

end Generic

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A compact call names a complete library definition and supplies its exact
public-output relation. Matching the definition is part of the checked proof;
editable display names do not select a theorem. -/
def libraryRule (recipe : RecipeTemplate) : RecipeRule K where
  Produces inputs outputs :=
    ∃ known : LibraryRecipe, recipe = known.template ∧ known.Produces inputs outputs
  sound f inputs outputs produced available := by
    obtain ⟨known, _, produced⟩ := produced
    exact (known.rule (K := K)).sound f inputs outputs produced available


mutual

/-- A node derives its own rule from its saved definition and child history. -/
def stepRule (step : Step K) : Option (RecipeRule K) :=
  match step with
  | .primitive _ => none
  | .library _ recipe _ _ => some (libraryRule recipe)
  | .call _ recipe _ _ body => some (callRule recipe body (lookupRules (rules body)))
termination_by structural step

/-- Derive rules recursively from the same saved call tree used for display. -/
def rules (history : History K) (index : Nat := 0) : List (String × RecipeRule K) :=
  match history with
  | [] => []
  | step :: rest =>
    match stepRule step with
    | none => rules rest (index + 1)
    | some rule => (toString index, rule) :: rules rest (index + 1)
termination_by structural history

end

/-- The fixed registry of a saved construction. The exporter cannot substitute
an unrelated sound rule for the recipe the user sees. -/
def registry (history : History K) : Registry K := lookupRules (rules history)

end LeanOrigami.Widget.Execution
