import LeanOrigami.Widget.Session
import Lean

/-!
# Standalone recipe workspace data

A workspace's exact samples are for exploration only. Its registered template
contains no samples. Native evaluation here opens data for the editor; it is
never evidence for the construction checker or a theorem about a recipe.
-/

namespace LeanOrigami.Widget
open Lean Meta

/-- Named sample objects become the typed parameters of a standalone recipe. -/
abbrev RecipeSamples := List (String × Object Scalar)

/-- A recipe visible in the current Lean environment. -/
structure NamedRecipe where
  id : String
  name : String
  template : RecipeTemplate

/-- Menu data omits both sample coordinates and the executable template. -/
structure RecipeMenuItem where
  id : String
  name : String
  parameters : Array RecipeParameter
  deriving ToJson, FromJson

/-- Capture the command's original spelling and elaborated data for reopening
and versioned replacement. The template declaration itself contains no samples. -/
structure WorkspaceContext where
  sourcePrefix : String
  samples : Expr
  recipe : Expr
  parameters : Array RecipeParameter

initialize recipeAttribute : TagAttribute ←
  registerTagAttribute `origami_recipe "Offer a RecipeTemplate declaration in origami widgets."

private unsafe def readRecipeUnsafe (expression : Expr) : MetaM RecipeTemplate :=
  evalExpr RecipeTemplate (mkConst ``RecipeTemplate) expression

/-- Evaluate template data for discovery, never a proof. -/
@[implemented_by readRecipeUnsafe]
opaque readRecipe (expression : Expr) : MetaM RecipeTemplate

private unsafe def readSamplesUnsafe (expression : Expr) : MetaM RecipeSamples :=
  evalExpr RecipeSamples (mkConst ``RecipeSamples) expression

/-- Load exact sample objects outside the certification path. -/
@[implemented_by readSamplesUnsafe]
opaque readSamples (expression : Expr) : MetaM RecipeSamples

private unsafe def readGroupsUnsafe (expression : Expr) : MetaM (Array RecipeGroup) :=
  evalExpr (Array RecipeGroup) (mkApp (mkConst ``Array [0]) (mkConst ``RecipeGroup)) expression

/-- History annotations are display data, separate from a saved proof certificate. -/
@[implemented_by readGroupsUnsafe]
opaque readGroups (expression : Expr) : MetaM (Array RecipeGroup)

/-- Collect the built-in and earlier registered recipes, checking their types
and reference structure before presenting them as operations. -/
def recipeLibrary : MetaM (Array NamedRecipe) := do
  let mut library := #[NamedRecipe.mk "recipe:midpoint" "Midpoint (distinct points)" midpointRecipe]
  let env ← getEnv
  let mut names := (recipeAttribute.ext.getState env).toArray
  for i in [:env.header.moduleNames.size] do
    names := names ++ recipeAttribute.ext.getModuleEntries env i
  for name in names do
    let value := mkConst name
    unless ← isDefEq (← inferType value) (mkConst ``RecipeTemplate) do
      throwError "{name}: origami_recipe requires a RecipeTemplate declaration."
    let recipe ← readRecipe value
    match recipe.validate with
    | .error message => throwError "Invalid recipe {name}: {message}"
    | .ok _ => pure ()
    library := library.push ⟨s!"recipe:{name}", name.toString, recipe⟩
  return library

/-- Reopen on samples, recomputing every result. Ambiguous operations pause for
fresh choices, as they do on any other invocation. -/
def openWorkspace (workspace : WorkspaceContext) : MetaM (Except String Session) := do
  let samples ← readSamples workspace.samples
  let recipe ← readRecipe workspace.recipe
  return do
    let seeds := samples.map Prod.snd
    unless recipe.parameters.map (fun p => (p.name, p.kind)) ==
        workspace.parameters.map (fun p => (p.name, p.kind)) do
      throw "The saved recipe parameters do not match the sample inputs."
    let session : Session := { seeds, objects := seeds }
    session.useRecipe "" recipe (Array.range seeds.length)

end LeanOrigami.Widget
