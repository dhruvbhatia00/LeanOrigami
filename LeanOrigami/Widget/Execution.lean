import LeanOrigami.Widget.Recipe
import LeanOrigami.Construction.Midpoint

/-!
# Recorded calls with private histories

An execution stores primitive selections and scoped recipe invocations. A call's
body is inspection/fallback data; only its public outputs are appended to the
caller. Source templates retain nested calls, so editing or changing samples
rediscovers them without carrying old coordinates into a new construction.
-/

namespace LeanOrigami.Widget
namespace Execution

/-- Concrete editing history. A proved recipe may omit its internal execution;
a library call keeps only public geometry, while its template supplies the
visual explanation on demand. Legacy calls remain readable. -/
inductive Step (K : Type*) [Field K] where
  | primitive (instruction : Instruction K)
  | library (name : String) (recipe : RecipeTemplate) (arguments : Array Nat)
      (outputs : Program.State K)
  | call (name : String) (recipe : RecipeTemplate) (arguments : Array Nat)
      (outputs : Program.State K) (body : List (Step K))

/-- An ordered sequence in one public reference scope. -/
abbrev History (K : Type*) [Field K] := List (Step K)

/-- Selected outputs are exact data; their constructibility is proved separately. -/
def Step.outputs {K : Type*} [Field K] : Step K → Program.State K
  | .primitive (.fold _ line) => [.line line]
  | .primitive (.intersect _ _ point) => [.point point]
  | .library _ _ _ outputs | .call _ _ _ outputs _ => outputs

/-- Erase old sample coordinates while retaining nested calls and local scopes. -/
def Step.operation {K : Type*} [Field K] : Step K → RecipeOperation
  | .primitive instruction => RecipeOperation.ofInstruction instruction
  | .library name recipe arguments _ | .call name recipe arguments _ _ =>
    .call name recipe arguments

/-- Shared editor metadata. Library explanations are reconstructed from their
saved definition; fallback calls retain their actual private selections. -/
def Step.callData {K : Type*} [Field K] :
    Step K → Option (String × RecipeTemplate × Array Nat × History K)
  | .primitive _ => none
  | .library name recipe arguments _ => some (name, recipe, arguments, [])
  | .call name recipe arguments _ body => some (name, recipe, arguments, body)

/-- Import a legacy primitive history without changing any object index. -/
def ofProgram {K : Type*} [Field K] (program : Program K) : History K :=
  program.map Step.primitive

/-- The exact public proof trace. Identity paths are local to this saved history;
certificate generation binds each path to the corresponding recipe rule. -/
def construction {K : Type*} [Field K] (history : History K) (scope : String := "") :
    Composition.Construction K :=
  history.zipIdx.map fun (step, index) => match step with
  | .primitive instruction => .primitive instruction
  | .library _ _ arguments outputs | .call _ _ arguments outputs _ =>
    .call (scope ++ toString index) arguments.toList outputs

/-- Reconstruct public objects without expanding calls. This is a display/data
operation, never evidence that a selected recipe output is correct. -/
def replay {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (seeds : Program.State K) (history : History K) : Except ConstructionError (Program.State K) :=
  Composition.replay seeds (construction history)

/-- History groups refer to public node boundaries, not internal fold offsets. -/
def groups {K : Type*} [Field K] (seedCount : Nat) (history : History K) : Array RecipeGroup := Id.run do
  let mut base := seedCount
  let mut groups := #[]
  for (step, index) in history.zipIdx do
    if let some (name, recipe, arguments, _) := step.callData then
      let indices := recipe.publicOutputs
      let names := recipe.namedOutputs.map fun output =>
        { output with index := base + (indices.findIdx? (· == output.index)).getD 0 }
      groups := groups.push ⟨name, index, 1, arguments, ⟨base, names⟩⟩
    base := base + step.outputs.length
  return groups

/-- The midpoint optimization applies only to the complete unchanged definition.
Display names do not choose theorem associations. -/
def isMidpoint (recipe : RecipeTemplate) : Bool := recipe.source == midpointRecipe.source


end Execution
end LeanOrigami.Widget
