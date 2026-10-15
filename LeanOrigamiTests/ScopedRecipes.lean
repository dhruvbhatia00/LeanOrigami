import LeanOrigami.Widget.Session

/-!
# Scoped editing and midpoint theorem dispatch

These executable checks cover editor behavior, not proof certification. The
mathematical certificate is tested independently in `Composition.lean`.
-/

namespace LeanOrigami.Tests.ScopedRecipes
open LeanOrigami Widget

private def get {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def require (message : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError message)
  IO.println ("PASS: " ++ message)

/-- Two calls, one primitive, inspection, editing fallback, and sample replay. -/
def run : IO Unit := do
  let half ← get (({} : Session).useRecipe "Midpoint" midpointRecipe #[0,1])
  require "one public midpoint, no intermediate creases" (half.objects.length == 3 && half.program.length == 1)
  let quarter ← get (half.useRecipe "Midpoint again" midpointRecipe #[0,2])
  require "nested public result is one quarter" ((← get (quarter.selected 3 .x)) == (1/4 : Scalar))
  require "private indices cannot be used by the caller"
    ((quarter.preview (.axiom1 ⟨0⟩ ⟨4⟩)).toOption.isNone)
  let preview ← get (quarter.preview (.axiom1 ⟨0⟩ ⟨3⟩))
  let finished ← get (preview.choose 0)
  require "ordinary folds consume public recipe results" (finished.objects.length == 5)
  let inspected ← get (half.inspect 0)
  require "inspection reconstructs the three private instructions"
    (inspected.program.length == 3 && inspected.objects.length == 5)
  require "inspection does not modify the caller" (half.objects.length == 3)
  let undone ← get quarter.undo
  require "undo removes one complete public call" (undone.objects.length == 3 && undone.program.length == 1)
  let template ← get (quarter.template #[⟨"A", .point⟩, ⟨"B", .point⟩] 3)
  require "saved recipe retains nested calls" (template.steps.length == 2)
  let seeds : Program.State Scalar := [.point (2,2), .point (6,6)]
  let changed ← get (({ seeds, objects := seeds } : Session).useRecipe "" template #[0,1])
  require "new samples rediscover nested outputs" ((← get (changed.selected 3 .x)) == (3 : Scalar))
  let edited := { midpointRecipe with parameters := #[⟨"Changed A", .point⟩, ⟨"B", .point⟩] }
  require "edited definition loses optimized theorem dispatch" (!Execution.isMidpoint edited)
  let fallback ← get (({} : Session).useRecipe "Edited midpoint" edited #[0,1])
  let some (Execution.Step.call (K := Scalar) _ _ _ _ body) := fallback.program[0]?
    | throw (IO.userError "Expected a retained call")
  require "edited recipe retains primitive fallback history" (body.length == 3)
  require "fallback still exposes only the result" (fallback.objects.length == 3 &&
    (← get (fallback.selected 2 .x)) == (1/2 : Scalar))
  require "coincident midpoint inputs are rejected"
    ((({} : Session).useRecipe "Midpoint" midpointRecipe #[0,0]).toOption.isNone)

end LeanOrigami.Tests.ScopedRecipes

#eval LeanOrigami.Tests.ScopedRecipes.run
