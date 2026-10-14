import LeanOrigami.Widget.Recipe

/-!
# Exact requirements, without the widget or Hex runtime

These examples exercise validity, Boolean logic, geometry, and serialization.
The generic correctness theorems cover every exact ordered field.
-/
namespace LeanOrigami.Tests.Conditions
open LeanOrigami LeanOrigami.Widget

def objects : List (Object Rat) := [.point (0, 0), .point (1, 0),
  .line ⟨0, 1, 0, Or.inr ⟨rfl, rfl⟩⟩, .line ⟨1, 0, 0, Or.inl rfl⟩]

example : (Condition.onLine 1 2).checkObjects objects = true := by decide +kernel
example : (Condition.onLine 1 3).checkObjects objects = false := by decide +kernel
example : (Condition.perpendicular 2 3).checkObjects objects = true := by decide +kernel
example : (Condition.parallel 2 2).checkObjects objects = true := by decide +kernel
example : (Condition.not (.samePoint 0 1)).checkObjects objects = true := by decide +kernel
example : (Condition.collinear 0 0 1).checkObjects objects = true := by decide +kernel
example : (Condition.not (.onLine 0 99)).checkObjects objects = false := by decide +kernel
example : (Condition.not (.onLine 2 0)).checkObjects objects = false := by decide +kernel
example : (Condition.or (.onXAxis 0) (.onXAxis 99)).checkObjects objects = false := by decide +kernel
example : (Condition.not (.eq (.constant 1 0) (.constant 0 1))).checkObjects objects = false := by decide +kernel
example : (Condition.and (.onXAxis 1) (.lt (.constant 0 1) (.component 1 .x))).checkObjects objects = true := by decide +kernel
example : (Condition.le (.component 0 .x) (.constant 0 1)).checkObjects objects = true := by decide +kernel

-- Missing or wrongly typed input references cannot hide inside NOT.
example : (RecipeTemplate.validate {
    parameters := #[⟨"A", .point⟩],
    requirements := #[.not (.sameLine 0 0)] }).toOption.isNone = true := by decide +kernel

-- Nested checks may refer to an earlier result, never a future one.
example : (RecipeTemplate.validate {
    parameters := #[⟨"A", .point⟩, ⟨"B", .point⟩],
    steps := [.fold (.axiom1 ⟨0⟩ ⟨1⟩)],
    checks := #[⟨1, 0, .onLine 0 2⟩] }).toOption.isSome = true := by decide +kernel
example : (RecipeTemplate.validate {
    parameters := #[⟨"A", .point⟩, ⟨"B", .point⟩],
    steps := [.fold (.axiom1 ⟨0⟩ ⟨1⟩)],
    checks := #[⟨0, 0, .onLine 0 2⟩] }).toOption.isNone = true := by decide +kernel

#print axioms Condition.checkObjects_map_iff
#print axioms Condition.onLine_holds
#print axioms Condition.perpendicular_holds
end LeanOrigami.Tests.Conditions
