import LeanOrigami.Widget.Recipe

/-!
# Exact requirements, without the widget or Hex runtime

Kernel-checked examples exercise validity, Boolean logic, and geometry.
Executable assertions cover recipe-reference validation, including its display
metadata. The generic correctness theorems cover every exact ordered field.
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

-- Template validation also processes display strings, including trimmed output
-- names. Test that UI behavior executably; the mathematical checks above remain
-- kernel-checked. Wrongly typed references cannot hide inside NOT, and nested
-- checks may refer to an earlier result but never to a future one.
#eval show IO Unit from do
  let mistyped : RecipeTemplate := {
    parameters := #[⟨"A", .point⟩], requirements := #[.not (.sameLine 0 0)] }
  unless mistyped.validate.toOption.isNone do
    throw (IO.userError "Wrong-kind input reference accepted under NOT")
  let afterFold : RecipeTemplate := {
    parameters := #[⟨"A", .point⟩, ⟨"B", .point⟩],
    steps := [.fold (.axiom1 ⟨0⟩ ⟨1⟩)],
    checks := #[⟨1, 0, .onLine 0 2⟩] }
  unless afterFold.validate.toOption.isSome do
    throw (IO.userError "Valid check after its producing fold rejected")
  let beforeFold := { afterFold with checks := #[⟨0, 0, .onLine 0 2⟩] }
  unless beforeFold.validate.toOption.isNone do
    throw (IO.userError "Forward reference accepted in a nested check")
  IO.println "PASS: typed input conditions and nested-check boundaries"

#print axioms Condition.checkObjects_map_iff
#print axioms Condition.onLine_holds
#print axioms Condition.perpendicular_holds
end LeanOrigami.Tests.Conditions
