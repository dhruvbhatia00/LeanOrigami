import LeanOrigamiTests.Runtime
import LeanOrigami.Scalar
import LeanOrigami.Geometry.Reflection
import LeanOrigamiDemos.Subdivision

/-!
# Interpreter integration

Run with `lake lean LeanOrigamiTests/Interpreter.lean`. Lake supplies the
native libraries needed by Hex. Reuse the runtime suite to check the execution
path used by elaborators and widgets, separately from the compiled executable.
These assertions are not proof premises.
-/

#eval main

open LeanOrigami in
-- Check that the public scalar field and geometry actually execute, rather
-- than merely having mathematical instances that support theorem proving.
#eval do
  let a : Scalar := 2 / 3
  unless decide (a + 1 / 3 = 1 ∧ a < 1 ∧ a * a⁻¹ = 1) do
    throw <| IO.userError "FAIL: public scalar arithmetic/order"
  let some line := Line.ofCoefficients? (-2 : Scalar) 0 (-2)
    | throw <| IO.userError "FAIL: valid line rejected"
  unless decide (line.a = 1 ∧ line.b = 0 ∧ line.c = 1) do
    throw <| IO.userError "FAIL: line normalization"
  unless decide (line.reflect (0, 0) = (2, 0)) do
    throw <| IO.userError "FAIL: exact reflection"
  match Line.ofCoefficients? (0 : Scalar) 0 1 with
  | some _ => throw <| IO.userError "FAIL: invalid normal accepted"
  | none => pure ()
  IO.println "PASS: public scalar arithmetic/order, normalization, reflection, and invalid-line rejection"

open LeanOrigami LeanOrigamiDemos.Subdivision in
-- This is the same saved recipe as the kernel-certified rational demo, now
-- executed using Hex. Proof-bearing state does not make execution noncomputable.
#eval do
  let recipe := program Scalar
  for (index, value) in [(5, (1/2 : Scalar)), (7, 1/4), (9, 3/4)] do
    unless Program.accepts recipe ⟨index⟩ .x value do
      throw <| IO.userError "FAIL: Hex construction or target certification"
  unless !(Program.accepts recipe ⟨9⟩ .x (1/4)) do
    throw <| IO.userError "FAIL: wrong target accepted"
  let forged : Program Scalar :=
    [.fold (.axiom1 ⟨0⟩ ⟨1⟩) ⟨1, 0, 0, Or.inl rfl⟩]
  match Program.run forged with
  | .error .incorrectOutput => pure ()
  | _ => throw <| IO.userError "FAIL: forged Hex output accepted"
  IO.println "PASS: Hex construction replay, all three exact targets, and forged-output rejection"
