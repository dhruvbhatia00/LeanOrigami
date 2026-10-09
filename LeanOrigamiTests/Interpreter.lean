import LeanOrigami.Scalar.FoldDiscovery
import LeanOrigami.Geometry.Reflection
import LeanOrigamiDemos.Subdivision
import LeanOrigamiDemos.OffAxis
import LeanOrigamiDemos.AllFolds
import LeanOrigamiDemos.Arithmetic

/-!
# Interpreter integration

Run with `lake lean LeanOrigamiTests/Interpreter.lean`. Lake supplies the
native libraries needed by Hex. Check the public scalar and construction
APIs through the execution path used by elaborators and widgets. The older
arithmetic/root suite remains in Runtime.lean and the full validation script.
These assertions are not proof premises.
-/

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

open LeanOrigami LeanOrigami.Scalar in
-- Exercise the real-root adapter itself, including multiplicity and degree loss.
#eval do
  let finite (coefficients : List Scalar) : IO (List Scalar) := do
    match realRoots (polynomial coefficients) with
    | .all => throw <| IO.userError "FAIL: nonzero polynomial classified as all roots"
    | .finite values => return values
  let check (label : String) (condition : Bool) : IO Unit := do
    unless condition do throw <| IO.userError s!"FAIL: {label}"
  match realRoots (polynomial [0, 0, 0]) with
  | .all => pure ()
  | .finite _ => throw <| IO.userError "FAIL: zero polynomial classified as finite"
  check "nonzero constant" ((← finite [1]).isEmpty)
  check "no real roots" ((← finite [1, 0, 1]).isEmpty)
  let repeated ← finite [1, -2, 1]
  check "double root appears once" (decide (repeated = [1]))
  let linear ← finite [-1, 1, 0, 0]
  check "leading zeros lower the degree" (decide (linear = [1]))
  let squareRoots ← finite [-2, 0, 1]
  check "both square roots" (squareRoots.length == 2 &&
    squareRoots.all (fun r => decide (r*r = 2)))
  let some sqrtTwo := squareRoots.find? (fun r => decide (0 < r))
    | throw <| IO.userError "FAIL: missing positive square root"
  let fourthRoots ← finite [-sqrtTwo, 0, 1]
  check "irrational coefficients" (fourthRoots.length == 2 &&
    fourthRoots.all (fun r => decide (r*r = sqrtTwo)))
  let cubeRoots ← finite [-2, 0, 0, 1]
  check "complex roots filtered out" (cubeRoots.length == 1 &&
    cubeRoots.all (fun r => decide (r^3 = 2)))
  for upper in [true, false] do
    check "Hex off-axis branch replay" (Program.accepts
      (LeanOrigami.Basis.program Scalar upper) ⟨8⟩ .y
      (LeanOrigami.Basis.height Scalar upper))
  IO.println "PASS: real-root classification, repeated roots, degree drops, irrational coefficients, and both Hex fold branches"

open LeanOrigami in
-- Native execution checks the discovery API; the library proves its semantics.
#eval do
  let check (label : String) (ok : Bool) : IO Unit :=
    unless ok do throw <| IO.userError s!"FAIL: {label}"
  let finite (label : String) (input : FoldInput Scalar) (count : Nat) : IO (List (Line Scalar)) := do
    let some choices := Scalar.folds input
      | throw <| IO.userError s!"FAIL: {label}: unexpectedly infinite"
    check s!"{label}: choice count" (choices.length == count)
    for crease in choices do
      match Solver.fold input crease with
      | .ok _ => pure ()
      | .error _ => throw <| IO.userError s!"FAIL: {label}: discovery/replay disagree"
    return choices
  let infinite (label : String) (input : FoldInput Scalar) : IO Unit :=
    match Scalar.folds input with
    | none => pure ()
    | some _ => throw <| IO.userError s!"FAIL: {label}: expected infinite family"
  let xAxis : Line Scalar := Line.horizontal 0
  let yAxis : Line Scalar := Line.chart 0 0
  let _ ← finite "rule 1" (.axiom1 (0, 0) (1, 0)) 1
  let _ ← finite "rule 2" (.axiom2 (0, 0) (1, 0)) 1
  let _ ← finite "intersecting lines" (.axiom3 xAxis yAxis) 2
  let _ ← finite "parallel lines" (.axiom3 xAxis (Line.horizontal 2)) 1
  infinite "coincident lines" (.axiom3 xAxis xAxis)
  let irrationalBisectors ← finite "irrational bisectors" (.axiom3 xAxis (Line.chart 1 0)) 2
  check "bisector polynomial" (irrationalBisectors.all (fun c => decide (c.b^2-2*c.b-1 = 0)))
  let _ ← finite "rule 4" (.axiom4 (0, 0) xAxis) 1
  let _ ← finite "two circle landings" (.axiom5 (1, 0) (0, 0) yAxis) 2
  let _ ← finite "tangent landing" (.axiom5 (1, 0) (0, 0) (Line.chart 0 1)) 1
  let _ ← finite "missed circle" (.axiom5 (1, 0) (0, 0) (Line.chart 0 2)) 0
  let _ ← finite "coincident fixed point off target" (.axiom5 (1, 0) (1, 0) yAxis) 0
  infinite "coincident fixed point on target" (.axiom5 (0, 0) (0, 0) yAxis)
  let one ← finite "rule 6: one crease"
    (.axiom6 (0, 1) (0, 0) (Line.horizontal (-1)) xAxis) 1
  check "horizontal crease after degree drop" (decide (one = [Line.horizontal 0]))
  let two ← finite "rule 6: repeated root and two creases"
    (.axiom6 (0, 1) (0, 0) (Line.horizontal 1) yAxis) 2
  check "two distinct rule-6 choices" (decide (Line.chart 0 0 ∈ two ∧ Line.horizontal 1 ∈ two))
  let three ← finite "rule 6: three creases"
    (.axiom6 (0, 1) (0, -1) (Line.horizontal (-1)) yAxis) 3
  check "three exact rule-6 choices" (decide
    (Line.chart 1 (-1) ∈ three ∧ Line.chart (-1) 1 ∈ three ∧ Line.horizontal 0 ∈ three))
  -- These have nonzero cubic leading coefficient, so none of their solutions
  -- can be hidden in the separate horizontal chart.
  let _ ← finite "genuine cubic: one irrational crease"
    (.axiom6 (0, 1) (2, 0) (Line.horizontal (-1)) yAxis) 1
  let repeated ← finite "genuine cubic: repeated root and two creases"
    (.axiom6 (0, 1) (-2, -1) (Line.horizontal (-1)) yAxis) 2
  check "repeated cubic root counted once" (decide
    (Line.chart 1 (-1) ∈ repeated ∧ Line.chart (-1) 1 ∈ repeated))
  let _ ← finite "genuine cubic: three irrational creases"
    (.axiom6 (0, 1) (2, -2) (Line.horizontal (-1)) yAxis) 3
  let _ ← finite "rule 6: incompatible parallel targets"
    (.axiom6 (0, 0) (0, 0) (Line.horizontal 1) (Line.horizontal 2)) 0
  infinite "rule 6: free direction" (.axiom6 (0, 0) (0, 1) xAxis (Line.horizontal 1))
  infinite "rule 6: zero eliminant" (.axiom6 (0, 1) (0, 1) xAxis xAxis)
  let _ ← finite "rule 7: unique crease" (.axiom7 (0, 0) (Line.chart 0 2) xAxis) 1
  let _ ← finite "rule 7: no crease" (.axiom7 (0, 1) xAxis xAxis) 0
  infinite "rule 7: infinite creases" (.axiom7 (0, 0) xAxis xAxis)
  let some sqrtTwo := (Scalar.rootList [-2, 0, 1]).find? (fun r => decide (0 < r))
    | throw <| IO.userError "FAIL: missing irrational test coefficient"
  let _ ← finite "irrational circle coefficients"
    (.axiom5 (2, 0) (0, 0) (Line.chart 0 sqrtTwo)) 2
  let _ ← finite "irrational cubic coefficients"
    (.axiom6 (0, sqrtTwo) (0, -sqrtTwo) (Line.horizontal (-sqrtTwo)) yAxis) 3
  for branch in [LeanOrigamiDemos.AllFolds.Branch.firstDiagonal,
      .secondDiagonal, .horizontal] do
    check "Hex all-seven-rule replay" (Program.accepts
      (LeanOrigamiDemos.AllFolds.program Scalar branch) ⟨18⟩ .x (1/2))
  IO.println "PASS: all seven exact fold lists, finite/empty/infinite cases, irrational coefficients, and complete program replay"

open LeanOrigami in
#eval do
  let args := LeanOrigamiDemos.Arithmetic.arguments
  let two := (ArithmeticRecipe.add (1 : Scalar) 1).append
    (Basis.program Scalar true) (args ⟨1⟩ ⟨1⟩).indices
  let negativeTwo := (ArithmeticRecipe.sub (0 : Scalar) 2).append
    two.1 (args ⟨0⟩ two.2).indices
  let four := (ArithmeticRecipe.mul (-2 : Scalar) (-2)).append
    negativeTwo.1 (args negativeTwo.2 negativeTwo.2).indices
  let hne : (-2 : Scalar) ≠ 0 := by
    rw [neg_ne_zero]
    exact two_ne_zero
  let quotient := (ArithmeticRecipe.div (4 : Scalar) (-2) hne).append
    four.1 (args four.2 negativeTwo.2).indices
  unless Program.accepts quotient.1 quotient.2 .x (-2) do
    throw <| IO.userError "FAIL: Hex arithmetic recipe expansion"
  IO.println "PASS: Hex arithmetic recipes, signed operands, and relocated references"
