import LeanOrigami.Scalar.Roots
import LeanOrigamiDemos.RootPrograms
import LeanOrigamiTests.TextScalar

/-!
# Native replay of irrational root constructions

Run `lake lean LeanOrigamiTests/RootInterpreter.lean` to execute.
These assertions test Hex integration; they are never used as proof premises.
The corresponding exact construction and angle theorems are in Demos/Roots.
-/

namespace LeanOrigamiTests.RootInterpreter
open LeanOrigami LeanOrigamiDemos.RootPrograms

private def check (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw <| IO.userError s!"FAIL: {label}"

private def roots (coefficients : List Scalar) : IO (List Scalar) := do
  match Scalar.realRoots (Scalar.polynomial coefficients) with
  | .all => throw <| IO.userError "FAIL: unexpected zero polynomial"
  | .finite values => return values

private def replay (label : String) (program : Program Scalar × PointRef) (target : Scalar) : IO Unit := do
  check label (Program.accepts program.1 program.2 .x target)
  check s!"{label}: wrong target" (!(Program.accepts program.1 program.2 .x (target+1)))

/-- Execute the complete saved constructions from the two seed points. -/
def run : IO Unit := do
  let certified := LeanOrigamiTests.TextScalar.squareRoot
  let some certifiedProgram := squareRootTwo Scalar certified
    | throw <| IO.userError "FAIL: certified Hex root recipe rejected"
  replay "same Hex value as the kernel certificate" certifiedProgram certified
  let squareRoots ← roots [-2, 0, 1]
  let some square := squareRoots.find? (fun x => decide (0 < x))
    | throw <| IO.userError "FAIL: positive square root missing"
  let some squareProgram := squareRootTwo Scalar square
    | throw <| IO.userError "FAIL: square-root recipe rejected"
  check "exact sqrt two" (decide (0 < square ∧ square^2 = 2))
  replay "sqrt two" squareProgram square
  check "negative square-root choice rejected" ((squareRootTwo Scalar (-square)).isNone)
  let cubeRoots ← roots [-2, 0, 0, 1]
  let [cube] := cubeRoots | throw <| IO.userError "FAIL: cube root count"
  check "exact cube doubling" (decide (cube^3 = 2 ∧ 0 < cube))
  replay "cube root two" (cubeRootTwo Scalar cube) cube
  let fourthRoots ← roots [-square, 0, 1]
  let some fourth := fourthRoots.find? (fun x => decide (0 < x))
    | throw <| IO.userError "FAIL: positive fourth root missing"
  let some fourthProgram := fourthRootTwo Scalar square fourth
    | throw <| IO.userError "FAIL: composed root recipe rejected"
  check "exact fourth root" (decide (fourth^4 = 2 ∧ 0 < fourth))
  replay "root used as coefficient" fourthProgram fourth
  let candidates ← roots [-1, -6, 0, 8]
  check "three trisection roots" (candidates.length == 3)
  let selected := candidates.filter (fun x => decide ((1/2 : Scalar) < x ∧ x < 1))
  let [cosine] := selected | throw <| IO.userError "FAIL: trisection branch count"
  check "exact trisection polynomial and branch"
    (decide (8*cosine^3-6*cosine-1 = 0 ∧ (1/2 : Scalar) < cosine ∧ cosine < 1))
  replay "trisection cosine" (trisectionCosine Scalar cosine) cosine
  let sineRoots ← roots [cosine*cosine-1, 0, 1]
  let some sine := sineRoots.find? (fun x => decide (0 < x))
    | throw <| IO.userError "FAIL: positive sine missing"
  let some pointProgram := trisectionPoint Scalar cosine sine
    | throw <| IO.userError "FAIL: trisection point rejected"
  replay "trisection point x" pointProgram cosine
  check "trisection point y" (Program.accepts pointProgram.1 pointProgram.2 .y sine)
  check "upper unit circle" (decide (cosine^2+sine^2 = 1 ∧ 0 < sine))
  check "lower trisection branch rejected" ((trisectionPoint Scalar cosine (-sine)).isNone)
  IO.println "PASS: exact sqrt two, cube doubling, composed fourth root, and trisection branch replay"

#eval run

end LeanOrigamiTests.RootInterpreter
