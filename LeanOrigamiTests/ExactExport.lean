import LeanOrigami.Text.Exact
import LeanOrigami.Scalar.FoldDiscovery
import LeanOrigamiDemos.RootPrograms
import LeanOrigamiTests.Text

/-!
# Solver output to independently replayable proofs

Run the exact-export command in README.md; Lake must load Hex's native
libraries. Search runs natively and exports ordinary scalar programs. `scripts/validate.sh` checks the
resulting source in a fresh process. No example supplies a root identity or a
custom proof tactic. Timings separate discovery/export from proof replay.
-/

namespace LeanOrigamiTests.ExactExport
open LeanOrigami LeanOrigami.Text LeanOrigamiDemos.RootPrograms

private def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"FAIL: {label}")

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def positiveRoot (coefficients : List Scalar) : IO Scalar := do
  let some root := (Scalar.rootList coefficients).find? (fun x => decide (0 < x))
    | throw (IO.userError "positive root missing")
  pure root

-- Replace requested root creases by actual objects returned by discovery.
-- Exact matching, even after reversing the choices, preserves the branch.
private def discovered (program : Program Scalar) : IO (Program Scalar) := do
  let mut state : Program.State Scalar := Program.initial
  let mut out := []
  for instruction in program do
    let instruction ← match instruction with
      | .fold request selected => do
        match request with
        | .axiom3 .. | .axiom5 .. | .axiom6 .. =>
          let input ← get ((Program.resolve state request).mapError reprStr)
          let some choices := Scalar.folds input
            | throw (IO.userError "unexpected infinite fold family")
          let some choice := choices.find? (fun l => decide (l = selected))
            | throw (IO.userError "selected crease missing from discovery")
          require "candidate ordering" (decide
            (choices.reverse.find? (fun l => decide (l = selected)) = some choice))
          pure (.fold request choice)
        | _ => pure instruction
      | _ => pure instruction
    let object ← get ((Program.step state instruction).mapError reprStr)
    state := state ++ [object]
    out := instruction :: out
  pure out.reverse

private def exportCase (name : String) (saved : Program Scalar × PointRef)
    (target : Scalar) : IO String := do
  let started ← IO.monoMsNow
  IO.println s!"START: {name} discovery"
  (← IO.getStdout).flush
  let program ← discovered saved.1
  IO.println s!"START: {name} export"
  (← IO.getStdout).flush
  let artifact ← get (← exportExact program saved.2 .x target)
  let decoded ← get (Artifact.decode artifact.encode)
  require "artifact round trip" (decoded == artifact)
  let directory : System.FilePath := ".lake/exact"
  IO.FS.createDirAll directory
  artifact.save (directory / s!"{name}.json")
  artifact.writeLean (directory / s!"{name}.lean")
  let wrong ← exportExact program saved.2 .x (target + 1)
  require "wrong target rejected" (match wrong with
    | .error _ => true | .ok _ => false)
  IO.println s!"PASS: {name}, {program.length} instructions, discovery/export {(← IO.monoMsNow) - started} ms"
  -- Combine the unchanged proof bodies into one fresh process to amortize
  -- loading Hex imports. Individual standalone artifacts are also retained.
  pure ((artifact.source.replace "import LeanOrigami.Text.Exact\n" "" |>.replace
    "SavedOrigami" name) ++ s!"\n#origami_verify \"{name}.submitted\"\n")

private def rationalProgram : Program Scalar :=
  LeanOrigamiTests.Text.allRules.steps.map fun instruction =>
    match instruction with
    | .fold request l => .fold request (l.map (Rat.castHom Scalar))
    | .intersect l r p => .intersect l r ((p.1 : Scalar), (p.2 : Scalar))

-- These short constructions exercise both ways of obtaining a quadratic
-- parameter: the direction of an angle bisector and a circle/line landing.
private def quadraticFold (useAxiom5 : Bool) : IO (Program Scalar × PointRef × Scalar) := do
  let initialProgram := Basis.program Scalar true ++ if useAxiom5 then
    [.fold (.axiom2 ⟨0⟩ ⟨1⟩) (Line.chart 0 (1/2))] else []
  let request : FoldRequest := if useAxiom5 then .axiom5 ⟨1⟩ ⟨0⟩ ⟨9⟩ else .axiom3 ⟨2⟩ ⟨5⟩
  let state ← get ((Program.run initialProgram).mapError reprStr)
  let input ← get ((Program.resolve state request).mapError reprStr)
  let some choices := Scalar.folds input | throw (IO.userError "infinite quadratic choices")
  require "two quadratic choices" (choices.length == 2)
  let some crease := choices.find? (fun l => decide (l.b < 0))
    | throw (IO.userError "quadratic branch missing")
  let horizontal : Line Scalar := Line.horizontal 1
  if h : crease.determinant horizontal ≠ 0 then
    let point := crease.intersection horizontal h
    let next := initialProgram.length+2
    return (initialProgram ++ [.fold request crease, .intersect ⟨next⟩ ⟨7⟩ point], ⟨next+1⟩, point.1)
  else throw (IO.userError "quadratic crease is horizontal")

/-- Exercise all primitives, irrational branches, and a root used as a later
coefficient; save exact artifacts for separate kernel replay. -/
def run : IO Unit := do
  let mut source := "import LeanOrigami.Text.Exact\nimport LeanOrigamiTests.Text\n\n"
  source := source ++ (← exportCase "Seed" ([], ⟨0⟩) 0)
  source := source ++ (← exportCase "Rational" (rationalProgram,
    LeanOrigamiTests.Text.allRules.output) (1/2))
  let (angleProgram, anglePoint, angle) ← quadraticFold false
  source := source ++ (← exportCase "Axiom3" (angleProgram, anglePoint) angle)
  let (landingProgram, landingPoint, landing) ← quadraticFold true
  source := source ++ (← exportCase "Axiom5" (landingProgram, landingPoint) landing)
  let square ← positiveRoot [-2, 0, 1]
  let some squareProgram := squareRootTwo Scalar square
    | throw (IO.userError "square root recipe rejected")
  source := source ++ (← exportCase "Square" squareProgram square)
  let cube ← positiveRoot [-2, 0, 0, 1]
  let cubeProgram := cubeRootTwo Scalar cube
  source := source ++ (← exportCase "Cube" cubeProgram cube)
  -- Neither root alone generates the field of both. Keep the valid square-root
  -- construction even though the submitted coordinate is the cube root.
  let mixed (join : Bool) : Recipe Scalar 2 := RecipeBuilder.build 2 do
    let p ← RecipeBuilder.use (⟨squareProgram.1, squareProgram.2⟩ : Recipe Scalar 2) (fun i => i.val)
    let q ← RecipeBuilder.use (⟨cubeProgram.1, cubeProgram.2⟩ : Recipe Scalar 2) (fun i => i.val)
    if join then do
      let _ ← RecipeBuilder.fold (.axiom1 p q) (Line.horizontal 0)
      pure q
    else pure q
  let independent := mixed false
  source := source ++ (← exportCase "Independent" (independent.steps, independent.output) cube)
  let joined := mixed true
  source := source ++ (← exportCase "Joined" (joined.steps, joined.output) cube)
  -- Supplied provenance is untrusted too: changing a saved expression must fail.
  let log ← ArithmeticLog.ofProgram squareProgram.1
  let tampered := log.map fun (value, op) =>
    (value, if value = square then ArithmeticOp.rational 0 else op)
  let rejected ← exportExact squareProgram.1 squareProgram.2 .x square (some tampered)
  require "tampered arithmetic rejected" (match rejected with | .error _ => true | .ok _ => false)
  let fourth ← positiveRoot [-square, 0, 1]
  let some fourthProgram := fourthRootTwo Scalar square fourth
    | throw (IO.userError "iterated root recipe rejected")
  source := source ++ (← exportCase "Fourth" fourthProgram fourth)
  let candidates := Scalar.rootList [-1, -6, 0, 8]
  for (root, index) in candidates.zipIdx do
    source := source ++ (← exportCase s!"CubicBranch{index}"
      (trisectionCosine Scalar root) root)
  require "three distinct cubic branches" (candidates.length == 3)
  let invalid ← exportExact [.fold (.axiom1 ⟨0⟩ ⟨1⟩) (Line.horizontal 1)] ⟨1⟩ .x 1
  require "bad unused fold rejected" (match invalid with
    | .error _ => true | .ok _ => false)
  source := source ++ "\nopen LeanOrigami LeanOrigami.Text LeanOrigamiTests.Text\n" ++
    "set_option maxHeartbeats 4000000\nset_option maxRecDepth 8192\n" ++
    "run_elab do Mathlib.Linter.UnusedTactic.addIgnoreTacticKind ``LeanOrigamiTests.Text.rejectWith\n" ++
    "namespace Axiom3\nexample : target ^ 2 - 2 * target - 1 = 0 := by\n  unfold target\n  origami_coordinates field\nend Axiom3\n" ++
    "namespace Axiom5\nexample : target ^ 2 = 3 := by\n  unfold target\n  origami_coordinates field\nend Axiom5\n" ++
    "namespace Square\nexample : target ^ 2 = 2 := by\n  unfold target\n  origami_coordinates field\n" ++
    s!"example : True := by\n  reject_with \"Origami submission:\" in\n    have : Program.accepts program ⟨{squareProgram.2.index}⟩ .x (target + 1) = true := by\n      unfold program target\n      origami_check using origami_coordinates field\n  trivial\n" ++
    "end Square\nnamespace Cube\nexample : target ^ 3 = 2 := by\n  unfold target\n  origami_coordinates field\nend Cube\n" ++
    "namespace Independent\nexample : field.polynomial.natDegree = 3 ∧ field1.polynomial.natDegree = 2 := by decide +kernel\nexample : target ^ 3 = 2 := by\n  unfold target\n  origami_coordinates field\nend Independent\nnamespace Joined\nexample : field.polynomial.natDegree = 6 := by decide +kernel\nexample : target ^ 3 = 2 := by\n  unfold target\n  origami_coordinates field\nend Joined\n" ++
    "namespace Fourth\nexample : target ^ 4 = 2 := by\n  unfold target\n  origami_coordinates field\nend Fourth\n"
  source := source ++
    "namespace Square\nexample : ¬ Hex.atomWitness field.polynomial ⟨0, 0, 64⟩ := by decide +kernel\nend Square\n" ++
    "namespace Rational\nexample : True := by\n  reject_with \"Origami instruction\" in\n    have : Program.accepts (program ++ [.fold (.axiom1 ⟨0⟩ ⟨1⟩) (Line.horizontal 1)]) ⟨1⟩ .x 1 = true := by\n      unfold program\n      origami_check using origami_coordinates field\n  trivial\nend Rational\n"
  for index in [:3] do
    source := source ++ s!"namespace CubicBranch{index}\nexample : 8 * target ^ 3 - 6 * target - 1 = 0 := by\n  unfold target\n  origami_coordinates field\nend CubicBranch{index}\n"
  IO.FS.writeFile ".lake/exact/Replay.lean" source

end LeanOrigamiTests.ExactExport

def main : IO Unit := LeanOrigamiTests.ExactExport.run

