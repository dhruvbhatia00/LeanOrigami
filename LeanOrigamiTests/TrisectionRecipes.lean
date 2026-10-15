import LeanOrigami.Widget
import LeanOrigami.Construction.Basis

/-!
# Trisection through the visual recipe API

Run explicitly through Lake. Two rational sample configurations exercise
translation, unequal lengths, and clockwise replay. A right-angle construction
starts from the actual proof seeds and exports an irrational coordinate for
independent kernel replay. Runtime assertions test discovery, not certification.
-/
namespace LeanOrigamiTests.TrisectionRecipes
open LeanOrigami LeanOrigami.Widget

private def get {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def require (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"FAIL: {label}")
  IO.println s!"PASS: {label}"

private def outputs (session : Session) :
    IO (RecipeOutput × RecipeOutput × RecipeOutput × RecipeOutput) := do
  let some group := session.groups.back? | throw (IO.userError "Missing recipe group")
  let [first, second, firstLine, secondLine] := group.outputs.toList
    | throw (IO.userError "Expected four named trisection outputs")
  IO.println "PASS: four named trisection outputs"
  return (first, second, firstLine, secondLine)

private def checkOutputs (session : Session) (vertex first second : Point Scalar) : IO Unit := do
  require "exact branches finish without a manual branch index"
    (session.running.isNone && session.pending.isNone && session.failure.isNone)
  let (firstPoint, secondPoint, firstLine, secondLine) ← outputs session
  for (out, expected) in [(firstPoint, first), (secondPoint, second)] do
    require out.name ((← get (session.selected out.index .x)) == expected.1 &&
      (← get (session.selected out.index .y)) == expected.2)
  for (out, endpoint) in [(firstLine, first), (secondLine, second)] do
    let .ok line := Program.line session.objects ⟨out.index⟩
      | throw (IO.userError "Named crease is not a line")
    require out.name (decide (line.Contains vertex ∧ line.Contains endpoint))

/-- Replaying a saved recipe must rediscover its roots after samples change. -/
private def samples : IO Unit := do
  let values : Array (Array String) := #[#["0", "0"], #["1", "0"],
    #["0", "1", "0"], #["1", "0", "0"], #["0", "1"],
    #["2", "-3"], #["2", "-1"], #["6/25", "-192/25"]]
  let inputs := trisectionTemplate.parameters.zipIdx.map fun (p, i) =>
    SampleInput.mk p.name p.kind values[i]! false
  let (workspace, session) ← get (({ name := "" } : WorkspaceState).applySamples
    ({ seeds := [], objects := [] } : Session) "trisectors" inputs 0)
  let built ← get (session.useRecipe "Trisection" trisectionTemplate (Array.range 8))
  checkOutputs built (2, -3) (6/5, -12/5) (26/25, -82/25)
  let clockwise := inputs.set! 5 ⟨"Vertex", .point, #["0", "0"], false⟩
    |>.set! 6 ⟨"First ray point", .point, #["1", "0"], false⟩
    |>.set! 7 ⟨"Second ray point", .point, #["-117/125", "-44/125"], false⟩
  let some selected := built.result | throw (IO.userError "Missing selected output")
  let (_, replayed) ← get (workspace.applySamples built "trisectors" clockwise selected)
  checkOutputs replayed (0, 0) (3/5, -4/5) (-7/25, -24/25)
  for (first, second) in [(((0 : Scalar), 0), (1, 1)), ((1, 0), (-1, 0))] do
    let objects := TrisectionRecipe.inputs (0, 0) first second
    require "zero or straight angle rejected before construction"
      ((({ seeds := objects, objects } : Session).useRecipe "Trisection"
        trisectionTemplate (Array.range 8)).toOption.isNone)
  require "edited template loses its proved specification"
    ((librarySpecification { trisectionTemplate with checks := #[] }).isNone)

/-- Construct the frame legally, trisect a right angle, and export cos(30°).
The fresh replay file checks both the primitive construction and its target. -/
private def exportProof : IO Unit := do
  let program := Basis.program Scalar true
  let .ok objects := Program.run program | throw (IO.userError "Basis execution failed")
  let session ← get (({ program := Execution.ofProgram program, objects } : Session).useRecipe "Trisection"
    trisectionTemplate #[0, 1, 2, 3, 8, 0, 1, 8])
  let (firstPoint, _, _, _) ← outputs session
  let index := firstPoint.index
  let x ← get (session.selected index .x)
  let y ← get (session.selected index .y)
  require "right-angle trisection has the positive irrational coordinate"
    (decide (0 < x) && x*x == 3/4 && y == 1/2)
  let saved ← get (← prepareComposition session index .x)
  let history := "#[" ++ String.intercalate ", " (session.groups.toList.map RecipeGroup.source) ++ "]"
  let source := "import LeanOrigami.Widget\nopen LeanOrigami LeanOrigami.Widget\n\n" ++
    "theorem trisector_coordinate : ConstructibleNumber (Real.sqrt (3 / 4)) := by\n" ++
    "  origami history (" ++ history ++ ") composed (" ++ saved.replace "\n" "\n  " ++ ")\n" ++
    "#print axioms trisector_coordinate\n"
  IO.FS.createDirAll ".lake/phase7"
  IO.FS.writeFile ".lake/phase7/TrisectionReplay.lean" source
  IO.println "PASS: irrational trisection proof exported; fresh kernel replay remains separate"

/-- Focused runtime coverage, followed by a separately checked proof artifact. -/
def run : IO Unit := do
  require "trisection template is well formed" trisectionTemplate.validate.toOption.isSome
  IO.println "START: changed-sample trisection checks"
  samples
  IO.println "START: irrational trisection export"
  exportProof

#print axioms Scalar.trisectionRoots_exists
#print axioms Scalar.trisectionRoots_sound
#print axioms TrisectionRecipe.executes
#print axioms trisectionTemplate_contract
#print axioms trisectionPostcondition_sound
#print axioms trisection_cubic_policy

end LeanOrigamiTests.TrisectionRecipes

def main : IO Unit := LeanOrigamiTests.TrisectionRecipes.run
