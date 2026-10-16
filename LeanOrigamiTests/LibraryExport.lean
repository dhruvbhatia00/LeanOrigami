import LeanOrigami.Widget.Export
import LeanOrigami.Construction.Basis

/-!
# Public-output recipe certificate regressions

Run with `lake lean LeanOrigamiTests/LibraryExport.lean -- --run
LeanOrigamiTests/LibraryExport.lean`. The optional `trisection` argument runs only
the small performance gate. Generated files in `.lake/library` must then be
checked independently: native discovery/export alone is not certification.
-/

namespace LeanOrigami.Tests.LibraryExport
open Widget

private def get {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def basis : IO Session := get (Session.ofProgram (Basis.program Scalar true))

private def applyRecipe (session : Session) (recipe : LibraryRecipe) (operands : Array Nat) :
    IO (Session × Nat) := do
  let arguments := if recipe == .midpoint then operands else #[0,1,2,3,8] ++ operands
  let result ← get (session.useRecipe (reprStr recipe) recipe.template arguments)
  let some index := result.result | throw (IO.userError "Missing library result")
  let some (.library ..) := result.program.getLast?
    | throw (IO.userError "Unchanged library recipe expanded instead of retaining public outputs")
  return (result, index)

private def save (name : String) (session : Session) (point : Nat) (goal : String) : IO Unit := do
  let start ← IO.monoMsNow
  let source ← get (← prepareComposition session point .x)
  let elapsed := (← IO.monoMsNow) - start
  IO.FS.createDirAll ".lake/library"
  IO.FS.writeFile s!".lake/library/{name}.lean"
    ("import LeanOrigami.Widget\nimport Mathlib.Util.CountHeartbeats\n\n" ++
      s!"#count_heartbeats in\ntheorem {name} : LeanOrigami.ConstructibleNumber ({goal}) := by\n" ++
      "  origami composed (" ++ source.replace "\n" "\n  " ++ ")\n" ++
      s!"#print axioms {name}\n")
  IO.println s!"{name}: {session.program.length} public steps; export {elapsed} ms; {source.utf8ByteSize} bytes; fresh kernel replay required"

/-- The early gate has five root witnesses but no private trisection instructions. -/
def rightAngle : IO Unit := do
  IO.println "START: right-angle discovery"
  (← IO.getStdout).flush
  let start ← IO.monoMsNow
  let (s, point) ← applyRecipe (← basis) .trisection #[0,1,8]
  IO.println s!"Right-angle discovery: {(← IO.monoMsNow)-start} ms"
  (← IO.getStdout).flush
  unless s.objects.length == 13 do throw (IO.userError "Trisection did not retain exactly four outputs")
  save "rightAngle" s point "Real.sqrt (3/4)"

/-- One certificate covers all arithmetic and measurement families, irrational
inputs, zero roots, signed roots, and a custom recipe containing compact calls. -/
def library : IO Unit := do
  let (s, half) ← applyRecipe (← basis) .midpoint #[0,1]
  let (s, two) ← applyRecipe s (.arithmetic .add) #[1,1]
  let (s, negative) ← applyRecipe s (.arithmetic .sub) #[1,two]
  let (s, _) ← applyRecipe s (.arithmetic .neg) #[negative]
  let (s, _) ← applyRecipe s (.arithmetic .mul) #[two,two]
  let (s, _) ← applyRecipe s (.arithmetic .inv) #[two]
  let (s, _) ← applyRecipe s (.arithmetic .div) #[half,two]
  let (s, root) ← applyRecipe s (.measurement .sqrt) #[two]
  let (s, _) ← applyRecipe s (.measurement .cbrt) #[two]
  let (s, _) ← applyRecipe s (.measurement .projectX) #[root]
  let (s, _) ← applyRecipe s (.measurement .projectY) #[root]
  let (s, vertical) ← applyRecipe s (.measurement .transferX) #[root]
  let (s, _) ← applyRecipe s (.measurement .transferY) #[vertical]
  let (s, _) ← applyRecipe s (.measurement .distanceX) #[0,vertical]
  let (s, _) ← applyRecipe s (.measurement .distanceY) #[0,vertical]
  let (s, _) ← applyRecipe s (.measurement .sqrt) #[0]
  let (s, _) ← applyRecipe s (.measurement .cbrt) #[negative]
  let (s, _) ← applyRecipe s (.arithmetic .inv) #[root]
  let sqrtSquared : RecipeTemplate := {
    parameters := (measurementTemplate .sqrt).parameters
    steps := [RecipeOperation.call "Root" (measurementTemplate .sqrt) #[0,1,2,3,4,5],
      RecipeOperation.call "Square" (arithmeticTemplate .mul) #[0,1,2,3,4,6,6]]
    output := 7 }
  let s ← get (s.useRecipe "Custom root squared" sqrtSquared #[0,1,2,3,8,two])
  let some result := s.result | throw (IO.userError "Missing custom result")
  unless (← get (s.selected result .x)) = 2 do throw (IO.userError "Custom result changed")
  save "allLibraryFamilies" s result "(2 : ℝ)"
  let forged : Session := { s with
    program := s.program ++
      [Execution.Step.library (K := Scalar) "Forged" midpointRecipe #[0,1] [Object.point (3,0)]]
    objects := s.objects ++ [Object.point (3,0)] }
  unless (← prepareComposition forged s.objects.length .x).toOption.isNone do
    throw (IO.userError "Forged library output was accepted")
  let edited := { midpointRecipe with output := 0 }
  let forgedDefinition : Session := { s with
    program := s.program ++
      [Execution.Step.library (K := Scalar) "Edited" edited #[0,1] [Object.point (0,0)]]
    objects := s.objects ++ [Object.point (0,0)] }
  unless (← prepareComposition forgedDefinition s.objects.length .x).toOption.isNone do
    throw (IO.userError "Edited definition retained its library rule")
  IO.println "PASS: forged outputs and changed library definitions rejected"

/-- A genuinely cubic angle followed by arithmetic recovers its original cosine.
Both output creases are certified along with the reused first endpoint. -/
def cubicAngle : IO Unit := do
  let (s, two) ← applyRecipe (← basis) (.arithmetic .add) #[1,1]
  let (s, three) ← applyRecipe s (.arithmetic .add) #[two,1]
  let (s, four) ← applyRecipe s (.arithmetic .add) #[two,two]
  let (s, vertical) ← applyRecipe s (.measurement .transferX) #[four]
  let s ← get ((← get (s.preview (.axiom4 ⟨three⟩ ⟨2⟩))).choose 0)
  let xLine := s.objects.length - 1
  let s ← get ((← get (s.preview (.axiom4 ⟨vertical⟩ ⟨3⟩))).choose 0)
  let yLine := s.objects.length - 1
  let s ← get (s.intersect xLine yLine)
  let endpoint := s.objects.length - 1
  let (s, trisector) ← applyRecipe s .trisection #[0,1,endpoint]
  let (s, t) ← applyRecipe s (.measurement .projectX) #[trisector]
  let (s, square) ← applyRecipe s (.arithmetic .mul) #[t,t]
  let (s, cube) ← applyRecipe s (.arithmetic .mul) #[square,t]
  let (s, twiceCube) ← applyRecipe s (.arithmetic .add) #[cube,cube]
  let (s, fourCube) ← applyRecipe s (.arithmetic .add) #[twiceCube,twiceCube]
  let (s, twice) ← applyRecipe s (.arithmetic .add) #[t,t]
  let (s, triple) ← applyRecipe s (.arithmetic .add) #[twice,t]
  let (s, result) ← applyRecipe s (.arithmetic .sub) #[fourCube,triple]
  unless (← get (s.selected result .x)) = (3/5 : Scalar) do
    throw (IO.userError "Trisection's cubic identity failed")
  save "cubicAngle" s result "(3/5 : ℝ)"

/-- A positive coordinate far below display precision must still get a checked
sign certificate. Zero is covered by the square-root case above. -/
def smallSign : IO Unit := do
  let root ← get (LibraryRecipe.chooseRoot [-2,0,1] (fun x => decide (0 < x)))
  let denominator : Scalar := 10^30
  let tiny := root / denominator
  let log : Text.ArithmeticLog := #[(root, .root), (denominator, .rational (10^30)),
    (tiny, .div 0 1)]
  let table ← get (Text.CoordinateTable.prepareBlocks log [[root, denominator, tiny]] tiny)
  let (table, bits) ← get (LibraryRecipe.refineSigns table [tiny])
  let arithmetic := "first | " ++ String.intercalate " | "
    (table.fieldSources.map fun (name, _) => s!"origami_coordinates {name}")
  let proof ← get (LibraryRecipe.signSource table arithmetic bits tiny true)
  let value ← get (table.scalarSource tiny)
  let declarations := String.join (table.fieldSources.map fun (name, source) =>
    s!"def {name} : Scalar.Presentation := {source}\n")
  IO.FS.writeFile ".lake/library/smallSign.lean"
    ("import LeanOrigami.Widget\nimport Mathlib.Util.CountHeartbeats\n\n" ++
      "namespace TinySign\nopen LeanOrigami LeanOrigami.Text LeanOrigami.Widget Hex\n" ++
      declarations ++ s!"def tiny : Scalar := {value}\n" ++
      "#count_heartbeats in\ntheorem positive : 0 < tiny := by\n" ++
      "  dsimp only [tiny]\n  " ++ proof.replace "\n" "\n  " ++
      "\n#print axioms positive\n#print axioms LeanOrigami.Scalar.Presentation.coordinate_pos\n" ++
      "#print axioms LeanOrigami.Scalar.Presentation.coordinate_nonneg\nend TinySign\n")
  IO.println s!"Tiny positive coordinate: {bits}-bit sign certificate; kernel replay required"

/-- A zero goal also exercises the target sign certificate at the boundary. -/
def zero : IO Unit := do
  save "zero" (← basis) 0 "(0 : ℝ)"

#print axioms LibraryRecipe.produces_sound
#print axioms Execution.libraryRule

end LeanOrigami.Tests.LibraryExport

def main (args : List String) : IO Unit := do
  LeanOrigami.Tests.LibraryExport.rightAngle
  unless args == ["trisection"] do
    LeanOrigami.Tests.LibraryExport.library
    LeanOrigami.Tests.LibraryExport.cubicAngle
    LeanOrigami.Tests.LibraryExport.smallSign
    LeanOrigami.Tests.LibraryExport.zero
    -- Share one cold import load when checking the complete replay suite.
    let mut replay := "import LeanOrigami.Widget\nimport Mathlib.Util.CountHeartbeats\n\n"
    for name in ["rightAngle", "allLibraryFamilies", "cubicAngle", "smallSign", "zero"] do
      let source ← IO.FS.readFile s!".lake/library/{name}.lean"
      replay := replay ++ String.intercalate "\n" ((source.splitOn "\n").drop 3) ++ "\n"
    IO.FS.writeFile ".lake/library/Replay.lean" replay
