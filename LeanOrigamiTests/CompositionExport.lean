import LeanOrigami.Widget.Export

/-!
# Scoped export and matched primitive comparison

Run this focused executable to produce small independent proof files. Discovery,
export, and source size are measured separately. The replay files include
`#count_heartbeats` around each theorem so cold imports are not mistaken for
kernel proof work. No trisection or full-library benchmark is run here.
-/
namespace LeanOrigami.Tests.CompositionExport
open LeanOrigami Widget

private def get {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def fold (session : Session) (request : FoldRequest) : IO Session := do
  get ((← get (session.preview request)).choose 0)

private def expanded : IO Session := do
  let s ← fold {} (.axiom1 ⟨0⟩ ⟨1⟩)
  let s ← fold s (.axiom2 ⟨0⟩ ⟨1⟩)
  let s ← get (s.intersect 2 3)
  let s ← fold s (.axiom1 ⟨0⟩ ⟨4⟩)
  let s ← fold s (.axiom2 ⟨0⟩ ⟨4⟩)
  let s ← get (s.intersect 5 6)
  fold s (.axiom1 ⟨0⟩ ⟨7⟩)

private def composed : IO Session := do
  let s ← get (({} : Session).useRecipe "Midpoint" midpointRecipe #[0,1])
  let s ← get (s.useRecipe "Midpoint again" midpointRecipe #[0,2])
  fold s (.axiom1 ⟨0⟩ ⟨3⟩)

private def save (name : String) (build : IO Session) (point : Nat) (goal : String) : IO String := do
  let start ← IO.monoMsNow
  let session ← build
  let discovered ← IO.monoMsNow
  let source ← get (← prepareComposition session point .x)
  let exported ← IO.monoMsNow
  IO.println s!"{name}: discovery {discovered-start} ms; export {exported-discovered} ms; {source.utf8ByteSize} bytes; {session.program.length} public steps"
  let text := s!"#count_heartbeats in\ntheorem {name} : LeanOrigami.ConstructibleNumber ({goal}) := by\n" ++
    "  origami composed (" ++ source.replace "\n" "\n  " ++ ")\n" ++
    s!"#print axioms {name}\n#print axioms LeanOrigami.Widget.SavedComposition.sound\n"
  IO.FS.writeFile s!".lake/composition/{name}.lean"
    ("import LeanOrigami.Widget\nimport Mathlib.Util.CountHeartbeats\n\n" ++ text)
  return text

/-- Small successful, fallback, multi-output, and forged-output regressions. -/
def run : IO Unit := do
  IO.FS.createDirAll ".lake/composition"
  let expandedProof ← save "expandedQuarter" expanded 7 "(1/4 : ℝ)"
  let composedProof ← save "composedQuarter" composed 3 "(1/4 : ℝ)"
  let edited := { midpointRecipe with parameters := #[⟨"Edited A", .point⟩, ⟨"B", .point⟩] }
  let editedProof ← save "editedHalf" (get (({} : Session).useRecipe "Edited midpoint" edited #[0,1])) 2 "(1/2 : ℝ)"
  let multiple := { midpointRecipe with outputs := #[⟨"Midpoint", 4⟩, ⟨"Joining crease", 2⟩] }
  let session ← get (({} : Session).useRecipe "Two outputs" multiple #[0,1])
  unless session.objects.length == 4 do throw (IO.userError "Private objects escaped the call")
  let _ ← get ((Program.line session.objects ⟨3⟩).mapError errorMessage)
  let multipleProof ← save "multipleOutputs" (pure session) 2 "(1/2 : ℝ)"
  let seedProof ← save "seed" (pure {}) 1 "(1 : ℝ)"
  IO.FS.writeFile ".lake/composition/Replay.lean"
    ("import LeanOrigami.Widget\nimport Mathlib.Util.CountHeartbeats\n\n" ++
      expandedProof ++ composedProof ++ editedProof ++ multipleProof ++ seedProof)
  let forged : Session := {
    program := [Execution.Step.call "Midpoint" midpointRecipe #[0,1] [.point (3,0)] []]
    objects := Program.initial ++ [.point (3,0)] }
  unless (← prepareComposition forged 2 .x).toOption.isNone do
    throw (IO.userError "Forged output was exported")
  IO.println "PASS: forged output rejected; independent replay remains required"

end LeanOrigami.Tests.CompositionExport

def main : IO Unit := LeanOrigami.Tests.CompositionExport.run
