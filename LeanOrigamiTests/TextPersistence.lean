import LeanOrigamiDemos.Text

/-!
# Artifact IO and standalone replay fixture

Run explicitly with `lake env lean LeanOrigamiTests/TextPersistence.lean`.
The validation script then checks the generated TextReplay.lean in a fresh
Lean process. Its source contains the constructions themselves, not an import
of LeanOrigamiDemos.Text, so reopening actually rechecks the saved commands.
-/

open LeanOrigami.Text

/-- error: expected a closed ConstructibleNumber theorem -/
#guard_msgs in
#origami_verify "Nat.zero"

#eval do
  let original := LeanOrigamiDemos.textExamples
  let .ok decoded := Artifact.decode original.encode
    | throw (IO.userError "FAIL: artifact JSON decode")
  unless decoded == original do throw (IO.userError "FAIL: artifact round trip changed data")
  unless decoded.source == original.source do
    throw (IO.userError "FAIL: exact source changed during round trip")
  let unsupported := {original with version := 2}
  if let .ok _ := Artifact.decode unsupported.encode then
    throw (IO.userError "FAIL: unsupported artifact version accepted")
  if let .ok _ := Artifact.decode "not JSON" then
    throw (IO.userError "FAIL: malformed JSON accepted")
  if let .ok _ := Artifact.decode ({original with source := ""}.encode) then
    throw (IO.userError "FAIL: missing proof source accepted")
  IO.FS.createDirAll ".lake/phase5"
  original.save ".lake/phase5/construction.json"
  let loaded ← Artifact.load ".lake/phase5/construction.json"
  unless loaded == original do throw (IO.userError "FAIL: file round trip changed artifact")
  loaded.writeLean ".lake/phase5/TextReplay.lean"
  IO.println "PASS: versioned artifact JSON, exact source and file round trips; standalone proof written"
