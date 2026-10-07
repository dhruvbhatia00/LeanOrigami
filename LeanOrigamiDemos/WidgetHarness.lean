import LeanOrigamiDemos.Widget

/-!
# Widget edit fixture

Emit the same versioned edit that the live panel returns, for an executable
interaction test of ProofWidgets' JavaScript and an independent Lean replay.
-/

open Lean Server LeanOrigamiDemos

meta def main : IO Unit := do
  let source := "example : (1 : Nat) + 1 = 2 := by\n  origami_phase0\n"
  let doc : DocumentMeta := {
    uri := "file:///phase0/WidgetReplay.lean"
    mod := `WidgetReplay
    version := 7
    text := source.toFileMap
    dependencyBuildMode := .never
  }
  let range : Lsp.Range := {
    start := { line := 1, character := 2 }
    «end» := { line := 1, character := 16 }
  }
  IO.println <| (toJson (submissionEdit doc range)).compress
