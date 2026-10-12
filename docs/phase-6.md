# Phase 6 checkpoint audit

The backend and panel implementation follow the expanded work order in
PLAN.md. Phase 6 remains open because live infoview validation is blocked.

Current evidence:

- The exact session module passed complete LSP diagnostics and a targeted
  build. It reuses `Program.resolve`, `Scalar.folds`, and `Program.step`.
- The shared exporter refactor passed complete LSP diagnostics. Standalone
  artifacts and local proof expressions now share certificate serialization;
  the targeted build also passed.
- The goal-matching module passes complete LSP diagnostics and its targeted
  build. `lean_verify` reports only `propext`, `Classical.choice`, and
  `Quot.sound` for `cube_identity` and `coordinate_nonneg`, with no source
  warnings or nonstandard dependencies.
- The RPC/panel module passed complete LSP diagnostics and a targeted build.
  The initial goal-matching examples pass their targeted build, including
  rejecting an incorrect rational target. The expanded interface tests pass
  complete LSP diagnostics: local target names, unsupported targets, and
  rejection of a proof of the wrong type. Their axiom reports contain only
  the ordinary foundations.
  The panel-opening tactic is registered as intentionally leaving goals
  unchanged; its tests now have no project warnings.
- The actual JavaScript module passes focused rendering and event-wiring
  checks: vertical lines, clipping, precision selection, stale replies,
  exact snapshot references, undo during pending submission, and versioned
  insertion. These use a React/editor adapter, not a live infoview.
- The session integration file passed complete LSP diagnostics, then its
  `main` ran in the active server: all seven operations, invalid references,
  coincident-line rejection, undo, precision-stable object/branch identities,
  and three trisection branches passed. Half, square-root, and cube-root
  proof sources were exported. The temporary evaluation command was removed;
  the maintained runtime file remains explicitly runnable.
- The visual demo module built successfully. The first fresh replay passed
  the standalone half certificate, but exposed two local-proof integration
  defects: field-instance synthesis for a local presentation and transport
  of rational casts. The shared arithmetic tactic now supplies the saved
  instance explicitly and transports rational casts. The three actual
  exported programs and their target equations pass focused LSP regression
  checks with that correction; temporary in-module fixtures were removed.
- Fresh full replay after the correction passed in a separate Lean process
  (`lake env lean .lake/phase6/Saved.lean`, exit 0). The standalone half
  certificate and the local half, square-root, and cube-root proofs all report
  only `propext`, `Classical.choice`, and `Quot.sound`.
- The plan records the previously deferred Phase 5 broad regression/timing
  run separately; it has not been claimed as completed here.

The code audit found no duplicate geometry or parallel certificate exporter.
The mathematical modules remain independent of the panel; the exact editing
session, goal identification, RPC, and rendering have separate responsibilities.
Tests and demonstrations are separate, with explicit commands in README.md
and scripts/validate.sh. Temporary evaluation commands and fixtures were
removed. Source scans and the replay axiom reports found no proof holes or
unapproved axioms. The diff and shell syntax checks pass. Dependencies and
manual-only CI are unchanged.

Remaining acceptance work: exercise the rational, square-root, and cube-root
constructions in the live Lean infoview, inspect trisection branches, insert
the proofs, and reopen the edited files. Verify the real rendered layout and
editor behavior there. Computer-use attempts consistently report that the
Mac is locked; the user has been asked to unlock it. The JavaScript adapter
and exact session checks do not replace this live validation.
