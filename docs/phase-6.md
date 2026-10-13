# Phase 6 checkpoint audit

The backend and panel implementation follow the expanded work order in
PLAN.md. Phase 6 remains open while live infoview validation is completed.

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

Live checks on 2026-10-12 constructed half, square root two, and cube root
two through actual canvas selections and RPC operations. The trisection
preview displayed three distinct creases; selecting the second branch added
one step. Wrong target coordinates and coincident-line intersections were
rejected. Undo and zoom controls worked, with two interaction defects found:
the active input slot was not reset after committing a fold, and wheel zoom
also scrolled the outer infoview.

Submission failed for all three correct constructions. Improved diagnostics
identified the cause: the captured asynchronous theorem environment restricts
auxiliary declaration names to the enclosing theorem, but the RPC context did
not restore that name prefix. Standalone proof replay did not exercise this
editor-only restriction. The repair must have a named-theorem regression and
live proof insertion/replay before acceptance.

Remaining acceptance work: complete cubic proof insertion and independent
replay of the live proofs, finish stale-edit checks and live hover inspection.
Phase 6 remains open.

Repair progress: `checkProof` now restores the enclosing asynchronous theorem's
auxiliary-name prefix and preserves underlying elaboration errors. The complete
RPC module passes LSP diagnostics and its targeted build. The separate
named-theorem regression passes complete LSP diagnostics without warnings;
its axiom report is empty. The actual JavaScript module passes adapter tests
for consuming wheel gestures, resetting input roles, hover inspection, and
bounded grid generation at small and large zoom levels.

After the repair, the live widget constructed half in three steps and square
root two in eight steps. Both submissions displayed successful proof checking;
both Insert checked proof actions wrote their generated construction proofs
into Visual.lean, and the editor reported no errors. The fallback demo tactics
then produced unused-tactic warnings, as expected after the goals were closed.
The inserted source was saved separately in `.lake/phase6/LiveVisual.lean` for
subsequent replay. The grid, operation descriptions, selection guidance, and
click-to-select were observed in the live panel. A wheel gesture visibly
changed the canvas scale while the surrounding controls stayed stationary.
The cubic construction is still in progress; its repaired submission has not
yet been checked live. The separate replay of the live half and square-root
proofs subsequently passed, with only the ordinary foundations.

The user accepted the observed construction behavior and requested persistent
visual editing and line labels. The plan now requires `origami saved (...)`
to retain the exact program, coordinate selection, and certificates. The new
`Widget/Saved.lean` module uses `Program.accepts_sound`; its axiom report is
only `propext`, `Classical.choice`, and `Quot.sound`. The exporter reuses one
certificate-expression serializer for proofs and saved data.

Live testing confirmed that a saved tactic closes the goal and still displays
its panel. It exposed an attempted native evaluation of the real target during
reopening. The loader now reduces the data projections before compilation,
extracting only the scalar program and selection. A focused regression with
a noncomputable real-division target passed. The targeted widget build passed.
The runtime exporter generated rational, square-root, and cube-root saved
tactics; all passed fresh replay with only the standard foundations. The final
runtime test source passes complete LSP diagnostics. JavaScript tests pass for
line and candidate labels, restored point/coordinate selections, and stale saves.
Hover and object descriptions now round to six significant digits and omit
trailing zeros; focused tests include integers, irrational values, signed zero,
and very small/large magnitudes.

Live persistence checks passed after restarting the Lean file. The half proof
restored all three steps and point 4's x coordinate with no open goal. Canvas
labels L2 and L3 were visible. An additional A4 fold was appended, checked,
and saved through the panel. Switching to the square-root proof restored its
eight steps and point 9's x coordinate; returning to half restored the saved
four-step program. Undo, submit, and save restored the minimal three-step demo.
The source remains `origami saved (...)` throughout. The user's existing
intersection order was retained. Earlier unsaved editor contents were backed
up under `.lake/phase6/UserVisualBuffer.lean` before replacing the source format.

The standalone integration regression must be run with `lake lean` so Hex's
native libraries are available to the display loader; plain `lake env lean`
is sufficient for proof-only replay but not this native display test. Its
native-enabled run passed, including reopening under a noncomputable real target,
rejecting a certificate for the wrong goal, and the standard-axiom audit.
The final widget build, including concise decimal formatting, passed. No
full-suite rerun or new timing benchmark is claimed for this focused UI revision.
The requested persistent editing and line-label checkpoint is complete; broader
Phase 6 acceptance remains tracked separately above.

History inspection follow-up: the history now carries structured input/output
references derived from each instruction, replacing prose-only entries. Hover
or keyboard focus highlights inputs in blue and the result in orange, dims
other objects, and draws the result last for coincident geometry. The history
sits below the canvas in a bounded scroll area. Inspection is local and leaves
programs, proofs, operation selections, and the submitted coordinate unchanged.

Validation: the session module and separate history tests pass complete LSP
diagnostics; the widget build passes and is up to date. Lean tests cover all
seven input mappings and intersection/output numbering. Browser tests cover
folds, intersections, keyboard focus, clearing on leave/collapse/undo, output
layering, and preservation of selections without RPC calls. The saved-proof
and certificate code is unchanged. Live testing on the saved square-root proof
confirmed blue inputs, orange output, dimming, and clearing on departure for
folds and intersections without changing its eight steps or selected point.
It exposed stationary-pointer interference when keyboard focus scrolls history;
inspection now follows actual pointer movement, and obsolete leave/blur events
do not clear another row's highlight. The regression and final live keyboard
check both pass: Tab to the fifth step keeps its intersection highlighted after
scrolling, with the original point/coordinate selection intact. The targeted
widget rebuild passed and its embedded source was checked for the fix. JavaScript-only edits require explicitly rebuilding
the widget module because this Lake setup does not track its `include_str` input;
the developer instructions now document that narrow rebuild.
