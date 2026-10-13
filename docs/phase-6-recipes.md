# Reusable recipe checkpoint

Status: Phase 6R complete (2026-10-13).

The approved Phase 6R adds parameterized recipes before Phase 7. Recipes erase
sample outputs and branch indices; invocation discovers new exact outputs and
expands to the existing primitive program. Standalone samples are not proof
seeds. Recipe groups are presentation metadata, separate from certificates.

The implementation shares the existing canvas, session operations, exporter,
and proof gate. The new modules separate template data from workspace loading;
`docs/recipes.md` gives the code map and workflow.

Validation and audit:

- Complete Lean LSP diagnostics passed for Recipe, Session, and Workspace.
- Targeted builds passed for these modules, their Saved consumer, and Widget,
  including the final source-formatting correction.
- The browser harness passed existing widget checks and the new workspace,
  invocation, nested history, group highlighting, and branch-cancellation cases.
- The Widget MCP worker restarted repeatedly without source changes. Its final
  validation uses a targeted command-line build instead; no dependency cache
  was cleared and no Hex code or dependency version was changed.
- Input-validation cases were moved from unsuitable reduction proofs into the
  executable test suite. Certification still uses the existing kernel-checked
  program and target proofs.

- Live GUI authoring created the midpoint with A1, A2, and an intersection.
  The saved recipe appeared in the proof's menu; invocation produced a group
  containing the three primitives. Expanding and focusing it highlighted its
  inputs/output. Submission checked the proof of one half and saved it.
- The live save test caught a multiline-record indentation error that isolated
  parsing had missed. Serialization now uses an indentation-independent record,
  with a regression parsing it after a long declaration header.

- After rebuilding, the corrected recipe saved and reopened with three steps.
  The saved proof reopened with “No goals,” restored all three objects added by
  construction, and retained its expandable recipe history and highlighting.
- A fresh CLI process checked the bodies of `Widget.lean`,
  `WidgetHistory.lean`, `RecipeRuntime.lean`, and `LeanOrigamiDemos/Recipes.lean`
  together in `.lake/recipes/Checkpoint.lean`, using their shared Widget import
  once. It exited successfully. This checked the actual GUI-authored saved
  proof independently of widget state, without the demo's former fallback.
- All 27 runtime assertions/export checks passed, covering changed/rotated
  inputs, nested calls, mixed input kinds and line outputs, invalid references,
  sample/seed separation, both ambiguous branches, and rollback after progress
  or failure. The serialization tests include the insertion-format regression.
- Axiom reports for the GUI-authored `half`, `SavedConstruction.sound`, and the
  existing widget identification theorems contain only `propext`,
  `Classical.choice`, and `Quot.sound`. The existing metadata/reopening tests
  also passed. No proof holes or project axioms were added.
- The browser harness passed again after the final UI edit. The diff audit
  found no dependency changes, duplicate proof path, or new mathematical rule.
  Library, workspace loading, UI, tests, and documentation remain separated.

The temporary combined driver avoids repeated import loading; the maintained
files retain separate validation commands in `docs/recipes.md` and
`scripts/validate.sh`. RecipeRuntime also generated `.lake/recipes/Replay.lean`;
that additional generated file was not rerun after the final correction because
the actual GUI-authored saved recipe and proof had already passed the fresh
combined replay. The full solver suite and older Phase 6 release checks were
not repeated or newly marked complete.

Intentional limits: recipe failures are reported on actual inputs; multi-fold
steps ask for a fresh choice. Conditional alternatives, automatic exact branch
predicates, and general symbolic specifications are later work. Midpoint is the
initial library recipe; the planned arithmetic/root/projection library follows
this workflow. Nested calls retain expanded snapshots, rather than changing an
existing caller when the callee is edited.
