# GUI sample setup and preview checkpoint

Status: complete (2026-10-13).

Phase 6S extends the existing recipe command, replay engine, and canvas. A bare
command opens setup without declaring or registering a recipe. The user names
point/line inputs and places them on a rational grid or enters exact fractions.
Existing algebraic samples retain their exact values unless explicitly replaced.

Edit samples replays the same instructions with fresh branch choices. A failed
step retains the full template and its output separately from the visible valid
prefix. Reset restores the saved example (or the initial setup for a new draft).
Parameter identities stay fixed after setup; sample coordinates never become
permitted proof seeds. Save retains the editable command and exact sample source.

## Validation

- Session and Workspace passed full Lean LSP diagnostics and targeted builds;
  Saved also rebuilt after the Session refactor. The command/RPC module built
  successfully with the final JavaScript bundle. Long integration LSP requests
  timed out, so the targeted build supplied that module's final compiler check.
- SampleWorkspace passed full LSP diagnostics, including source round-trip with
  an untouched irrational input. Its executable checks passed for rational and
  line input validation, changed midpoint coordinates, seed isolation, reset,
  partial failure, recovery, parameter identity, and fresh branch choices.
- The browser harness passed its existing checks and new setup, exact request
  fields, sample editing, stale responses, failure/reset, point dragging, and
  two-click line placement regressions.
- One combined local check reused the maintained bodies of RecipeRuntime,
  SampleWorkspace, Widget, WidgetHistory, RecipeSetup, and Recipes under one
  import. `lake lean .lake/samples/Checkpoint.lean -- --run
  .lake/samples/Checkpoint.lean` exited successfully. Both runtime suites passed;
  saved proof examples compiled. Key soundness/identity theorems and the saved
  midpoint proof depended only on `propext`, `Classical.choice`, and `Quot.sound`.
  The separate maintained validation commands remain in scripts/validate.sh.
- The first plain `lake env lean` attempt lacked Hex's native arithmetic library;
  it was not counted as passing. The successful run used Lake's setup-aware
  runner. No Hex or dependency changes were needed.
- Live VS Code walkthrough in the existing LeanOrigami workspace: bare command,
  GUI naming and sample creation, midpoint recipe composition, changed-input
  replay (B = 2 gives midpoint 1), coincident-input failure, Reset recovery,
  saving and reopening with the changed samples and output preserved. Calling
  the saved recipe on proof seeds then submitted and saved a kernel-checked
  proof of one half; the reopened proof showed No goals.

Live startup caught an omitted-field RPC bug: structure defaults do not make
those JSON fields optional. Every browser request now sends the sample fields,
and the harness checks that contract. Short profiles also identified expensive
field inference; explicit types/calls improved those expressions.

## Audit

The implementation refactors the existing replay path and uses one shared
editor. Tests and the empty starter are separate from production modules.
No proof holes, new axioms, unsafe proof shortcuts, dependency changes, or CI
changes were introduced. Existing unsafe evaluation remains limited to loading
exploration data; proof submission still elaborates and checks its certificate.
The diff passed whitespace checks. User edits in Recipes.lean and .DS_Store were
preserved and excluded from this checkpoint.

Limits remain as planned: rational GUI replacements, replay on release rather
than continuous dragging, interactive branch selection, and exploration rather
than a universal theorem about a user recipe. Point dragging and line placement
were exercised in the browser harness; the live walkthrough used input fields.

The existing strict source-version guard can invalidate a reused earlier panel
after editing later declarations. Restart File refreshes its context. This was
observed after adding the proof below the recipe; the stale request was rejected.
