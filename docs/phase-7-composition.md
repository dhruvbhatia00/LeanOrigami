# Phase 7 checkpoint 5A — compositional recipe calls

Status: complete, 2026-10-15. This completes the approved shared refactor and
midpoint demonstration, not the remaining recipe migrations or all of Phase 7.

## Interface and mathematical audit

`Construction/Composition.lean` defines transitions containing primitive
instructions or retained calls. A `RecipeRule` states an exact input/output
relation and proves all outputs constructible from constructible inputs.
Registry lookup, reference resolution, and that relation are explicit premises
of a checked call. `Certified.sound` composes these proofs;
`Certified.replay_eq` connects the certified state to display replay;
`Certified.coordinate_sound` proves the existing real-number goal.
The original primitive checker and constructibility rules remain unchanged.

`Construction/Midpoint.lean` proves the A1/A2/intersection argument once. Its
rule requires two distinct points and exactly their coordinate midpoint as the
public output. Coincident inputs remain rejected, matching the existing recipe.
Call certificates apply this theorem without unfolding its geometric proof.

`Widget/Certificate.lean` derives rules from the actual saved template and
private history. The midpoint shortcut requires equality with the complete
registered template, not an editable label. Fallback certificates check the
body's operations against that template, recursively certify the body, and
select its public outputs. They prove constructibility; arbitrary user-written
output specifications still require separate theorems.

No new axioms, proof holes, `native_decide`, or numerical proof oracles were
introduced. Native execution proposes data; ordinary Lean checks the evidence.
The audited soundness and end-to-end theorems depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

## Editor and persistence

- `Widget/Recipe.lean` retains nested templates and validates references using
  each call's public output count.
- `Widget/Execution.lean` stores exact public outputs and scoped private history.
  Unchanged midpoint calls compute only their output; private folds are rebuilt
  lazily for inspection.
- `Widget/Session.lean` owns private child sessions, branch continuations,
  atomic call undo, and public reference allocation. Sample changes rediscover
  nested outputs. Private indices do not exist in the caller.
- `Widget/Export.lean` records only the arithmetic needed by the certificates.
  It shares coordinate serialization and primitive checking with the existing
  text exporter instead of duplicating those algorithms.
- `Widget/Saved.lean` stores the call tree and its certificate together.
  New saves use `origami composed`; legacy `origami saved` remains readable
  with its original primitive indices. The tactic remains editable and visible.

Only the default and additional named outputs enter the public scene. Inspect
opens a read-only private scene; Return to construction restores the caller.
Nested inspection is supported. The broader canvas-selection design remains
Phase 8 work.

## Validation

The targeted widget build passed after the shared refactor. Foundation modules
and scoped editing checks passed LSP/targeted builds. The JavaScript syntax and
adapter checks passed, including nested inspection, disabled editing controls,
and return to the unchanged selection.

Fresh native export covered expanded and retained quarter constructions, an
edited midpoint taking the primitive fallback, two public outputs, and an empty
history selecting a seed. A forged midpoint output was rejected.

The five freshly generated proofs and affected test sources passed together in
`.lake/composition/Compatibility.lean` using `lake lean` (exit status zero).
The temporary batch retained original namespaces and proofs and omitted only
duplicate executable `main` declarations. It covered history, requirements,
arithmetic, measurements/roots, recipe contracts, sample editing, branch choices,
legacy saved proofs, and the new certificates. Large WidgetRuntime/trisection
benchmark entry points were typechecked, not executed again. This was focused
validation, not a repeat of the full suite. All maintained tests and demos retain
paths through `scripts/validate.sh` and their library/demo targets.

The MCP restarted its worker between partial diagnostic reports, losing import
progress; the final combined check therefore used the CLI fallback. The correct
native command is `lake lean ... -- --run ...`; plain `lake env lean --run` did
not load Hex's native arithmetic implementation in this environment.

Live VS Code checks passed in `LeanOrigamiDemos/ComposedRecipes.lean`:

1. The saved tactic reopened with no goals, two calls and one ordinary fold.
2. Inspect displayed the midpoint's two folds and intersection, disabled editing,
   and returned to the unchanged caller.
3. The public midpoint and quarter points supplied an additional A2 fold,
   producing the exact crease x = 3/8.
4. Submit kernel-checked the edited proof; Save construction persisted it as a
   tactic and reopened the four-step construction with no goals.
5. Undo, submit, and save restored the compact three-step demo, again with no goals.

The three pre-existing unsaved buffers and on-disk user edits were preserved.
Arc remained open. Temporarily paused editor workers were resumed.

## Measurements and limits

Single illustrative native run; these are not general recipe benchmarks:

| Construction | Public steps | Discovery | Export | Source bytes | Proof heartbeats |
| --- | ---: | ---: | ---: | ---: | ---: |
| Expanded quarter | 7 | 87 ms | 88 ms | 3,478 | 60,687 |
| Retained quarter | 3 | 17 ms | 12 ms | 2,648 | 22,773 |
| Edited midpoint fallback | 1 | <1 ms | 44 ms | 3,082 | 27,566 |
| Two public outputs | 1 | <1 ms | 41 ms | 3,279 | 27,569 |
| Seed only | 0 | <1 ms | 1 ms | 898 | 2,370 |

Heartbeats measure proof elaboration work, not a separate kernel-only timer.
Source bytes measure the certificate expression before surrounding tactic/history
annotations. Cold imports/builds still took minutes per process on this machine;
they are excluded from discovery/export timings. Live interactions worked after
loading, but no precise display-latency benchmark was collected.

Only the unchanged midpoint currently uses a registered theorem shortcut. Other
recipes retain calls and public-output boundaries but still discover and certify
their private bodies. The primitive-only `RecipeContract` interface remains for
existing built-in specifications; this checkpoint does not provide automatic
universal specification proofs for arbitrary nested user recipes.

Next: migrate further recipe families to proved output rules, measure their
actual discovery and certification costs, and then revisit trisection. Separating
executable templates from heavy proof imports is a possible later startup-cost
improvement, not part of this delivery.

## Trying the demo

Open `LeanOrigamiDemos/ComposedRecipes.lean` and put the cursor on `origami` at
line 17. Expand Construction history, expand a midpoint, and choose Inspect.
Use Return to construction to continue editing. Only this new file was saved
during the live test.

Focused reproducible export and independent replay:

```sh
lake lean LeanOrigamiTests/CompositionExport.lean -- --run LeanOrigamiTests/CompositionExport.lean
lake lean .lake/composition/Replay.lean
```
