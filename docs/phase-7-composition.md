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

At checkpoint 5A, only the unchanged midpoint used a registered theorem shortcut. Other
recipes retain calls and public-output boundaries but still discover and certify
their private bodies. The primitive-only `RecipeContract` interface remains for
existing built-in specifications; this checkpoint does not provide automatic
universal specification proofs for arbitrary nested user recipes.

The next migration was authorized and implemented as checkpoint 5B below. Separating
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


## Checkpoint 5B — all existing library families

Status: complete. Implementation, fresh generated replay, affected integration
checks, tactic-source cleanup, and live save/edit/reopen checks passed.

All 16 built-ins now share one public-output rule interface: midpoint, six
arithmetic operations, four projections/transfers, two distances, square/cube
roots, and trisection. The existing geometric execution theorems establish
constructibility once. Each call supplies its exact inputs, outputs, and root
witnesses to that theorem; it does not unfold the private execution proof.

### Where the code lives

- `Widget/LibraryRules.lean`: complete-template recognition, exact public-output
  relations, and their constructibility theorem. Trisection exposes two endpoints
  and two lines, for either orientation of a nondegenerate angle.
- `Widget/LibraryDiscovery.lean`: direct exact output formulas and branch-aware
  real-root discovery. The same formulas run for preview and arithmetic recording.
- `Widget/LibraryCertificate.lean`: recorded witnesses, adaptive rational bounds,
  and generated proof source. Discovery results alone are never accepted as proof.
- `Scalar/Bounds.lean`: kernel-checkable sign theorems for number-field coordinates.
- `Widget/Execution.lean` and `Certificate.lean`: the compact history node and its
  binding to the complete saved template. The old call constructor stays readable.
- `Widget/Session.lean`, `Workspace.lean`, and `Export.lean`: invocation, private
  inspection, requirement display, and saved certificates.
- `LeanOrigamiTests/LibraryExport.lean`: all-family, nested-call, cubic-reuse,
  forged-output, and small-sign regression cases. It generates independent proofs.

Edited/custom recipes retain checked private bodies. Recognized library calls
inside them still use compact certificates. This does not automatically prove
universal user-written specifications. Inspect may still expand a long original
construction; normal invocation and proof submission do not.

The prototype replay checks a right-angle irrational coordinate, all arithmetic
and measurement families in one construction, a cubic-angle coordinate reused to
prove its cubic identity, and a positive coordinate needing 128-bit sign bounds.
Their transitive axiom lists contain only `propext`, `Classical.choice`, and
`Quot.sound`. Fresh generated artifacts also passed independent replay, including
a zero target and earlier saved-proof compatibility cases. The final tactic-source cleanup also passed a targeted widget build, native
regeneration, and independent replay of all five library proofs, without
generated-proof warnings.

The local persistent Lean server avoided repeated cold imports during proof
iteration after the MCP's 300-second transport timeout kept restarting workers.
This is a tool fallback, not a change to the project or its proof foundations.
Cold imports remain a separate machine/resource limitation.

Reproduce the new export and independent replay with:

```sh
LEAN_NUM_THREADS=1 lake lean LeanOrigamiTests/LibraryExport.lean -- --run LeanOrigamiTests/LibraryExport.lean
LEAN_NUM_THREADS=1 lake lean .lake/library/Replay.lean
```

### Validation and performance evidence

The affected native integration batch passed the maintained scoped-recipe,
arithmetic, measurement, composition-export, trisection, and new library-export
checks. It covered changed samples, clockwise obtuse and translated angles,
all four trisection outputs, invalid domains, undo, private-index rejection,
edited-definition fallback, nested library calls, and forged-output rejection.
An independent Lean process checked freshly generated library and composition
proofs, the trisection replay, and the older saved composition demo. The browser
component regression script also passed. This was an affected-check batch, not
another full repository validation run; checkpoint 4's earlier full build and
integration results remain recorded in its audit.

After the final tactic-source cleanup, one native run measured:

| Construction | Public steps | Discovery | Export | Certificate bytes |
| --- | ---: | ---: | ---: | ---: |
| Right-angle trisection | 8 (including 7 frame steps) | 192 ms | 193 ms | 7,807 |
| All arithmetic/measurement families and nested calls | 26 | not separately timed | 225 ms | 34,268 |
| Cubic-angle trisection followed by arithmetic | 23 | not separately timed | 2,132 ms | 25,844 |

These are illustrative single-run measurements under memory pressure, excluding
cold imports/builds. Final proof elaboration took 131,231, 377,977, and 257,748
heartbeats respectively; these are not separate kernel-only timings. A tiny
positive coordinate required 128-bit rational bounds, and a zero target was
checked separately. All audited soundness and end-to-end theorems depend only
on `propext`, `Classical.choice`, and `Quot.sound`.

The final source cleanup centralizes field selection in
`origami_library_arithmetic`, avoiding dead fallback tactics in generated proofs.
It does not disable linters or change the mathematical output relations.

### Live verification and completion audit

The updated trisection workspace displayed one call and all four named outputs.
Changing the second ray to (0, -1) recomputed clockwise outputs approximately
(0.866025, -0.5) and (0.5, -0.866025), with their two lines. The saved right-angle
proof reopened with no goals and eight public steps. Adding a midpoint between
the origin and the first trisector endpoint produced (0.433013, 0.25) as one
additional public step. Inspect displayed its three private steps read-only;
Return restored the unchanged caller. Submit checked the complete proof, Save
retained the `origami` tactic, and returning to that tactic restored nine steps,
the chosen final coordinate, and no goals. This used a temporary test file in
the existing project; the three unsaved user buffers were preserved.

The mathematical audit checked complete-template binding, exact public identities,
nonzero/branch assumptions, all four trisection outputs, and fallback behavior.
No proof holes, new trusted axioms, or approximate proof evidence were introduced.
The common discovery implementation serves both preview and arithmetic recording;
separate modules own the library relations, discovery, certificate source, and
scalar bounds. Obsolete midpoint-only computation helpers were removed while
keeping the earlier saved-proof format readable. Tests and demos remain separate.

This closes Phase 7 checkpoints 4 and 5, including the performance follow-up.
Phase 8 remains the approved next UI work. General user-recipe theorem synthesis,
shorter private visual explanations, and cold-import optimization are not claimed
as completed features.

To explore the public-output demo, open `LeanOrigamiDemos/Trisection.lean` and
place the cursor on `origami_recipe` at line 37. Use Edit samples to vary the rays.
