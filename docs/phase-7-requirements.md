# Phase 7 checkpoint 1 — requirements and authoring guidance

Status: complete, 2026-10-13.
Scope: PLAN.md 7.1–7.3. Checkpoints 2–4 are not included.

## Implementation

- Reset view and Refine display explain their effects on hover and keyboard
  focus. New sample inputs get editable, collision-free point/line names.
- `Construction/Condition.lean` is independent of widgets and Hex. Its small
  polynomial language has typed component references, rational constants,
  Boolean combinations, an executable checker, and interpretation proofs.
  Reference/denominator validation covers every Boolean branch; invalid input
  cannot become acceptable by negation or short-circuiting.
- `Widget/Requirements.lean` translates form selections into that language and
  generates readable descriptions and ordinary Lean source. The existing
  rational parser is shared with sample editing, rather than duplicated.
- `RecipeTemplate` separates editable input requirements from inherited checks
  at recorded primitive-step boundaries. Flattening relocates references and
  boundaries; undo removes checks with their owning call.
- `Session` enforces conditions during invocation/replay. `Workspace` retains
  full recipes on sample failure and supports editing requirements to recover.
  The existing widget exposes these shared APIs and distinguishes declared
  requirements from future proved specifications.

## Mathematical audit

Coordinates and canonical line coefficients supply exact values. Parallel
allows coincident lines; collinear allows repeated points. Distinctness can be
required separately. Zero normals are already excluded by `Line`.

`checkObjects_iff` states validity and the exact polynomial meaning.
`checkObjects_map_iff` proves agreement with geometry under ordered field
embeddings; its Scalar-to-real instance is exercised separately. Incidence,
point equality, and perpendicularity have direct geometric interpretation
lemmas. These proofs use only the usual Mathlib foundations, as checked by
`#print axioms` in the focused condition test file.

Requirements do not assert universal recipe correctness or successful execution
for every allowed input. Concrete construction certification remains the
existing kernel-checked primitive program. Branch policies and proved recipe
specifications belong to checkpoint 2.

## Validation record

Passed so far:

- Full LSP diagnostics for Condition, Requirements, Recipe, Session, and Workspace.
- Targeted dependency builds through Workspace and the final Widget bundle.
- `lake env lean LeanOrigamiTests/Conditions.lean`: exact geometry, invalid
  references/kinds/denominators, Boolean combinations, boundary cases, reference
  timing, and key theorem axiom dependencies.
- `node --experimental-vm-modules scripts/widget-construction-test.mjs`: existing
  interaction regressions plus names, collisions, hover/focus help, requirement
  form/RPC fields, and removal during a failed replay.

- `lake lean LeanOrigamiTests/RecipeRequirements.lean`: nested reference/timing
  preservation, exact output, grouped undo, changed-sample rejection, retained
  replay recovery, OR replacement, wrong-kind rejection, irrational polynomial
  decisions, Scalar-to-real theorem instantiation, and Lean source round-trip.

- Live VS Code checks in a temporary copy of `Demos/Requirements.lean`:
  automatic A/B/ℓ₁ names; named input selection; exact satisfied/failed statuses;
  midpoint invocation and inherited requirement display; off-axis sample
  rejection with zero executed steps; reset restoring all three steps; keyboard
  explanations; save/reopen retaining the condition, inherited check, and result
  `(1, 0)`. The corrected public demo's unchanged prefix matches this live copy.
- The live check found a duplicate displayed inherited row after reopening.
  Its saved data still contained one check. Distinct React sibling keys fix the
  reconciliation error; the focused browser regression now checks this collision.

The final widget declaration uses `ProofWidgets.Component` explicitly to avoid
shadowing by the geometric component type. The example's sample annotation was
also corrected during validation. No Hex, toolchain, or dependency changes were
needed. The final widget build passed after the React-key correction; its
compiled artifact contains the corrected keys. The functional live flow was
checked before that final display-only correction; its regression was checked
in the browser harness rather than repeating the long editor import load.

The full integrated phase suite is deliberately reserved for checkpoint 4,
following the user's light-testing instruction. Fresh widget/demo processes
spent several minutes initializing Lean's imported compiler cache; a one-second
stack sample confirmed this was import setup, not condition or fold evaluation.

## Deliberate limits

The GUI polynomial form uses one selected coordinate, at most 32 rational
coefficients, and comparison with zero. The Lean data language also supports
polynomials in multiple typed components. Arbitrary Lean predicates, custom
checker registration, angle families, output contracts, and branch policies
are outside this checkpoint. A sample passing its requirements is not a proof
of a recipe specification.
