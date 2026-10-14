# Phase 7 checkpoint 3 audit

Status: checkpoint 3 complete (2026-10-14). Broad phase validation remains for checkpoint 4.

## Design

`Construction/CoordinateRecipe.lean` contains axis projections and signed
coordinate transfer. `Construction/RootOperation.lean` constructs square roots
with A5 and cube roots with A6, then extracts the crease parameter using folds
and intersections. A chosen root is output data, never an additional seed.
`Construction/DistanceRecipe.lean` composes coordinate extraction, arithmetic,
and the nonnegative square root to transfer a distance to either axis.

Each program has an execution theorem identifying its actual output.
Square roots require a nonnegative radicand and select the nonnegative root.
Cube roots accept every real scalar, including negative values and zero.
Distances accept coincident points. Coordinate transfer retains the sign;
distance transfer does not.

`Scalar/RootOperations.lean` proves existence of the needed exact scalar roots
using the complete algebraic root finder and its real interpretation.
`Construction/MeasurementSemantics.lean` identifies the polynomial distance
specification with Mathlib's Euclidean distance and the square-root specification
with `Real.sqrt`. These interpretations are proofs, not executable real arithmetic.

`Widget/Frame.lean` shares the explicit standard-frame requirements with the
arithmetic library. `Widget/Measurements.lean` supplies the eight menu templates,
input requirements, output conditions, and universal contracts. Its erasure
theorem connects each template to the same primitive program covered by the
execution proof. Its square-root branch condition is a polynomial sign test;
the uniqueness theorem identifies exactly the nonnegative solution. Cube-root
creases are unique. Neither policy remembers a sample's branch number.

## Validation so far

- Complete file-level diagnostics passed for the construction proofs, scalar
  existence bridge, real interpretation, and measurement template contracts.
- Targeted measurement and widget builds passed on 2026-10-14.
- `MeasurementRecipes.lean` passed complete LSP diagnostics without errors or
  warnings. It covers all eight operations, signed/off-axis coordinates,
  nonzero and zero distance, zero/irrational square roots, rational and
  irrational negative cube roots, nested multiplication, invalid root inputs,
  changed-sample rejection/recovery, and saved-template round-trips.
- The execution theorem, template erasure and contract, both root branch
  policies, and Euclidean distance interpretation depend only on `propext`,
  `Classical.choice`, and `Quot.sound`. A source scan found no proof holes or
  native-decision certification in the new modules.
- Live standalone sample replay passed: zero produced `(0, 0)`, a negative
  radicand displayed the failed nonnegativity requirement and hid downstream
  results, and changing it to four restored all 39 steps with output `(2, 0)`.
  Live proof submission and saved-tactic replay also passed: the square-root
  theorem closes and reopening restores all 53 steps and the selected result.
  A separate LSP worker checked the exact saved demo source together with
  `LeanOrigamiTests/Widget.lean`, including the expired-context regression.
  Its complete diagnostics had no errors or warnings. The saved theorem uses
  only `propext`, `Classical.choice`, and `Quot.sound`. The combined temporary
  replay avoided loading the same imports twice; each maintained file remains
  on the normal full-phase validation path. Full phase integration is reserved
  for checkpoint 4.

The live proof walkthrough constructed the standard frame, added `1 + 1`, and
ran the square-root recipe with automatic branch selection (53 primitive
steps). Submission exposed a resource-context bug: Core retained the default
200,000-heartbeat ceiling even though the generated term requested 4,000,000.
The fix gives RPC certification and saved-tactic replay the same fresh, bounded
construction budget and passed complete widget-file LSP diagnostics and a
targeted build. Live resubmission and reopening, separate-worker replay of
the exact saved source, and the expired-context regression all passed.
The saved demo is included in the documented `LeanOrigamiDemos` build target.

The earlier `RootRecipe.squareRoot` retains its cubic-embedding construction
for the existing explicit-program demonstrations. The new visual operation
uses a direct A5 construction and a universal execution theorem. Both use the
same primitive checker and root geometry; no alternate solver or certification
path was introduced.

## Audit outcome

All eight operations have primitive execution proofs, precise output meanings,
valid-input existence proofs, and matching visual templates. The root branch
policies are exact and independent of sample enumeration order. The common
frame requirements were extracted rather than duplicated. Tests and the saved
visual proof remain outside library modules. The diff and proof-hole scans
passed; unrelated user changes were preserved. A module-docstring heading was
corrected after validation; no executable or proof code changed afterward.

The existing cubic-based square-root demonstration remains supported. Broad
integration and the angle family belong to checkpoint 4; the agreed visual
design pass remains deferred until after Phase 7.
