# Phase 5 audit: named constructions and saved proofs

## Scope and implementation

The public entry point is `LeanOrigami.Text`. The mathematical library remains
independent of the text elaborator, and importing the text interface does not
load Hex. No dependency or toolchain versions changed.

- `Text/Certified.lean` carries exact real values together with the existing
  geometric construction evidence. Its seven fold operations require both
  the chosen crease's geometric relation and finite-choice admissibility.
  Intersections require incidence on both lines and a nonzero determinant.
- `Text/Syntax.lean` provides named, typed instructions, exact `choose` values,
  optional `proving` certificates, reusable helpers, and final submission.
  Each instruction is checked even if its output is never used. Names cannot
  shadow earlier bindings; failures carry their instruction number.
- `Text/Artifact.lean` preserves exact source with its prerequisite imports,
  definitions, and certificates. Its versioned JSON round-trips this source;
  reopening writes a standalone Lean file and rechecks the named theorem and
  its transitive axiom dependencies. JSON decoding itself proves nothing.

Arithmetic and root commands reuse the construction algorithms proved in
Phases 3 and 4. They check the actual input histories and chosen roots, rather
than supplying an unrelated theorem about the final target. Square roots
include a nonnegative sign condition. Quadratic and cubic commands require a
nonzero leading coefficient; the lower-degree operations remain distinct.

## Acceptance evidence

Phase 5 passed local validation on 2026-10-09:

- Completed LSP diagnostics for the implementation, primitive tests, examples,
  and persistence test, with no new errors or warnings.
- `lake build LeanOrigami.Text LeanOrigamiDemos.Text` and the focused
  `LeanOrigamiTests.Text` build passed.
- `LEAN_NUM_THREADS=1 bash scripts/validate.sh` exited successfully. This
  includes every maintained library/test/demo target, compiled runtime and
  Hex interpreter checks, widget insertion/replay, artifact file/JSON round
  trips, and fresh replay of `.lake/phase5/TextReplay.lean`.
- The exported square-root, cube-root, iterated-root, and trisection proofs
  reported only `propext`, `Classical.choice`, and `Quot.sound` dependencies.
  The primitive and reordered-choice examples passed the same audit.
- Source and diff checks found no proof holes, new project axioms, native
  decision proofs, unrelated edits, or dependency changes. Existing pinned
  dependency warnings and Node's VM-module notice remain.

The maintained acceptance paths are:

| Criterion | Evidence |
| --- | --- |
| All seven primitives, typed names, intersections | `LeanOrigamiTests/Text.lean`: `all_rules`. |
| Exact branch identity independent of enumeration | The quadratic test selects the same exact root from both candidate orders and checks equality of resulting values. No command stores a candidate index. |
| Reusable construction and substantial Phase 4 examples | `LeanOrigamiDemos/Text.lean`: doubling helper, √2, ∛2, √√2, and the complete trisection point. |
| Invalid references, wrong kinds, duplicate names | Separate negative examples in `LeanOrigamiTests/Text.lean`. |
| Invalid folds, macro inputs, and targets | Negative examples cover a crease missing its inputs, an underconstrained fold, zero division, a negative square-root choice, zero quadratic leading coefficient, and wrong final coordinate. |
| Persistence and fresh replay | `LeanOrigamiTests/TextPersistence.lean` writes, loads, compares, and exports the artifact; `scripts/validate.sh` checks the emitted source in a new Lean process. |
| Kernel trust | Per-instruction checks, artifact declaration checks, and printed transitive axiom reports. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted. |

The standalone export includes the example proofs themselves, not an import
of the text demo module. Its imports supply the mathematical prerequisites.
This tests reconstruction of the saved instructions without an editor or GUI.
The artifact is a complete source prefix, not a minimal dependency extraction.

## Findings and limits

The rejection tests exposed name shadowing and Lean's recovery from failed
nested certificates. The elaborator now checks the active goal's local
context and rejects unfinished evidence at each instruction. It restores
failed elaboration state before reporting the error, so callers can catch a
failed construction without leaving placeholder proofs behind.

The exact symbolic proof path and executable Hex path have different jobs.
`Program Scalar` and `Scalar.folds` still perform native exploration and
candidate discovery. The new interface checks exact expressions and supplied
certificates. Routine arithmetic is automated; difficult identities may need
explicit proofs. There is no general automatic conversion of an arbitrary
opaque Hex output into a short symbolic certificate. That remains an
integration concern for the GUI; it must not be hidden by trusting native
success flags.

The candidate-order test uses a small exact integer candidate list to vary
presentation order. It tests the text boundary, not Hex's enumeration
implementation, which was covered by the earlier discovery checks.

No GUI canvas, float rendering, or new mathematical characterization theorem
is included in this phase. Phase 6 has not started.
