# Phase 0 feasibility audit

Status: Phase 0 complete, audited on 2026-10-07. The dependency build and all semantic,
runtime, and widget experiments passed. Geometry and construction
certification are later phases.

## Preservation and reset

The full previous tracked project, modified README, and approved AGENTS.md
and PLAN.md were committed as `679c96345f0466dc3515d9068401a7ccc37388dd`.
The branch `archive/pre-restart-2026-10-06` was pushed to origin and its hash
verified with `git ls-remote` before removing the old implementation.
The new work lives on `restart/phase-0`.

## Dependency baseline

| Component | Pinned version or revision |
| --- | --- |
| Lean | `leanprover/lean4:v4.35.0-rc3` |
| HexNumberFieldMathlib | `b8ce919449329ba3b758d434147b222c69380695` (v0.7.0) |
| HexNumberField | `2a179b1ccfced4e7739aa1c8a8f6c19f75fd502a` (transitive) |
| Mathlib | `d870b9068518a0870842d15a0cd42637ec30b587` |
| ProofWidgets | `c643bbb3c24f8a25f9c14e3a6b1ceb13d01f3de1` |
| Batteries | `33131f4fb10067cb3009bf4db615d9680c1ccd6b` |

The committed Lake manifest fixes the remaining transitive dependencies.
Library, proof tests, and widget demos have separate Lake targets; runtime
and editor harnesses are checked by `bash scripts/validate.sh`. The default
library target stays small. A manual-only CI workflow invokes the full validation script if requested.
Per the user’s 2026-10-07 direction, checkpoints use local validation and
pushes serve version control; no GitHub Actions run is requested.

## Scalar interface and certification decision

Use the released `Hex.AlgebraicNumber` backend restricted to values satisfying
its exact `isReal` test. Phase 1 will turn this subtype into the public scalar
API. Do not depend on an unreleased standalone real-algebraic implementation.
`Feasibility.lean` probes an injective interpretation into Mathlib's `ℝ`,
compatibility of executable order, and closure under addition. It is not yet
a complete ordered-field adapter.

Hex supplies polynomials with algebraic coefficients and root completeness
statements over Mathlib's `ℂ`. Filter by exact reality and retain exact root
identity. Principal complex radicals are not a general real-root selector:
for example, negative real cubics must use the real branch rather than assume
that the principal complex cube root is real. The zero polynomial has `.all`
roots; a failed search is a separate outcome.

Prefer compact kernel-checked proofs using Hex's correspondence and algebraic
laws over reducing an entire root search inside the kernel. Runtime tests are
not certificates. No runtime Boolean or approximate display value is used as
a proof premise. Concrete fold certificates and their performance remain a
later-phase obligation.

Dyadic approximation has a proved containment guarantee. Rendering can convert
the dyadic center through rationals to floats, while keeping the exact scalar
as the object's identity. Floating conversion itself is only a display step.

## Widget boundary

The prototype proves a trivial goal before offering a link that inserts `rfl`.
The link uses the pinned ProofWidgets component and a versioned source edit.
The interaction harness executes the shipped JavaScript against a minimal
editor adapter, then checks the inserted proof in a separate Lean process.
The adapter rejects a stale document version. The click test and independent
Lean replay both passed; the replay imports no widget code.

This is not a visual test in VS Code or a complete origami canvas. In
particular, the real editor's stale-edit behavior and the full asynchronous
interaction lifecycle still need host integration testing in the widget phase.

## Build observations

On this Apple M2 with 8 GB RAM, serialize dependency builds with `LEAN_NUM_THREADS=1`. Some Hex bridge
modules import all of Mathlib, making concurrent imports costly on this machine.
Mathlib's cache fetched 8,947 artifacts successfully; Hex modules build from
source. An already-running Lean 4.30 server survived the toolchain change and
wrote incompatible artifacts into the new build tree. It was stopped, the
Mathlib cache restored with `lake exe cache unpack!` (36.8 seconds), and the
affected Hex traces invalidated for rebuilding. The editor also restarted automatic dependency builds after server termination;
it was temporarily paused to prevent duplicate jobs. These incidents are not
a useful cold-build benchmark. Restart existing Lean servers after changing toolchains.

The Lean MCP initially timed out during dependency compilation. Once restored,
it checked the complete widget file successfully and reported the registered
`SubmissionPanel` at the tactic token. The prototype theorem has no axiom
dependencies. The idle server was then closed to conserve build memory. CLI
diagnostics remain the documented fallback when the server is unavailable.

The runtime probe is a separate native executable (`lake exe phase0-runtime`).
An initial `lake env lean --run` attempt failed to load a native Hex symbol;
that invocation is not the supported validation path. The executable target
lets Lake build and link its native dependency graph explicitly.

A Reservoir lookup for the exact HexNumberFieldMathlib revision and
`arm64-apple-darwin24.6.0` / Lean 4.35.0-rc3 returned “outputs not found”.
The pinned Hex CI restores its own Linux build outputs and fetches Mathlib
separately. No compatible published Hex cache was established for this Mac.

## Runtime measurements

The compiled executable completed every assertion successfully. The user’s
completed validation run reported the following elapsed times (1 ms clock
resolution; zero means below that resolution):

| Experiment | Elapsed |
| --- | ---: |
| Rational inverse and order | 0 ms |
| Construct principal square-root values | 0 ms each |
| Irrational arithmetic sequence, including inversion | 41 ms |
| Roots of `x² - √2`, equation checks and signs | 37 ms |
| Roots of `x³ - 2`, real filtering and equation check | 18 ms |
| Zero-polynomial classification | 0 ms |
| 40-bit approximation and float conversion | 0 ms |

The display value was `1.414214`. Square-root construction alone may defer
work internally; the identity and root-solving tests exercise the values.
These are feasibility observations, not worst-case performance guarantees.

## Proof checking and interpreter measurements

Reproducing the kernel profile after building imports:

```sh
LEAN_NUM_THREADS=1 lake env lean -Dtrace.profiler=true \
  -Dtrace.profiler.threshold=0 LeanOrigamiTests/Feasibility.lean
```

The completed run reported these `Kernel` trace times:

| Declaration | Kernel time |
| --- | ---: |
| Real interpretation injectivity | 0.791 ms |
| Real order correspondence | 0.776 ms |
| `sqrtTwo_sq` | 0.340 ms |
| `irrational_sequence` | 14.982 ms |
| Algebraic root membership correspondence | 0.090 ms |
| Approximation containment | 0.366 ms |

The irrational proof elaboration took 151.465 ms separately. These timings
check new declarations against compiled dependencies; they do not recheck
all imported proofs or include import startup. The CLI invocation took
several minutes overall, so kernel time must not be confused with interactive
startup latency. The compact proof path is feasible for this example, not a
performance guarantee for arbitrary root certificates.

The maintained interpreter suite passed with 219 ms for the irrational
sequence, 203 ms for the algebraic quadratic, and 95 ms for the cubic.
Compiled and interpreted runs both perform exact arithmetic; neither test
result is admitted as theorem evidence.

## Validation and remaining boundaries

The user completed `LEAN_NUM_THREADS=1 bash scripts/validate.sh`: Lake
reported success for all 9,933 jobs (including reused dependencies), all
runtime assertions passed, and the widget click harness passed. A separate
check of the maintained `Interpreter.lean` also passed through `lake lean`;
this path is now included in the validation script. It checks the native
library loading needed by elaborator execution, reusing the runtime suite.
The generated standalone widget proof was checked independently.

The seven printed axiom reports in `Feasibility.lean` contain only
`propext`, `Classical.choice`, and `Quot.sound`. The widget submission theorem
has no axioms. No project proof holes or unproved axioms were introduced.
Runtime assertions remain separate from theorem evidence.

The real subtype is a feasibility probe: its full ordered-field API remains
Phase 1 work. Arbitrary selected-root certificates and concrete construction
replay remain later work; these experiments do not benchmark that complete
pipeline. Actual editor integration still requires a visual host test.
Upstream linter warnings were replayed by Lake; they are not new project
errors and do not mean those dependencies rebuilt.

Checkpoint audit: the archive, reproducible pins, separate validation paths,
backend experiments, proof/runtime measurements, and widget insertion
prototype satisfy Phase 0. Reviewed module separation, public documentation,
source proof-hole scan, transitive axiom reports, and final diff. No changes
to later-phase acceptance criteria were made. Validation was local; no
GitHub Actions run was requested.
