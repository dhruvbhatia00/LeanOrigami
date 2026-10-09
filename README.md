# LeanOrigami

A fresh Lean formalization of origami constructions, with exact algebraic
computation and a planned proof-producing graphical interface.

The restart follows [PLAN.md](PLAN.md) and [AGENTS.md](AGENTS.md). The library
provides exact real algebraic coordinates, normalized lines, reflection,
intersection, and the seven fold relations. Replayable construction programs
now certify all seven rules and unique intersections. The library includes exact candidate discovery, arithmetic, and quadratic/cubic
root constructions. Phase 5 adds named text commands and saved proof artifacts. The origami GUI is a later phase.

## Setup

Install [elan](https://github.com/leanprover/elan), Git, and Node.js 22 or newer.
The pinned Lean toolchain is installed automatically on first use.

```sh
lake exe cache get
lake build
```

On an 8 GB machine, use `LEAN_NUM_THREADS=1 lake build` for dependency builds.
The full-validation script defaults to one thread and accepts an override.

The manifest records exact revisions. Do not run `lake update` merely to
refresh diagnostics: normal development uses the committed manifest and
`lake build`. The initial Hex build can take substantially longer than
subsequent builds; Mathlib should come from its binary cache. Restart open
Lean editor sessions after a toolchain change so an old server cannot write
incompatible build artifacts.

Compiled dependency files avoid rebuilding Hex, but a fresh Lean process
still loads its imports. Keep an LSP session open while working in one file,
build the changed module before switching files, and reserve full validation
for checkpoints. Import the smaller geometry modules when Hex is not needed;
avoid simultaneous builds and repeated server restarts on an 8 GB machine.

## Validation

The default build checks the library. Tests and demos have separate targets:

```sh
lake build LeanOrigamiTests LeanOrigamiDemos
bash scripts/validate.sh
```

The validation script checks the library, text interface, tests, and demos, runs
the arithmetic and root experiments, round-trips saved text proofs, exercises the pinned ProofWidgets insertion handler, and checks
the resulting standalone Lean proof. It requires no npm installation. Checkpoints are validated locally;
the GitHub Actions workflow is manual-only and does not run on pushes.

To run only the arithmetic experiment after building its imports:

```sh
lake exe phase0-runtime
```

`Geometry.lean` contains examples of all seven fold rules and geometric
boundary cases. `Feasibility.lean` checks the public scalar and exact geometry
interfaces alongside the original Hex experiments. Both print axiom reports.
`Runtime.lean` contains executable assertions and timing output; these tests
are not proof certificates.

`Interpreter.lean` exercises the public scalar, geometry, and construction
operations through `#eval`. It omits the older runtime suite for focused
development checks; full validation still runs that suite as `phase0-runtime`.
Run it with
`lake lean LeanOrigamiTests/Interpreter.lean`; Lake supplies the required
native libraries. This check is also included in the validation script.

## Widget prototype

Open `LeanOrigamiDemos/Widget.lean` in a Lean editor and place the cursor on
`origami_phase0` in `submission_example`. Its panel offers an insertion link
that replaces the tactic with `rfl`. The tactic checks that proof before
presenting it. Save and reopen the file to confirm the ordinary proof works.

The automated interaction harness uses the shipped ProofWidgets JavaScript
with a minimal editor adapter; it exercises the click event, versioned edit,
and independent replay. It does not replace a visual test inside VS Code.
The full origami canvas is a later phase.

## Preservation

The previous implementation, README edits, and approved planning documents
are preserved at commit `679c96345f0466dc3515d9068401a7ccc37388dd` on the
pushed branch
[`archive/pre-restart-2026-10-06`](https://github.com/dhruvbhatia00/LeanOrigami/tree/archive/pre-restart-2026-10-06).
The restart is developed on `restart/phase-0`.

See [the Phase 0 audit](docs/phase-0.md) for dependency findings,
measurements, and validation status.

## Geometry modules

Import `LeanOrigami` for the mathematical and executable API. Import
`LeanOrigami.Text` for the proof-producing text commands. Coordinate geometry can
also be imported without Hex, for example `LeanOrigami.Geometry.Reflection`.
It is shared between exact scalars and the real plane. The real interpretation
proves equality with Mathlib's reflection and perpendicularity notions.

Fold relations describe a proposed crease. Legal selections additionally
require finitely many solutions over the whole real plane. These definitions alone do not establish a construction history; the
construction and solver modules provide those additional guarantees.

See [the Phase 1 audit](docs/phase-1.md) for module responsibilities,
exceptional cases, validation status, and the remaining later-phase work.

## Construction programs

Open `LeanOrigamiDemos/Subdivision.lean` for a complete text example. It starts
with `(0,0)` and `(1,0)`, constructs the axes, and constructs the points
`(1/2,0)`, `(1/4,0)`, and `(3/4,0)`. Every instruction saves its requested
operation, references to earlier objects, and an exact selected output.
Indices 0 and 1 name the seeds; each instruction appends one object.

`Program.run` checks the program and returns its objects or a structured
error. `Program.accepts` additionally checks a selected final coordinate
against a target. `Program.accepts_sound` turns a kernel-checked acceptance
proof into a theorem that the requested real number is constructible.
The demo uses exact rationals with `decide +kernel` for small certificates;
`Interpreter.lean` executes the same recipe using Hex's `Scalar`. Runtime
assertions are separate from proof evidence.

The standard Lean data syntax is the initial text interface. The program
format supports all seven fold requests. Missing or wrong-kind
references, underconstrained folds, non-unique intersections, forged outputs,
and target mismatches are rejected.

The construction module guide, data flow, and audit are in
[the Phase 2 report](docs/phase-2.md). To check just the new proofs and demo:

```sh
lake build LeanOrigamiTests.Construction LeanOrigamiDemos.Subdivision
```

## Phase 3 modules

Phase 3 passed full local validation and its [audit](docs/phase-3.md).
The main entry points are:

| Open this file | To find |
| --- | --- |
| `Scalar/Roots.lean` | Exact real roots of algebraic polynomials, including zero-polynomial classification. |
| `Scalar/FoldDiscovery.lean` | `Scalar.folds`, its soundness and completeness over all real creases, and duplicate removal. |
| `Solvers/Candidates.lean` | Candidate formulas and finite-choice guards for all seven rules. |
| `Solvers/LineLine.lean`, `PointLine.lean`, `Perpendicular.lean`, `Cubic.lean` | The geometry and exceptional cases for rules 3, 5, 7, and 6. |
| `Solvers/Equations.lean` | Polynomial meanings of reflection and guarded cubic elimination. |
| `Solvers/Certified.lean` | Checking a saved crease without repeating root discovery. |
| `Construction/Basis.lean`, `Coordinates.lean`, `Arithmetic.lean` | The coordinate basis, coordinate/point equivalence, and arithmetic construction theorems. |
| `Construction/Recipe.lean`, `ArithmeticRecipe.lean` | Reference remapping, recipe expansion, and executable arithmetic recipes. |

`Scalar.folds input` returns `none` for an infinite family, `some []` for no
solution, and `some choices` for a finite list of distinct exact creases.
Discovery does not choose a sequence of operations. A caller chooses one
crease and saves it in an ordinary construction instruction.

For examples, open `LeanOrigamiDemos/OffAxis.lean`, `AllFolds.lean`, or
`Arithmetic.lean`. The arithmetic demo composes four recipes and checks the
expanded program in Lean's kernel. `LeanOrigamiTests/Interpreter.lean`
contains native Hex checks, including exact choice counts and irrational
coefficients; these runtime results are not proof premises.

## Phase 4 modules

Phase 4 passed local validation and its [audit](docs/phase-4.md).

Root constructions extend the field operations: every real root of a quadratic
or cubic with constructible coefficients is constructible. A root can become
a coefficient of another construction. Being a Hex scalar alone still gives
no construction evidence.

| Open this file | To find |
| --- | --- |
| `Construction/RootGeometry.lean` | The coefficient configuration, its exact cubic equivalence in both directions, and finite admissibility. |
| `Construction/Roots.lean` | Coefficient provenance, root extraction, cubic/quadratic/linear closure, and nonnegative square roots. |
| `Construction/RootRecipe.lean` | Executable recipes using coefficient references and a selected exact root. |
| `LeanOrigamiDemos/Roots.lean` | Kernel-checked square-root, cube-doubling, iterated-root, and 60-degree trisection theorems. |
| `LeanOrigamiDemos/RootPrograms.lean` | Saved programs for those examples, including both coordinates of the trisection point. |
| `LeanOrigamiTests/RootConstructions.lean` | Kernel replay, nonmonic and repeated roots, branch guards, and degenerate cases. |
| `LeanOrigamiTests/RootInterpreter.lean` | Native Hex replay of the irrational programs; assertions are not proof premises. |

Run the focused native integration checks with
`lake lean LeanOrigamiTests/RootInterpreter.lean`.
Full validation includes this command. Mathematical construction proofs and
native integration checks are separate: no native assertion is used to close
a Lean theorem. The trisection identification theorem connects exact polynomial,
interval, and unit-circle conditions to the named point at angle `π/9`.

## Phase 5 text interface

See [the tutorial](docs/text-interface.md) for the command syntax and saving
proofs, and [the audit](docs/phase-5.md) for validation and limitations.
The text entry point is separate so symbolic proof files do not load Hex.

| Open this file | To find |
| --- | --- |
| `LeanOrigami/Text/Certified.lean` | Points, lines, and numbers carrying construction evidence; checked operations and final submission. |
| `LeanOrigami/Text/Syntax.lean` | Named `origami` commands, certificate tactics, and instruction errors. |
| `LeanOrigami/Text/Artifact.lean` | Exact source capture, versioned JSON, saving, loading, and standalone proof export. |
| `LeanOrigamiDemos/Text.lean` | Square root, cube doubling, iterated roots, trisection, and a reusable helper through the new interface. |
| `LeanOrigamiTests/Text.lean` | All seven primitives, candidate-order independence, and rejected constructions. |
| `LeanOrigamiTests/TextPersistence.lean` | File round trips and generation of a fresh replay file. |

For focused validation:

```sh
lake build LeanOrigami.Text LeanOrigamiTests.Text LeanOrigamiDemos.Text
lake env lean LeanOrigamiTests/TextPersistence.lean
lake env lean .lake/phase5/TextReplay.lean
```

Each saved choice is an exact expression with a kernel-checked certificate.
Routine arithmetic is automated; more difficult identities can use explicit
`proving (by ...)` arguments. The interface does not yet automatically translate
arbitrary native Hex outputs into symbolic certificates. The canvas remains
Phase 6 work.
