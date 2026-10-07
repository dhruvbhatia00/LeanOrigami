# LeanOrigami

A fresh Lean formalization of origami constructions, with exact algebraic
computation and a planned proof-producing graphical interface.

The restart follows [PLAN.md](PLAN.md) and [AGENTS.md](AGENTS.md). Phase 0
establishes dependency and interface feasibility; it does not yet implement
geometry or an origami tactic.

## Setup

Install [elan](https://github.com/leanprover/elan), Git, and Node.js 22 or newer.
The pinned Lean toolchain is installed automatically on first use.

```sh
lake update
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

## Validation

The default build checks the library. Tests and demos have separate targets:

```sh
lake build LeanOrigamiTests LeanOrigamiDemos
bash scripts/validate.sh
```

The validation script checks all three targets, runs the arithmetic and root
experiments, exercises the pinned ProofWidgets insertion handler, and checks
the resulting standalone Lean proof. It requires no npm installation. Checkpoints are validated locally;
the GitHub Actions workflow is manual-only and does not run on pushes.

To run only the arithmetic experiment after building its imports:

```sh
lake exe phase0-runtime
```

`Feasibility.lean` contains kernel-checked semantic results and axiom reports;
`Runtime.lean` contains executable assertions and timing output. Runtime
assertions are tests, not proof certificates.

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
