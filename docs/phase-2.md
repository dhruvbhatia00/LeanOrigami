# Phase 2 construction audit

Status: complete (2026-10-08). All Phase 2 acceptance criteria passed the
mathematical, code, proof-dependency, and local execution audits.

## What this phase adds

A saved program starts with exactly `(0,0)` and `(1,0)`. Each instruction
refers to earlier objects and appends one selected exact result. Accepted
objects carry proofs that they were obtained by the independent mathematical
construction rules. Submission also checks the requested coordinate value.

The program data already covers all seven fold requests. Rules 1, 2, and 4
and unique intersections execute now; rules 3, 5, 6, and 7 return explicit
unsupported-operation errors until Phase 3.

## Code map and data flow

| Module | Responsibility |
| --- | --- |
| `Construction/History.lean` | Point/line objects and mathematical constructibility from the two seeds, legal folds, and unique intersections. All seven rules are already included in this meaning. |
| `Construction/Program.lean` | Point and line references, all seven fold requests, instructions with exact selected outputs, coordinate selection, and errors. |
| `Solvers/Basic.lean` | Bisector and perpendicular-through-point formulas; reflection correctness, uniqueness, and real solution-set/admissibility proofs. Rule 1 reuses Phase 1 results. |
| `Solvers/Certified.lean` | Executable candidate computation with proofs of real finite-choice legality; exact intersection computation with uniqueness evidence. |
| `Construction/Checker.lean` | Reference resolution, selected-output checks, append-only certified state, program execution, final-target checks, and soundness theorems. |
| `LeanOrigamiDemos/Subdivision.lean` | A readable saved construction and kernel-checked proofs of the three subdivision numbers. |
| `LeanOrigamiTests/Construction.lean` | Exact output-list replay, construction histories, rejected inputs/outputs, primitive boundary cases, and axiom reports. |
| `LeanOrigamiTests/Interpreter.lean` | Execution of the same subdivision recipe using Hex, alongside the earlier execution tests. |

All library paths above are relative to `LeanOrigami/`. The public entry
point imports the checker; the test and demo roots import their new modules.

The execution path is:

1. Resolve each typed reference against the actual preceding object list.
2. Retrieve the input's construction evidence along with its exact value.
3. Compute the requested primitive candidate and its geometric legality proof.
4. Compare the saved selected output with that candidate using exact equality.
5. Append the output with a construction history built from those inputs and
   that legality proof.
6. Resolve the selected final point and check equality of its chosen coordinate
   to the target.

Proof fields are erased during execution. They are checked by Lean and do not
make runtime success a trusted axiom. `Program.run` returns ordinary objects;
`Program.run_sound` proves every returned object constructible.
`Program.accepts_sound` connects a proved acceptance result to constructibility
of the exact requested real number.

## Mathematical and representation audit

- `Constructible` is defined by geometric rules, not by checker acceptance.
  Every fold constructor requires histories for all its inputs and legality
  over all real creases. Every intersection requires a unique common point.
- Initial state supplies only the two permitted points. There is no instruction
  that imports arbitrary coordinates as already constructed objects.
- References use one zero-based append-only object list. The point/line role
  in a reference is checked against the actual stored object. Missing and
  forward references both fail as unavailable indices.
- Output coordinates are claims to check. Canonical line equality compares
  coefficients; supplying a valid but incorrect line does not bypass the rule.
- Rule 2's distinctness guard is equivalent to real finite-choice admissibility.
  The bisector is proved to reflect the points and to be the only real solution.
- Rule 4 always has exactly one solution, including when its point lies on
  the input line. Horizontal, vertical, and oblique cases are supported.
- Parallel distinct and coincident lines yield separate intersection errors.
  Repeated points yield an underconstrained-fold error for rules 1 and 2.
- The checker works over an ordered field with a field embedding into the
  reals. Hex's `Scalar` with `Scalar.realHom` is the executable algebraic
  instance. The generic coordinate formulas are reused across instances.
  Executable functions take no real embedding argument: histories quantify
  over embeddings inside proof fields, and soundness theorems specialize
  those proofs to `Scalar.realHom`. This keeps noncomputable real
  interpretation out of execution.
- Exhaustive solver enumeration is unnecessary for the three unique-solution
  folds: their completeness theorems establish the one available result.
  Phase 3 will extend candidate selection to multiple branches; saved output
  identity and the construction semantics already accommodate that extension.
- Resource exhaustion is reported by the Lean/execution host. It is never
  returned as evidence of impossible geometry or accepted as a certificate.

## Examples and certification

The subdivision program constructs the axes at indices 2 and 3, then the
points `(1/2,0)`, `(1/4,0)`, and `(3/4,0)` at indices 5, 7, and 9. A test checks
the complete expected object list and applies the general soundness theorem
to prove construction histories for its outputs.

The text interface is ordinary Lean program data plus `Program.accepts_sound`;
no custom parser or GUI state is needed. Lean checks malformed data syntax
and types; the checker rejects semantic reference and geometry errors.

The concrete proof examples instantiate the recipe over exact rationals and
use `decide +kernel`. This is kernel reduction, not `native_decide`. It keeps
these rational certificates small without evaluating Hex internals. The same
recipe is instantiated over `Scalar` for separate execution checks. General
checker soundness applies to both instances. These examples certify concrete rational programs. General symbolic
construction parameters remain the Phase 9 stretch goal; later algebraic
examples will need appropriately compact certificates.

Rejection proofs cover wrong input kinds, missing and forward references,
repeated points, forged fold and intersection outputs, coincident and
parallel lines, all four unsupported fold kinds, and a wrong final target.
Primitive examples also exercise horizontal and oblique bisectors and a
perpendicular through a point already on an oblique line.

## Validation and remaining work

Lean LSP diagnostics passed for the new library modules, subdivision demo,
and construction proof tests. The ten printed axiom reports for primitive
correctness/completeness, checker soundness, output construction histories,
and the three end-to-end number theorems contain only `propext`,
`Classical.choice`, and `Quot.sound`.

Full validation command:

```sh
LEAN_NUM_THREADS=1 bash scripts/validate.sh
```

The command completed successfully after the runtime-interpretation fix.
It built the library and every maintained test/demo target, ran the native
and interpreter arithmetic/root suites, and executed the subdivision program
with Hex. All three exact coordinate targets were accepted; a wrong target
and a forged crease were rejected. Widget insertion, stale-edit rejection,
and the independently checked replay proof also passed.

The interpreter test caught an initial noncomputable real embedding passed
as a runtime argument. The final implementation keeps embeddings entirely
inside proof fields; the same execution test now guards this boundary.
All affected proof examples and axiom reports passed again after the fix.

Final source and diff audits found no proof holes, unproved project axioms,
forbidden proof shortcuts, or unrelated edits. No dependency revisions,
build configuration, validation-script behavior, or CI behavior changed.
The earlier approved Phase 2 expansion and future-work ideas are preserved
in the plan. No GitHub Actions run was used. Upstream dependency warnings
and Node's experimental-VM warning remain; no project warnings remain.

The generic checker, demo, and construction test module builds took tens of
seconds. Combined entry points importing Hex still took several minutes per
fresh process. Continue using focused modules during development and the
full validation script at checkpoints.

Remaining planned work includes the other four primitive solvers and their
multiple branches, arithmetic macros, quadratic/cubic constructions, richer
text interaction, and the origami GUI. These remain later phases; Phase 2
does not claim support for those operations.
