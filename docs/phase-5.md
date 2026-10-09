# Phase 5 audit

Status: complete (2026-10-09). The original completion claim was withdrawn
because its text commands bypassed `Program`. This repair uses
one saved program throughout assembly, executable feedback, and certification.

## Implementation and mathematical checks

- `RecipeBuilder` supplies ordinary named Lean `do` notation for all seven
  folds, intersections, and reusable arithmetic/root recipes. The old
  `Text/Certified.lean` and `Text/Syntax.lean` implementations were removed.
- The checker stores plain exact objects. Its geometric rules, reference-kind
  checks, finite-choice conditions, and final equality check are unchanged.
  Soundness is proved separately by induction over the same execution.
- Four certificate lemmas expose actual checker steps, execution composition,
  and submission. `origami_check` uses them to prove `Program.accepts = true`,
  then `accepts_sound` establishes constructibility. Every instruction is
  checked, including unused instructions. No separate construction history
  replaces acceptance of the saved record.
- Structural normalization leaves scalar values and geometry untouched. This
  avoids both whole-program Hex reduction and repeated expansion of nested
  recipe states. Geometry is proved symbolically; generated terms still pass
  through Lean's kernel. Custom certificates may supply root equations and
  branch facts.
- `RootPrograms.lean` uses the existing builder for efficient reference
  assignment. Its public saved-program API remains the same. The square-root,
  cube-doubling, nested-root, and full trisection programs have generic
  acceptance certificates. The trisection certificate covers both coordinates.
- `TextScalar.lean` connects a concrete executable Hex square root, its real
  interpretation, the saved scalar program, and the final constructibility
  theorem. Native replay tests the same value separately.
- Artifacts preserve exact source and selected expressions, including the
  acceptance proofs. Loading JSON is not certification; a fresh Lean process
  checks the exported source and its theorem's transitive axiom dependencies.

## Validation

The generic root certificates and real conclusions have passed LSP diagnostics
and targeted builds. Their transitive axiom dependencies are only `propext`,
`Classical.choice`, and `Quot.sound`. The all-seven-axiom example passes both
symbolic certification and kernel evaluation of the rational checker.

Rejection tests cover missing/forward references, wrong object kinds, wrong
folds and intersections, underconstrained folds, unused invalid steps, wrong
final targets, negative square-root choices, extraneous quadratic roots, and
zero divisors/leading coefficients. They check rejection locations without
leaving failed declarations in the environment. Candidate-list reordering
preserves the exact selected construction. A separate regression checks that
certifying a goal leaves unrelated goals alone.

The concrete Hex acceptance and submission theorems have also passed LSP
checks and the transitive axiom audit with only the same standard foundations.
`LEAN_NUM_THREADS=1 bash scripts/validate.sh` completed successfully locally.
It checked all library/test/demo targets, native arithmetic and root replay
(including the certified Hex candidate), widget smoke and fresh replay, artifact
round trips, and fresh text-proof replay. The exported source rechecked all
four root certificates and their named conclusions with only the standard
Mathlib axioms. No project warnings, proof holes, project axioms, or native
decision proofs were introduced. The pinned dependencies retain their existing
warnings. The final diff and maintained-source build paths were reviewed; no
dependency versions changed and no GitHub Actions validation was requested.

## Size and limitations

Relative to the original Phase 5 checkpoint, production Lean library source
shrinks from 4,811 to 4,729 lines (82 fewer). Including demos and tests, Lean
source grows from 6,750 to 6,778 lines (28 more). This replaces the previous
interface rather than retaining it alongside the shared-program path.

Proof generation is not construction search and does not automatically extract
a compact certificate from every opaque Hex result. Exact algebraic identities
and branch facts can require explicit proofs. Large examples still take time
to elaborate and kernel-check. Source artifacts preserve the source prefix and
rely on imports from the pinned project; they are not self-contained bundles
of all dependencies. The graphical construction editor remains Phase 6 work.
