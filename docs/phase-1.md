# Phase 1 geometry audit

Status: complete (2026-10-07). The Phase 1 acceptance criteria passed the
specification, code, proof-dependency, and local validation audits below.

## Boundaries

Exact scalars are the real subfield of Hex's algebraic numbers. Arithmetic
and comparisons remain executable; interpretation into Mathlib's reals is
used only for proofs. A value in this field is not evidence of construction.

Coordinate geometry is shared between this field and the reals. Lines
have a nonzero normal and normalized coefficients. Finite-choice legality is
measured using real creases, not just a computed list of algebraic creases.

## Exceptional-case review

The following is the mathematical case review guiding the definitions.
Full executable case guards and completeness proofs belong to Phases 2–3;
this table is not a claim that those later proofs are already implemented.

| Rule | Cases the implementation must distinguish |
| --- | --- |
| 1 | Distinct points determine one crease. Identical points allow every line through that point, so the selection is underconstrained. |
| 2 | Distinct points determine their perpendicular bisector. Identical points allow every line through the point. |
| 3 | Distinct parallel lines have one midline; intersecting lines have two angle bisectors. An identical input line is preserved by itself and by every perpendicular crease, giving infinitely many choices. |
| 4 | A valid line and a point always determine one perpendicular crease through the point, including when the point is on the line. |
| 5 | Creases pass through the fixed point. The moved point's images lie on a circle about that fixed point and on the target line. Zero, tangent, and two-intersection cases matter. If both input points coincide on the target, every crease through that point works; if they coincide off the target, none works. A point already on the target is not by itself grounds for rejection. |
| 6 | The two point-to-line constraints may be independent or redundant. Repeating the same point and target leaves infinitely many creases. Two distinct points already on the same target line also allow infinitely many creases perpendicular to that target. These examples do not exhaust the degenerate cases: full classification and degree-drop analysis remain Phase 3 obligations. |
| 7 | The second line fixes the crease direction. If the two input lines are parallel, a point on the target gives infinitely many choices and a point off the target gives none. Nonparallel input lines determine a unique crease. |

Empty sets are finite but supply no selected fold. Infinite sets supply no
legal selection, even when a particular crease satisfies the fold relation.
Coincident lines have infinitely many intersection points; parallel distinct
lines have none. Neither gives a unique-intersection step.

## Implemented interfaces

| File | Responsibility |
| --- | --- |
| `LeanOrigami/Scalar.lean` | Real subfield of Hex, executable field/order instances, injective real field homomorphism. |
| `LeanOrigami/Geometry/Basic.lean` | Points, canonical valid lines, checked coefficients, line equality, incidence, lines through points, unique intersections, field transport. |
| `LeanOrigami/Geometry/Reflection.lean` | Reflection, perpendicularity, fixed points, involution, midpoint incidence, squared-distance preservation, field transport. |
| `LeanOrigami/Geometry/Euclidean.lean` | Affine-line interpretation in Mathlib's Euclidean plane; equality with Mathlib reflection; orthogonality of full direction subspaces. |
| `LeanOrigami/Folds.lean` | The seven relations, whole-line reflection meaning, real solution sets, finite-choice legality, representative infinite cases, exact unique-intersection condition. |
| `LeanOrigami/Geometry/Exact.lean` | Exact objects interpreted in real geometry; real legality for exact inputs. |

The real plane is Mathlib's `EuclideanSpace ℝ (Fin 2)`, not a product with
an accidentally different norm. Line normalization is characterized by
incidence and proved invariant under nonzero scaling. Normal validity is
part of the line type; the public coefficient constructor rejects invalid
normals. Every reflection denominator has a positivity proof.

`FoldInput.Satisfies` is a relation, not a solver. For rule 3, its equivalence
to equality of the reflected source set and target set is proved.
`FoldInput.LegalExact` interprets inputs in the real plane and requires
finiteness over all real crease solutions. It is not a claim about input
provenance, and no executable finite-choice checker is implemented yet.

## Validation and checkpoint audit

The library was checked with Lean LSP diagnostics and module builds;
no project errors or warnings remain in those checks. Separate real-plane
examples passed, including all seven rules,
line normalization, reflection, intersections, and rejection of coincident
or parallel intersections. A rule-3 regression rejects aligning just one
point when the whole lines do not match. A rule-7 example checks that the
second input line actually constrains perpendicularity.

The printed axiom dependencies of the ten main geometry/specification
results are only `propext`, `Classical.choice`, and `Quot.sound`.
The exact scalar examples also passed, including rational arithmetic,
nonzero inversion, division and rational-cast transport, the positive square
root of two, an irrational line coefficient, and exact reflection at an
irrational coordinate. Their axiom reports contain only the same three
standard foundations.

`LEAN_NUM_THREADS=1 bash scripts/validate.sh` completed successfully. It
checked the library, proof tests, and demos; ran the native and interpreter
arithmetic/root suites; executed the public scalar arithmetic, order, line
normalization, reflection, and invalid-normal rejection checks; and checked
the widget insertion, stale-edit rejection, and standalone proof replay.
Upstream dependency warnings and Node's experimental-VM warning remain;
no project errors or warnings were introduced. No GitHub Actions run was used.

The audit compared the implementation against all six Phase 1 steps.
Validity assumptions reside in the line type and intersection arguments;
reflection and perpendicularity are connected to Mathlib geometry; finite
choice is quantified over real creases. The old scalar probe was replaced
by the public interface, and tests remain separate from library modules.
Source scans found no proof holes or forbidden proof shortcuts. The diff
has no dependency, toolchain, build-configuration, or CI changes.

Compiled Hex imports remain expensive to load in fresh processes on this
8 GB machine: the exact-geometry module and combined test import each took
roughly four to five minutes, while generic geometry modules took seconds.
The native arithmetic/root checks took milliseconds. Keep LSP sessions warm,
use focused imports, and reserve the full script for checkpoints.

## Later-phase obligations

- Build construction histories and prove that their inputs and outputs are
  obtainable from permitted starting objects (Phase 2 onward).
- Derive executable admissibility guards and complete the exceptional-case
  classification with each solver. Prove soundness, completeness, and the
  seven finite-solution bounds (Phases 2–3).
- Prove the polynomial descriptions of the fold relations, including full
  real-plane meaning for whole-line alignment. No solver correctness is
  assumed by the current geometry or legality definitions.
- Implement the graphical construction interface and test it in the actual
  editor host in its planned phase. The Phase 0 widget remains a prototype.

These are existing plan boundaries, not waived Phase 1 requirements.
