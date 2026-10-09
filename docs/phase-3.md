# Phase 3 audit — exact fold discovery and arithmetic

Phase 3 is complete. All four checkpoints in `PLAN.md` passed, including full
local validation and the transitive proof-dependency audit.

## Delivered interfaces

- `Scalar.folds` finds every distinct exact crease for a specified request.
  It returns `none` for infinitely many choices, `some []` for no solution,
  and `some choices` for a finite list. It does not search for a sequence of
  operations or choose a branch for the user.
- `Solver.fold input selected` checks a saved crease without repeating root
  discovery. All seven rules are supported. `fold_succeeds_iff` characterizes
  success by the shared finite-choice guard and the original fold relation.
- Programs retain exact selected outputs and references to earlier objects.
  The checker resolves those references with their construction histories;
  it does not infer provenance from an algebraic coordinate's existence.
- `constructible_point_iff` relates constructed points to their two constructed
  coordinates. Coordinate placement and arithmetic theorems cover signed and
  zero operands; division requires a nonzero divisor.
- Recipes expand into ordinary primitive instructions. Argument references
  are substituted and intermediate references shifted. `Recipe.relocate_lt`
  proves preservation of earlier-reference bounds for existing arguments.
  Expansions use the same checker and soundness theorem as handwritten programs.

The [README module guide](../README.md#phase-3-modules) identifies the files
for these interfaces. `AllFolds.lean` and `Arithmetic.lean` are the main demos.

## Mathematical cases reviewed

| Rule | Complete finite-choice classification |
| --- | --- |
| 1 | Distinct points: one crease. Coincident points: infinitely many. |
| 2 | Distinct points: one crease. Coincident points: infinitely many. |
| 3 | Intersecting lines: exactly two. Distinct parallel lines: exactly one. Coincident lines: infinitely many. |
| 4 | Always one crease. |
| 5 | Distinct source/fixed points: at most two, including tangency and no solution. Coincident points: infinitely many if on the target, otherwise none. |
| 6 | At most three unless the eliminant is identically zero or both sources already lie on parallel targets. Each exceptional case has a proved infinite family. |
| 7 | A nonzero alignment coefficient gives one crease. A zero coefficient gives infinitely many if the source is on its target, otherwise none. |

Admissibility and completeness quantify over **all real creases**, not a
computed list or only algebraic coordinates. The discovery proof shows that
every crease of a finite request has an algebraic representation and then
uses Hex's complete root interface. Duplicate normalized lines are removed.

The rule-6 analysis handles both line charts, degree drops, repeated roots,
and zero denominators. A horizontal crease forces the cubic leading
coefficient to vanish. An eliminant root alone is insufficient: candidate
filtering checks the original two reflection conditions. Tests include an
extraneous root where both alignment dot products vanish.

Geometry and all seven original fold relations retain their Phase 1 meanings.
Whole-line reflection in rule 3 is reduced to two incidence checks by a proved
equivalence. Embedding transport does not assume that an arbitrary field
embedding preserves a chosen order. Approximation is absent from certification.

## Validation and trust

Individual modules passed Lean LSP checks and targeted Lake builds. Separate
kernel-checked rational programs cover both off-axis branches, all seven
primitive rules, each of three rule-6 selections, and composed arithmetic.
Boundary tests cover zero operands, negative placement, forged coordinates,
wrong-kind references, and missing references.

Transitive axiom reports for root completeness, crease representability,
complete discovery, fold classifications, arithmetic, recipe relocation, and
end-to-end examples contain only the ordinary Mathlib foundations:
`propext`, `Classical.choice`, and `Quot.sound` (some use fewer). The source
scan found no proof holes, unproved project axioms, or `native_decide`.
No toolchain, dependency, or CI configuration changes were made.

Full validation passed with exit status 0:

```sh
LEAN_NUM_THREADS=1 bash scripts/validate.sh
```

The build completed successfully (9,972 jobs, mostly cached). Validation
covered the library, all maintained tests and demos, the older runtime
suite, native Hex discovery/replay, and widget insertion plus standalone
proof replay. The expanded native suite passed, including genuine cubic equations
with one, two, and three distinct real crease choices, repeated roots,
irrational coefficients, and composed arithmetic recipes. No project warnings or errors remained;
replayed dependency warnings were not suppressed. Native test results
are not used as premises in proofs.

## Performance and scope

Fresh Hex-heavy Lean processes still take several minutes on this 8 GB machine
with compiled dependencies available: the discovery-library build took about
300 seconds and its separate test build about 284 seconds. Generic geometry
and arithmetic modules check much faster. Keep one proof file active and
avoid simultaneous Hex-heavy checks. One duplicate audit worker was stopped;
its failed tool result was not counted as validation. The later dedicated
`#print axioms` audit passed.

General arithmetic correctness is proved geometrically; concrete expanded
recipes are checked through replay. Phase 4 will construct roots of arbitrary
quadratics and cubics from construction evidence for their coefficients.
A proof-producing origami GUI remains a later phase.
