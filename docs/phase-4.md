# Phase 4 audit — real roots as origami constructions

Status: complete, 2026-10-08. All planned acceptance criteria passed.

## Mathematical result

Constructible numbers are closed under every real root of a genuine quadratic
or cubic with constructible coefficients, in addition to Phase 3's field
operations. Nonnegative square roots and linear roots have named theorems.
These results compose, including using a constructed root as a coefficient.
They do not assert constructibility of arbitrary algebraic numbers.

The monic cubic `t³+a*t²+b*t+c` uses `(0,1)` onto `y=-1` and `(c-a,b)` onto
`x=-a-c`. `RootGeometry.satisfies_iff_exists` proves both directions of the
correspondence with creases `y=t*x-t²`. The first alignment excludes vertical
creases. Normalization handles `t=0` without division by the root. The targets
are perpendicular and the eliminant has a fixed nonzero coefficient, so the
request is finite for every coefficient tuple, even with coincident sources.

`Construction/Roots.lean` constructs each input from the coefficient histories.
Intersections at horizontal coordinates zero and one recover the crease slope
by subtraction. The unknown root is never an input with assumed provenance.
General cubics are normalized by a constructed nonzero leading coefficient.
Quadratics reuse their product with the variable; square roots choose the
nonnegative branch. A zero constant equation supplies no construction evidence.

## Executable integration

`RootRecipe` emits ordinary primitives, using the existing arithmetic recipes
to construct its inputs. `RecipeBuilder.use` expands nested recipes with the
same reference relocation as program append. `ArithmeticRecipe.pair` reuses
its existing coordinate helpers to combine two constructed coordinates.

Quadratic recipes reject the extra zero root unless it solves the original
quadratic. Square-root recipes check the exact equation and nonnegative sign.
Cubic recipes defer root validation to the fold checker. Division requires a
nonzero leading coefficient. All referenced inputs still pass ordinary replay.

## Demonstrations and tests

- Kernel-checked construction histories for exactly `√2` and `2^(1/3)`;
  the latter is proved to cube to two.
- A second square-root construction using the first root as its coefficient.
- Constructed unit-circle points at sixty and twenty degrees; the latter has
  a positive vertical coordinate and arccos angle one third of sixty degrees.
- The cubic branch above one half is unique. Polynomial, interval, and circle
  conditions identify the exact twenty-degree point, not just a polynomial root.
- Saved programs for square root, cube doubling, composed fourth root, and both
  coordinates of the trisection point.
- Kernel replay tests for three distinct roots, a repeated root, a nonmonic
  cubic, both quadratic branches, square root zero, and an incorrect cubic root.
- Rejection tests for negative radicands, negative square-root branches, and the
  quadratic embedding's artificial zero root. A coincident-source case remains
  a legal finite request.
- Native Hex integration checks exact equations, branches, full replay, target
  mismatches, and reuse of an irrational coefficient. These assertions are not
  used as Lean proof premises.

## Validation and limitations

Focused LSP checks and targeted Lake builds passed for the new mathematical
modules, recipes, rational replay tests, and theorem demonstrations. Transitive
`#print axioms` reports for closure and demonstration theorems contain only
`propext`, `Classical.choice`, and `Quot.sound`.

All commands on the local validation path passed:

- `lake build LeanOrigami LeanOrigamiTests LeanOrigamiDemos phase0-runtime`
  completed successfully (9,978 jobs, predominantly cached).
- The existing `phase0-runtime` and `Interpreter.lean` checks passed.
- `lake lean LeanOrigamiTests/RootInterpreter.lean` passed all new irrational
  replay and exact branch checks, both in the LSP and from the command line.
- The widget harness, JavaScript click/stale-edit checks, and standalone
  `WidgetReplay.lean` proof passed.
- Final diff/whitespace and source-hole checks passed. No new project warnings.

The first validation-script run stopped at an incorrect invocation of Lean's
`--run` option for the new test. The test now uses the same explicit `#eval`
entry point as the existing interpreter test. The corrected command and the
remaining widget commands were then run successfully; already-passing build
and interpreter checks were not repeated. This test is not imported by the
default library or test umbrella, so ordinary builds do not rerun it.
No toolchain, dependency, or CI changes.

The saved irrational programs are tested through native Hex execution; the
named mathematical conclusions have separate kernel-checked construction
proofs. Native test results are not kernel reduction certificates. General
proof-producing text commands and exported proof artifacts remain Phase 5;
the graphical interface remains Phase 6. This phase does not prove the full
classification of all origami-constructible field extensions or general angle
trisection, which are outside its stated acceptance criteria.
