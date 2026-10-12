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

## Solver-output certificate checkpoint (in progress)

The original repair's remaining automation gap is being closed before Phase 6.
`Scalar/Presentation.lean` packages a checked irreducible polynomial and a real
root isolation, and proves that rational coordinates in this field embed into
the existing executable `Scalar`. `Text/Exact.lean` recovers coordinates for
all saved objects in one field, checks exact reconstruction, and exports an
ordinary scalar program with an automatic acceptance proof.

`origami_coordinates` transports equations through that embedding and uses
kernel reduction only on the rational coordinates. A guard rejects incomplete
transport. It shares the existing `origami_check`, step certificates, final
reference checks, and `accepts_sound`; no geometric rule or construction record
has been replaced. The field generator is not an added seed or an assumption
of constructibility. Search and exactification stay outside proof reduction.

Tests live in `LeanOrigamiTests/ExactExport.lean`. They rediscover the selected
root creases, reverse candidate lists, export and round-trip artifacts, and
produce a fresh replay file. Cases cover all seven axioms, square and cube
roots, an iterated root with algebraic coefficients, three real cubic branches,
and independent roots requiring a common degree-six field. Replayed checks
include exact target equations, a changed target, an invalid unused fold,
and an invalid isolation witness. The validation script includes this path.

The two new library modules total 201 lines. Existing symbolic certificates
remain useful for generic theorems and identification with named Mathlib real
expressions; the new path handles actual executable solver values. Common-field
conversion can be costly for independent roots. It does not search for a
construction, and its native success is never accepted as proof.

Final validation and timing results will be recorded before this checkpoint
is marked complete.

### Performance investigation (2026-10-10)

The user's full validation log reached the final profiling summary without
errors. All nine exported constructions produced acceptance and constructibility
theorems with only `propext`, `Classical.choice`, and `Quot.sound`. The exponent
warning and two unused-tactic warnings still require cleanup; this is not yet
a completed checkpoint.

The original 301-second and 913-second instance-inference measurements were
contaminated by system sleep. The macOS power log records 303-second and
915-second sleep intervals during that replay (19:59–20:20 on October 9).
These elapsed-time measurements must not be interpreted as CPU costs.
Isolated LSP replays on October 10 completed the cube acceptance proof in
about 38 seconds and the independent-root acceptance proof in about 100
seconds, excluding import loading. Both retained the standard axiom set.
There is repeated subsecond instance work, but the previously suspected
minutes-long individual instance search did not reproduce.

The separate independent-root native export took 1,204 seconds in the original
run, before those sleep intervals. Temporary diagnostic drivers split
the same fallback into primitive-generator extensions, power-table creation,
coordinate recovery, and exact reconstruction. No production algorithm or
dependency version was changed.

Findings:

- The ordinary interpreter setup loads some native helpers but not the entire
  Hex number-field backend. Process sampling confirmed interpreter overhead.
  A targeted `lake build @HexNumberField/HexNumberField:shared` built the
  missing shared libraries and native dependency objects. A temporary setup
  loaded these plugins in dependency order; merely loading the final library
  without its dependencies is insufficient. No full repository rebuild ran.
- With the compiled backend loaded, fold rediscovery took about 2 seconds
  and native acceptance about 1.3 seconds for the 184-step mixed-root program.
  There were 18 distinct saved scalar values.
- `AlgebraicPoly.Common.primitive?` extends a generator with each nonzero
  value. `extendShift?` tests its whole conservative shift bound, including
  values already in the field. The 16 extensions took 291.562 seconds in the
  compiled experiment; three degree-six/degree-two attempts alone took
  71.106, 70.010, and 95.873 seconds without increasing the field degree.
- `QAdjoin.fastPair?` on just the cube and square roots produced a generator
  and checked coordinates for that pair in 68 ms. This isolates the redundant
  multi-input search cost; it does not establish a general export fix.
- Coordinate conversion has a separate bottleneck. The compiled fallback
  spent at least 290 seconds building its power table before being stopped.
  The two-root shortcut spent at least 295 seconds in conversion and had not
  completed even its power table. Sampled stacks pinpointed
  `Common.powers? → AlgebraicRoot.exactFactor? → ZPoly.isolateComplexRoots?`
  in the fallback. The shortcut was also inside canonical exactification
  while building powers. Thus loading native code and choosing fewer inputs
  do not, by themselves, resolve export performance.

These are diagnostic measurements, not a calibrated benchmark: arithmetic
probes overlapped, and incomplete stages are lower bounds, not successful
completions. The first interpreter driver's per-stage zero readings were
discarded because pure arguments could evaluate before entering its timer.
The compiled probes used delayed callbacks and reported nonzero timings.
The user's original whole-export timer is independent of that probe error.

Next work should address both conservative generator search and the repeated
canonicalization/root isolation used to recover coordinates. Prefer retaining
or recovering algebraic coordinate relations without constructing canonical
algebraic numbers for every intermediate power/product. Keep exact identity
checks and kernel certification intact. Do not redesign the proof-side field
instances on the basis of the sleep-contaminated profile.

All temporary processes were stopped and probe sources moved out of the
repository. Local raw evidence and drivers are retained under
`/private/tmp/origami-performance-investigation`. The investigation does not
mark the certificate checkpoint complete.

### Project-side performance repair (2026-10-12)

The approved repair leaves Hex sources and dependency pins unchanged. A small
precompiled `LeanOrigamiNative` library imports the executable Hex backend.
Lake's generated setup now includes the number-field shared library and all its
native dependencies, without requiring a handwritten plugin list.

`Text/Recording.lean` records arithmetic while reusing existing candidate and
intersection formulas. A local instrumented field has definitionally unchanged
scalar operations; runtime hooks additionally collect an arithmetic DAG. The
log belongs to one recording, with no global mutable state. This is untrusted
preparation: missing events fail explicitly, reconstructed coordinates must
match the selected scalars exactly, and exported proofs use the ordinary field.
The hooks do not occur in the proof certificates. The module passes complete
LSP diagnostics and has been integrated into the exporter.

Field preparation groups roots only when a construction step needs
them together. Coordinate recovery is limited to root parameters. Intermediate
coordinates are obtained by evaluating the saved arithmetic in reduced
polynomial coordinates. This replaces the previous recovery of every saved
coordinate from one global primitive element. The independent square/cube-root
case and its connected variant passed the focused end-to-end check.

Audit and validation:

- Production modules compiled, with clean LSP diagnostics during development.
- The 184-step independent square/cube-root construction retained separate
  degree-two and degree-three fields. The 185-step variant joining the two
  constructions used a degree-six field. Both exported proofs passed in a
  fresh Lean process; accepted/submitted theorems depend only on `propext`,
  `Classical.choice`, and `Quot.sound`.
- Focused executable probes covered quadratic axiom-5 recording and quadratic
  and cubic axiom-6 recording. The expanded separate test module adds axiom 3,
  all seven rules, nested roots, branch identity, and rejection cases.
- The full validation attempt rebuilt the library and existing test modules,
  then stopped at a reserved-word syntax error in the new test harness. The
  identifier has been corrected; the complete test file now passes LSP
  diagnostics with no errors or warnings. The expanded 12-case executable export and
  combined kernel replay have **not** been run to completion.
- At the user's request, that broader run and final comparative timings are
  deferred. The focused mixed-root proof checks and removal of the measured
  all-coordinate recovery bottleneck are the evidence for proceeding. No
  numerical speedup is claimed from sleep-contaminated wall-clock timings.
- Geometry definitions and checker statements are unchanged. No proof holes,
  unchecked proof primitives, Hex source edits, or dependency updates were
  introduced. The recording hooks are untrusted preparation only.
- The implementation uses 522 lines across Presentation, Recording,
  Coordinates, and Exact, plus a small native-loading bridge. The exporter
  replaces the old recovery path and reuses the existing geometry formulas.

Cold import loading remains slow. Interacting high-degree roots can still
require expensive field preparation. Matching the exported scalar to an
arbitrary named real-valued goal remains a Phase 6 responsibility.
