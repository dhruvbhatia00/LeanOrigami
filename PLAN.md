# LeanOrigami restart plan

## 1. Purpose, scope, and completion

Build a Lean library and interactive environment in which a user proves that
a number is origami-constructible by supplying a sequence of folds and
intersections. The user chooses operations, their inputs, and solution
branches. Lean computes the available outcomes and certifies the resulting
construction and its final value.

This is a fresh implementation. Consult the archived project for useful
arguments and counterexamples, but do not preserve its APIs or architecture
by default. Follow [AGENTS.md](AGENTS.md) throughout implementation.

### Main release

- Faithful specifications and exact solvers for all seven Huzita–Hatori
  single-crease operations, including their exceptional cases.
- Explicit, replayable construction programs, a text interface, and a
  ProofWidgets interface producing kernel-checkable Lean proofs.
- Exact real algebraic coordinates, with approximate rendering.
- Reusable constructions with concrete inputs.
- Proofs that constructible real numbers form a subfield, are closed under
  nonnegative square roots, and contain every real root of a cubic with
  constructible coefficients.
- Separate tests and readable demonstrations, including square roots,
  cube doubling, and a concrete angle trisection.

### Later milestones

1. Characterize constructible real numbers using finite towers of real
   quadratic and cubic extensions.
2. Stretch goal: symbolic construction parameters, explicit hypotheses,
   and reusable constructions with generated proof obligations.

The paper is a viewport onto the ideal plane. Physical sheet boundaries,
moving regions, layer simulation, and simultaneous multi-crease operations
are outside scope. Automatic search for a construction sequence is also
outside the main release: a fold solver answers a user-selected operation.

The one-week objective motivates early end-to-end milestones, not weaker
definitions or incomplete proofs. Phase 0 establishes feasibility and
performance evidence before making a delivery forecast. Main-release
completion requires all its acceptance criteria, regardless of elapsed time.

## 2. Architecture and mathematical contracts

### Geometry and scalars

Use exact real algebraic numbers for executable coordinates and coefficients.
Represent points as coordinate pairs and lines by `a*x + b*y = c`, with
`a` and `b` not both zero. Do not represent all lines by slopes.

Normalize line coefficients by their first nonzero normal coefficient:
`(1, b/a, c/a)` when `a ≠ 0`, otherwise `(0, 1, c/b)`. Prove normalization
preserves incidence and identifies exactly the same geometric lines. This
avoids both coefficient-scaling ambiguity and normalization by square roots.

Use Hex's verified real interface if the pinned version supplies the needed
operations. Otherwise define a small real subtype/interface over its complex
algebraic representation. Phase 0 must settle and document this choice. Do
not implement a second algebraic-number engine. Provide a verified embedding
into `ℝ` preserving arithmetic, equality, and order.

Share basic coordinate formulas over suitable ordered fields where useful;
avoid speculative abstractions. Interpret the geometry in `ℝ²`, connecting
incidence, perpendicularity, and reflection to appropriate Mathlib notions.
The real semantic layer must support theorems with variables and hypotheses
without executing Hex.

All real algebraic numbers are available as a representation, but only a
valid construction history establishes origami constructibility.

### Fold relations and admissibility

Keep the geometric meanings of the seven operations as propositions.
Operations, construction histories, and branch selections are data.

An admissible primitive fold selects from a finite set of geometrically
distinct real crease solutions determined by its inputs. Finiteness is over
the real geometric solution set, not merely over a computed candidate list
or the algebraic values a backend happens to find. Intersections require a
unique point, witnessed computationally by a nonzero determinant.

Derive explicit, decidable admissibility conditions for each operation and
prove their connection to this semantic rule. Underconstrained operations
must not introduce arbitrary coordinates. Do not impose convenient extra
restrictions that silently exclude legitimate finite cases.

Prove the finite-solution bounds for operations 1–7 respectively:
`1, 1, 2, 1, 2, 3, 1`. Deduplicate repeated roots and scaled representations.
Prove that the guards cover the intended finite cases; document any mismatch
as an unresolved specification issue, not as a completed implementation.

### Algebraic bridges and solvers

For every operation, prove that its geometric relation is equivalent to an
explicit algebraic system under the required validity assumptions. Clearing
denominators must be justified. Use Mathlib polynomials for the mathematical
statements and proved translations to Hex's executable representations.

Separate three proof obligations:

1. Geometry is equivalent to the algebraic constraints.
2. Every reconstructed solver candidate satisfies those constraints.
3. Every admissible geometric solution appears among the candidates.

Polynomial elimination alone may introduce extraneous roots or omit cases.
Account explicitly for vertical creases, zero leading coefficients, repeated
roots, and divisions by expressions that can vanish. Check reconstructed
candidates against the original constraints.

The solver computes all available creases for a supplied operation and its
inputs; the user chooses one. Distinguish no solutions, infinitely many
solutions, invalid inputs, and computational failure or resource exhaustion.
A computational failure is never evidence of geometric impossibility.

### Construction programs and certification

Use a finite sequence of instructions with references to earlier objects.
Start with `(0,0)` and `(1,0)`; construct axes and all additional objects.
Track the requested operation, its inputs, and an exact selected output or
root certificate. Do not persist branch identity solely as an index into a
solver's current ordering or as a floating approximation.

The public capabilities are:

- Describe a primitive operation and its required object references.
- Enumerate its exact outcomes and select an outcome.
- Check and interpret a construction program.
- Select a final point coordinate and prove equality to a target value.
- Define and invoke a reusable construction with explicit inputs and outputs.

The checker validates references, input provenance, admissibility, and every
selected output. Prove that accepted programs denote mathematically
constructible objects. Checking a selected branch need not rerun exhaustive
enumeration when its certificate and the admissibility lemmas suffice.

Certification includes both legal construction and target identification.
Root membership does not distinguish conjugate roots: identifying `√2`, for
example, requires the positive branch. Use verified exact equality or a
root characterization with uniqueness. Minimal-polynomial divisibility is
useful over the correct coefficient field, not a universal substitute for
exact equality and branch identification.

Reusable constructions initially take concrete objects. Expand their bodies
into primitive instructions for certification, so a macro adds no trusted
construction rule. Keep input/output roles explicit to support later
symbolic generalization.

### Text interface, widget, and rendering

Both interfaces create the same construction programs and use the same
backend. Begin with goal-directed submission: open a constructibility goal,
build a construction, select a coordinate, and submit a proof of the goal.
A target mismatch leaves the goal open with an explanation.

Submission must insert a persistent Lean expression or construction script
that checks after reopening the file without widget state. Source insertion
must detect stale editor state rather than overwrite unrelated edits.

Render exact points and lines through controllable numerical approximations.
Convert approximations to screen coordinates, clipping lines to the viewport
without requiring slope conversion. Refine precision when zoom or nearby
branches demand it. Every rendered object retains an exact backend identity;
screen coordinates are never imported as new construction data.

Provide input selection, operation selection, branch previews, undo,
pan/zoom, construction inspection, and submission. Keep the UI responsive
during computation and reject stale asynchronous results after undo or edits.
Free exploration with theorem export is an optional follow-up after
goal-directed submission, not a main-release requirement.

## 3. Mathlib and Hex responsibilities

| Foundation | Responsibility |
| --- | --- |
| Ordered fields and homomorphisms | Coordinate formulas, normalization, denominator conditions, semantic transport. |
| Mathlib polynomials | Evaluation, degree, root finiteness, algebraic identities, coefficient maps. |
| Real-number theory | Positivity, square roots, odd-degree real-root existence where needed. |
| Euclidean geometry | Independent geometric interpretation of coordinate definitions. |
| Subfields, intermediate fields, minimal polynomials, finite dimension | Closure results and the later extension-tower characterization. |
| Hex and its Mathlib correspondence | Exact arithmetic, realness/order, algebraic-coefficient roots, approximation, and certification of executable values. |

Keep these three claims distinct: a real cubic has a real root; every real
root of a cubic with constructible coefficients is constructible; and the
software computes and certifies corresponding folds. Arbitrary real
coefficients require a relative construction problem with supplied inputs.

General closure theorems should work with mathematical variables. Concrete
program execution uses Hex. Theorems, checker results, and exported proofs
must remain kernel-checkable under the ordinary Mathlib foundations.

## 4. Implementation phases

Each phase includes separate tests/examples and the checkpoint audit in
AGENTS.md. A phase is complete only when its stated acceptance evidence is
available. Work in dependency order, batching development within one file
and rebuilding imports at file transitions as prescribed there.

### Phase 0 — Preserve the old project and establish feasibility

Archive the complete current state, including user changes, in a pushed
commit and archive branch or tag; verify its hash against the live remote.
Preserve AGENTS.md and this plan through the subsequent reset. Do not erase
the prior implementation before preservation is verified.

Create a fresh project with compatible pinned Lean, Mathlib, Hex, and
ProofWidgets versions. Establish separate library, test, and demo targets
and explicit full-validation commands. CI must cover targets excluded from
the fast default build.

Run small isolated experiments for exact real arithmetic/order, algebraic
coefficients in root solving, branch identification, the embedding into
`ℝ`, and dyadic approximation. Measure executable computation and kernel
checking separately, including a short sequence with irrational values.
Use the results to select direct evaluation or compact certificates without
weakening the trust requirement. Prototype widget interaction and insertion
of a trivial persistent Lean proof.

**Acceptance:** recorded dependency pins, working experiments, representative
timings, chosen real-number API and certification path, explicit unresolved
dependency limitations, and a verified remote archive. No unsupported
assumption about a dependency may be hidden in the next phase.

### Phase 1 — Geometry and the construction specification

**Goal:** provide exact geometric objects and precise statements of what
each fold means. By the end, we can prove that a supplied crease performs
a specified fold. Construction programs, automatic fold finding, and the
GUI remain in later phases.

Work through the following steps in dependency order. Keep scalar support,
basic geometry, real interpretation, and fold rules in modules with clear
responsibilities. Settle module boundaries as the interfaces become clear;
do not put the entire phase in one file or create a wrapper for every lemma.
Keep examples in separate test files and add them to the validation path.

#### 1. Finish the real-number interface

- Build on the Phase 0 choice: Hex algebraic numbers together with evidence
  that their exact `isReal` test succeeds. Reuse Hex's arithmetic engine.
- Provide zero, one, rational values, addition, subtraction, multiplication,
  division, equality, and order, with the field and order laws needed by
  geometry. Prove that the operations preserve reality. Follow Lean's field
  convention for division, while requiring nonzero denominators wherever a
  geometric formula depends on division being invertible.
- Provide an injective interpretation into Mathlib's `ℝ`, preserving
  arithmetic, equality, and order. Keep this mathematical interpretation
  separate from executable arithmetic and display approximations.
- Refactor the Phase 0 subtype probe into the library interface where useful;
  update its tests rather than keep a competing scalar implementation.

**Checks:** rational arithmetic, an irrational value, comparison, and division
by a nonzero value. Include proofs about variables through the real
interpretation, not only calculations on fixed examples. Audit this interface
before making geometry depend on it.

#### 2. Define points and valid, normalized lines

- Represent points by two real algebraic coordinates. Provide their
  interpretation in `ℝ²` and prove that equality is preserved and reflected.
- Represent a line by `a*x + b*y = c`, with `a` and `b` not both zero.
  Make invalid lines unrepresentable or reject them at the public constructor.
  Vertical lines must work without a special slope representation.
- Normalize coefficients to `(1, b/a, c/a)` if `a ≠ 0`, and otherwise to
  `(0, 1, c/b)`. Prove the denominators used here are nonzero.
- Prove normalization preserves which points lie on the line, is unchanged
  by nonzero scaling, and gives the same representation exactly when the
  original coefficients describe the same geometric line. Include a
  uniqueness/idempotence result so repeated normalization changes nothing.

**Checks:** horizontal and vertical lines; `x + y = 1` versus
`2*x + 2*y = 2`; negative scaling; an irrational coefficient; rejection of
`a = b = 0`, for both zero and nonzero `c`.

#### 3. Implement basic geometry and prove its meaning

- Define incidence (a point lies on a line), perpendicularity, and the line
  through two distinct points. State the distinctness requirement explicitly.
- Define reflection across a valid line. Prove its denominator is nonzero,
  reflecting twice returns the original point, and the fixed points are
  exactly the points on the crease. Connect reflection and perpendicularity
  to the corresponding geometry in Mathlib over `ℝ²`, rather than merely
  assigning geometric names to coordinate formulas.
- Define intersection for two lines whose coefficient determinant is
  nonzero. Prove the result lies on both lines and is their unique common
  point. Distinguish parallel distinct lines from coincident lines; neither
  supplies a unique intersection.
- Share coordinate formulas over suitable ordered fields where this helps
  the real interpretation. Keep statements with variables usable without
  executing Hex, and avoid building an unnecessarily general geometry library.

**Checks:** reflection across `x = 1` sends `(0,0)` to `(2,0)`;
a point on the crease stays fixed; reflection twice returns the input;
horizontal/vertical and oblique intersections work. Parallel and coincident
lines cannot be used as unique-intersection steps.

#### 4. State all seven fold relations

Each relation is a proposition about its inputs and a proposed valid crease.
Use incidence and reflection to state the actual geometric conditions:

| Rule | What the proposed crease must do |
| --- | --- |
| 1 | Pass through both supplied points. |
| 2 | Reflect the first supplied point onto the second. |
| 3 | Reflect the first supplied line onto the second as a whole line. |
| 4 | Pass through the supplied point and be perpendicular to the supplied line. |
| 5 | Reflect one supplied point onto the supplied line and pass through the other supplied point. |
| 6 | Reflect each of two supplied points onto its corresponding target line. |
| 7 | Reflect the supplied point onto the first supplied line and be perpendicular to the second supplied line. |

For rule 3, prove that the chosen definition expresses equality of the
reflected line and the target line, not just an intersection or one matching
point. Rule 7 has two input lines. Keep all seven meanings independent of
the future solver and any list of computed candidates.

**Checks:** a separate, readable geometric example for every rule, proving
that its chosen crease satisfies the relation. These examples need not yet
show that all their inputs have a construction history.

#### 5. Specify legal finite-choice steps and audit exceptional cases

- Separate satisfying a fold relation from being a permitted construction
  step. A crease may satisfy an underconstrained relation without being a
  legal way to construct a new object.
- Define admissibility using finiteness of the set of distinct crease
  solutions in real geometry. Do not substitute finiteness of a solver's
  output or restrict this set to the algebraic values already represented.
- A legal selected fold must both be admissible and satisfy its relation.
  An empty solution set is finite but provides no crease to select. An
  infinite solution set is underconstrained and cannot provide a legal step.
- Prepare a case review for each rule: ordinary inputs, coincident points,
  coincident or parallel lines, points already on target lines, and whether
  the resulting solution set is empty, finite, or infinite. Do not reject
  every coincident-input case without checking its geometry.
- Prove representative exclusions now, including that rule 1 with identical
  input points cannot supply a legal finite-choice fold. Keep unique
  intersection requirements explicit as well.

This phase establishes the semantic rule and reviews the cases that later
implementations must cover. Executable admissibility guards, full solver
coverage, polynomial elimination, and the numerical bounds for all seven
rules are completed with their implementations in Phases 2–3. Record any
unsettled case explicitly; do not silently add a restriction to avoid it.

#### 6. Complete the specification audit

Before downstream automation relies on these definitions:

- Review every public geometric definition and fold statement against its
  intended meaning, including representation independence and all required
  nonzero or distinctness assumptions.
- Check the real interpretation, reflection identities, intersection
  uniqueness, all seven fold examples, and representative invalid or
  underconstrained cases in separate tests.
- Check axiom dependencies of the main interpretation and geometry theorems;
  allow only the ordinary Mathlib foundations. Leave no proof holes.
- Review module organization, names, documentation, duplication, and the
  replacement of Phase 0 probes. Run the relevant local library and test
  targets, and record the audit outcome and any later-phase obligations.

**Acceptance:** a usable real scalar interface; points and valid normalized lines
with faithful real interpretation; proved basic geometry; all seven fold
relations; finite-choice semantics that exclude underconstrained selections;
the examples and rejection checks above; and a completed specification audit.
This does not yet claim a fold solver or a proof of construction history.

### Phase 2 — Programs, checker soundness, and basic execution

**Goal:** write a finite construction program and obtain a kernel-checkable
proof that its final point was legally constructed and has the claimed
coordinates. Phase 1 supplies geometry; this phase adds construction history,
execution, and certification.

Work in the following dependency order. Keep program data, mathematical
construction rules, primitive implementations, checker proofs, and text
integration in modules with clear responsibilities. Keep the foundation
independent of the text interface and future widget. Finalize file names as
the interfaces settle, and document where each responsibility lives.

#### 1. Represent construction programs

- Use a finite sequence of instructions referring to earlier objects. Start
  with exactly `(0,0)` and `(1,0)`; axes and other objects must be constructed.
- Distinguish point and line references. Validate raw references before using
  them: reject missing, forward, or wrong-kind references. If internal types
  rule these out, retain explicit checks at the input boundary.
- Record the requested fold and its input references separately from its
  selected exact output or certificate. An arbitrary algebraic value is not
  evidence that the corresponding object has been constructed.
- Accommodate all seven fold operations in the program design from the start,
  reusing the Phase 1 input roles. Implement execution for rules 1, 2, and 4
  here; report rules 3, 5, 6, and 7 as unsupported until Phase 3. They must not
  acquire an unchecked acceptance path.
- Leave room for multiple outcomes in Phase 3. Persist a selected outcome by
  exact identity or certificate, never solely by solver ordering or a float.

**Checks:** a small program with several dependent steps; missing and forward
references; a line supplied where a point is required; an unsupported fold.

#### 2. Define mathematical construction histories

- Define what it means for points and lines to be constructible from the
  permitted initial points using legal folds and unique intersections.
  Inputs to each step must already have construction histories.
- Use the Phase 1 geometric relations and finite-choice legality over all
  real creases. Do not define validity merely as successful execution of the
  checker or membership in a solver's candidate list.
- Define the meaning of program states and outputs, including how exact
  objects are interpreted in real geometry. Use `Geometry/Exact.lean` and
  its Mathlib connections instead of duplicating coordinate formulas.
- State the relationship between a valid program history and mathematical
  constructibility. The statement must remain usable when the remaining
  primitive implementations are added.

**Checks:** initial points have construction histories; a valid step extends
one; merely supplying coordinates cannot introduce a new constructed object.
Audit these definitions before building the checker on top of them.

#### 3. Implement and certify the first operations

| Operation | Computation and required justification |
| --- | --- |
| Axiom 1 | Construct the line through distinct points; reuse the Phase 1 uniqueness and admissibility results. Reject identical inputs. |
| Axiom 2 | Construct the perpendicular bisector of distinct points. Prove it reflects the first onto the second and is the unique real crease. Reject identical points, which leave infinitely many choices. |
| Axiom 4 | Construct the line through the point perpendicular to the supplied line. Prove existence and uniqueness, including when the point is already on the supplied line. |
| Intersection | Use the nonzero-determinant guard and the proved unique-intersection formula. Reject both parallel distinct and coincident lines. |

For each supported fold, connect executable guards to semantic admissibility,
prove that the result satisfies the original relation, and prove completeness
over real crease solutions. The three supported folds each have exactly one
crease for admissible inputs. Reuse or extend Phase 1 lemmas rather than
introducing competing geometry implementations.

**Checks:** representative examples of each operation, horizontal and vertical
cases, an oblique case, and the invalid cases above. Keep operation selection
explicit: the solver answers a requested fold and does not search for an
entire construction sequence.

#### 4. Build the checker and prove soundness

- Interpret a program step by step, resolving inputs from the accepted prior
  state. Check input provenance, admissibility, and each selected output.
- Keep outcome computation separate from certification. A checked exact
  output and the relevant uniqueness/admissibility lemmas may suffice without
  rerunning exhaustive search.
- Prove that every accepted step preserves the state invariant, then prove
  that every accepted program produces mathematically constructible objects.
- Include final-target identification: selecting a point coordinate and
  claiming a value must require proof of exact equality to that value.
  Constructibility of an unrelated output does not prove the requested goal.
- Connect executable acceptance to kernel-checkable evidence. Do not use
  `native_decide`, unsafe evaluation, or an unchecked success flag as proof.
- Report malformed inputs, underconstrained folds, absent unique
  intersections, unsupported operations, and resource failures distinctly
  enough to explain the result. A resource failure is not a geometric proof.

**Checks:** successful multi-step certification; forged crease and intersection
outputs; an unconstructed input; an incorrect final target. Check the general
soundness theorem's transitive axiom dependencies.

#### 5. Add a minimal text interface and end-to-end examples

- Provide a small Lean text entry point for describing a program, choosing
  its final point coordinate, and obtaining the corresponding proof. An
  explicit Lean data representation is sufficient initially; a large custom
  syntax is not required.
- Use the same program and checker interfaces intended for the future GUI.
  Reopening and checking a saved example must require no interactive state.
- Starting only from `(0,0)` and `(1,0)`, construct the coordinate axes as
  lines and rational subdivision points on the initial axis. Prove the final
  points have coordinates `(1/2,0)`, `(1/4,0)`, and `(3/4,0)`.
- Keep these programs in separate readable test/demo files. Show their
  construction histories as well as their final coordinate conclusions.

**Checks:** replay the examples in a fresh Lean session; reject a target
mismatch and representative malformed text inputs; test execution separately
from theorem checking. Obtaining a point off the initial axis remains part
of Phase 3.

#### 6. Complete the program and checker audit

- Compare the implementation with every requirement above, especially input
  provenance, finite-choice legality, and exact final-target identification.
- Confirm that extending support to rules 3, 5, 6, and 7 will extend the
  existing program/checker structure without replacing its construction
  semantics. Their solvers, multiple branches, and remaining exceptional-case
  proofs belong to Phase 3.
- Review module boundaries, documentation, duplication, and error behavior.
  Remove temporary proof holes and development experiments.
- Run local validation for the library and all maintained tests/demos.
  Inspect axiom dependencies of the general soundness theorem and exported
  end-to-end proofs, allowing only the ordinary Mathlib foundations.
- Record the audit outcome, replay evidence, and any performance limitations.
  Push the checkpoint for version control without triggering GitHub Actions.

**Acceptance:** a replayable program starting from the two permitted points
constructs the axes and the three specified subdivision points; the checker
certifies every step and the exact final values; invalid references, wrong
input kinds, inadmissible steps, unsupported operations, and forged outputs
are rejected. The general soundness theorem and exported examples pass the
proof-dependency audit. The GUI and remaining fold solvers are later phases.

### Phase 3 — Complete primitive folding and elementary arithmetic

Proceed in the following dependency order, with audits at each checkpoint.
The phase is complete only when all checkpoints pass.

#### 3.1 — Exact real roots and branch selection

- Add an executable real-root interface over `Scalar`, using Hex's algebraic
  polynomial solver and exact `isReal` test. Prove that returned values are
  roots and that every real root is represented. Distinguish the zero
  polynomial (all real numbers) from a nonzero polynomial with no real roots.
  Remove repeated roots from the list of choices; multiplicity does not
  create another geometric choice. Test irrational coefficients, repeated
  roots, constant polynomials, and leading coefficients that vanish.
- Refactor the single-result solver interface to support a finite list of
  distinct creases. State soundness and completeness against the original
  geometric relation over `ℝ`, including real creases not initially given
  as algebraic coordinates. Infinite solution sets must be rejected as
  underconstrained; an empty finite set is a different outcome.
- Keep requests as references to existing objects and save the selected
  exact crease in each instruction. Reference resolution checks the inputs;
  certification checks that the selected crease is legal. Later the GUI will
  enumerate candidates before the user chooses; no automatic search for a
  sequence of folds is required. Never identify a saved branch solely by
  its position in a list or by approximate coordinates.
- Keep real interpretation in proofs, outside executable data. Audit the
  existing field-embedding certificate interface before extending it: an
  arbitrary field embedding cannot silently be assumed to preserve order.

#### 3.2 — Quadratic folds and an off-axis point

- Implement axiom 3, proving the equations describe reflection of the whole
  input line onto the other line. Cover intersecting lines (two bisectors),
  distinct parallel lines (one bisector), and coincident lines (infinitely
  many creases). Include horizontal and vertical lines.
- Implement axiom 5 using the fixed-point and point-to-line conditions.
  Cover two solutions, tangency, no solution, and exceptional cases where
  the source is on its target or coincides with the fixed point. Prove the
  exact admissibility classification, rather than imposing convenient
  extra input restrictions. Prove the finite bound of two creases.
- Give replayable programs selecting each available branch and rejecting
  forged selections. Construct a point off the initial axis from the two
  permitted seed points and prove its exact coordinates. No extra seed
  points or lines may be assumed.

#### 3.3 — Reusable arithmetic constructions

- Develop concrete primitive-step recipes and general correctness lemmas
  for signed coordinate placement, addition, subtraction, multiplication,
  and division by a nonzero value. Explain and check all degeneracies,
  including zero and negative operands.
- Support reuse by expanding recipes into ordinary instructions with
  correctly shifted references. The expanded program must use the same
  checker as a handwritten program; a recipe is not a new trusted axiom.
- Prove that a point is constructible exactly when both coordinates are
  constructible numbers. Inputs to arithmetic constructions must themselves
  have construction evidence; being an algebraic scalar is insufficient.
- Add separate, readable arithmetic and expansion examples with exact
  conclusions, and audit the semantic theorems and executable integration.

#### 3.4 — Axioms 7 and 6; complete primitive coverage

- Implement axiom 7 with its linear equations, including no-solution and
  underconstrained configurations; prove its finite bound of one crease.
- Implement axiom 6 with a proved equivalence between the two geometric
  reflection conditions and the solver's polynomial equations. Account for
  vertical creases, every denominator guard, degree drops, repeated roots,
  and source points already on their target lines. Handle degenerate
  systems explicitly; a vanishing elimination polynomial alone does not
  justify claiming that every crease is a solution.
- Prove soundness, completeness, admissibility classifications, and finite
  solution bounds for all seven primitives: respectively 1, 1, 2, 1, 2, 3,
  and 1. Resource failure must never be reported as a geometric impossibility.
- Give concrete examples with one, two, and three distinct axiom-6 creases,
  checking each against the original geometric relation. Include invalid
  and infinite-solution cases and exercise all seven operations through
  program replay, not just standalone solvers.

**Final acceptance:** all four checkpoints pass; every maintained test and
demo is on the local validation path; key soundness, completeness, arithmetic,
and end-to-end theorems pass a transitive axiom audit. Record the audit and
remaining performance limits. Push the checkpoint for version control without
adding a GitHub Actions validation requirement. Constructing every real root
of an arbitrary cubic from its coefficients remains Phase 4.

### Phase 4 — Encode quadratics and cubics as constructions

Prove constructibility of square roots of nonnegative constructible values
and of every real root of a cubic with constructible coefficients and
nonzero leading coefficient. Use Phase 3 arithmetic to construct the input
configurations; do not assume those inputs are available for free.

#### Work order and checkpoints

Phase 3 established closure under field operations. This phase extends that
closure to every real root of a quadratic or cubic with constructible
coefficients. Results must compose: a root may be used in arithmetic and then
as a coefficient in another root construction. Hex root computation alone
never supplies construction evidence.

1. **Polynomial encoding and geometry.** Audit the proposed axiom-6
   configuration below, prove its polynomial correspondence, and prove finite
   admissibility, including zero coefficients and coincident source points.
   Keep these identities independent of Hex and the user interface.
2. **Construction provenance and closure.** Construct every input from the
   coefficient histories, extract the selected root using legal operations,
   and prove closure for all real roots. Normalize nonmonic cubics only with
   a nonzero leading coefficient. Derive quadratic and nonnegative square-root
   closure, with separate linear and constant cases. Reusing the cubic
   construction for a quadratic multiplied by the variable is permitted:
   prove the correspondence and identify the selected root explicitly.
3. **Executable constructions.** Supply reusable recipes expanding into the
   existing fold/intersection language. Saved root choices are checked against
   their coefficients; they are never supplied as initial constructed points.
   Include a composed construction using a previously constructed root.
4. **Examples and audit.** Prove the exact examples below, including branch
   identification for trisection. Cover repeated roots, three real roots,
   zero roots/coefficients, and invalid choices. Validate all maintained local
   targets and audit transitive axioms of closure and demo theorems. Record
   remaining limitations and push the checkpoint for version control.

The implemented and Lean-verified configuration for a monic cubic
`p(t) = t^3 + a*t^2 + b*t + c` is:

- `P₁ = (0,1)`, target `L₁: y = -1`;
- `P₂ = (c-a,b)`, target `L₂: x = -a-c`.

The first alignment excludes vertical creases and forces a crease
`F: y = t*x - t^2`. The horizontal displacement of `reflect F P₂` from
`L₂` is `2*p(t)/(1+t^2)`. Prove the equivalent polynomial alignment equations in both directions, the
configuration's constructibility, finite admissibility, and extraction of
the root from the crease. The unknown root is not an input assumed already
constructible. The implementation covers coincident source points and the
horizontal crease at a zero root; no alternative encoding was needed.

Normalize a general cubic using the leading coefficient. State and prove
the theorem for every real root, not just existence of one selected root.
Handle lower-degree polynomials through separate linear/quadratic results.

**Tests and acceptance:** exact `√2` and `∛2` constructions, a concrete
trisection of a 60-degree angle with a proved angle/branch characterization,
and cubics with zero coefficients and repeated or three distinct real roots.
All demonstrations conclude the claimed value or geometric property, not
merely that some polynomial vanishes.

**Completion:** all four checkpoints passed. The generic closure theorems,
coefficient-building recipes, exact-value and trisection proofs, rational kernel
replay, irrational Hex replay, and existing widget checks are validated locally.
The [Phase 4 audit](docs/phase-4.md) records coverage and the distinction between
native integration checks and kernel-checked proof evidence.

### Phase 5 — Stable text interface and proof artifacts

Complete readable commands for all primitives, branch selection, reusable
constructions, and final-coordinate submission. Persist exact choices and
provide errors at the responsible instruction. Printed/exported programs
must reconstruct the same exact values.

**Tests and acceptance:** replay the substantial Phase 4 examples through
the public interface; round-trip saved programs; check target mismatch and
invalid macro inputs; verify behavior is independent of candidate ordering.
Keep demos separate from implementation modules.

#### Shared-program repair — completed 2026-10-09

The first Phase 5 implementation was incorrectly marked complete. Its text
commands built proof-bearing real objects directly instead of the existing
`Program`. Successful example proofs and source export did not establish the
promised common backend. The repair below is complete; see
[the Phase 5 audit](docs/phase-5.md) for validation and limitations.

1. **Prove acceptance without wholesale reduction.** Keep `Program`, its
   executable checker, and `accepts_sound`. Establish a small theorem interface
   for proving the checker's actual steps from algebraic certificates. Test an
   irrational saved program before committing to the frontend design. Native
   computations may provide immediate feedback without generating proofs.
2. **One construction record.** Use ordinary Lean `do` notation with the
   existing `RecipeBuilder` for named construction instructions and references.
   Remove the duplicate bespoke command parser as well as its proof objects. Reuse existing recipe expansion for arithmetic
   and roots. Remove the separate proof-bearing `Text.Point/Line/Number` path;
   do not preserve it behind new wrappers. Proof generation happens separately
   on the actual saved program and checks every step, including unused steps.
3. **Exact identity and submission.** Certificates must concern the exact saved
   choices and final target. Show how symbolic algebraic proofs relate to the
   executable scalar representation; no unrelated constructibility theorem or
   native success flag can substitute for acceptance of the saved program.
4. **Examples, persistence, and audit.** Migrate the square-root, cube-doubling,
   iterated-root, and trisection examples; retain all seven primitive commands,
   reusable constructions, error locations, exact branch identity, and fresh
   export/replay. Test malformed references, bad unused steps, wrong selections,
   invalid recipe arguments, target mismatch, and candidate-order independence.
   Run local validation and transitive axiom checks before marking complete.

Keep this repair small: prefer refactoring existing abstractions, remove the
superseded implementation and stale documentation, and record the source-size
change at the audit. Shared programs and proof certificates are distinct:
editing and immediate feedback must not require building kernel proofs.

### Phase 6 — ProofWidgets construction interface

Implement the goal-directed interface described above using the existing
program and solver APIs. Add numerical rendering, branch previews, object
inspection, undo, pan/zoom, and persistent proof submission. Expose precise
failure explanations without exposing irrelevant backend details.

**Tests and acceptance:** perform the rational, square-root, and cube-root
demos through the widget; verify the trisection example is inspectable.
Reopen exported proofs without widget state. Check close branches, vertical
lines, zoom changes, undo during pending computation, stale source edits,
and a deliberately incorrect final target. Document repeatable manual GUI
checks alongside automated backend and integration tests.

### Phase 7 — Package the main theory and release

Package the arithmetic results as a subfield of `ℝ`, and expose clean
square-root and cubic-root closure theorems. Prove all constructible
coordinates are algebraic over `ℚ`, using the full primitive case analysis.
Connect the executable construction results to these public statements.

Write a tutorial covering a complete GUI-to-proof example and the equivalent
text program, explain the trust boundary and ideal-plane model, and document
all full-build commands. Refactor duplicated code and stabilize imports.

**Acceptance:** every main-release requirement is met; all maintained tests
and demos build from a fresh checkout; key results pass transitive axiom
audits; documentation matches behavior; measured example performance and
known limitations are recorded. Excluding tests from default targets cannot
hide failures. No `sorry`, unproved project axiom, or native-execution trust
shortcut occurs in certification.

### Phase 8 — Real extension-tower characterization (later)

State the precise equivalence: a real number is origami-constructible iff it
belongs to the last field of a finite tower of subfields of `ℝ`, beginning
with the image of `ℚ`, whose successive extension degrees are 2 or 3.
Trivial extensions can be omitted; rational values allow a tower of length
zero. Prove both directions, including primitive generation and real
embedding details. A numerical degree of the form `2^a * 3^b` alone is not
the proposed criterion.

Use Mathlib intermediate fields, minimal polynomials, and finite-dimensional
extension theory. Relate finite construction histories to finite towers,
including the combination of fields from different prior branches.

**Tests and acceptance:** instantiate the equivalence on representative
quadratic and cubic towers and derive a nonconstructibility example such as
the real fifth root of 2. Audit both directions and all embedding hypotheses.

### Phase 9 — Symbolic construction programs (stretch)

Extend reusable programs with symbolic inputs and explicit hypotheses.
Interpret operations as generating proof obligations for validity,
distinctness, determinants, root existence, and branch selection. Reuse
general geometric theorems instead of pretending numerical Hex execution
decides symbolic propositions.

Start with text-based symbolic recipes; add widget support only after their
semantics work. A concrete program need not generalize automatically because
its parameters can change degeneracies and available branches.

**Tests and acceptance:** reusable midpoint and arithmetic constructions,
followed by a square-root construction under a nonnegativity hypothesis;
show the generated obligations and handle the zero case explicitly.

## 5. Audits, risks, and progress

At every checkpoint record the acceptance criteria met, exact validation
commands/results, axiom checks, performance observations when relevant, and
remaining limitations. Audit specification fidelity as well as compilation.
Use an extra checkpoint after changes to primitive rules or the public
certification interface. Fix in-scope issues before claiming completion.

| Risk | Required response |
| --- | --- |
| Hex/toolchain incompatibility or incomplete real API | Resolve in Phase 0; pin verified compatible revisions and isolate the adapter. |
| Exact computation is fast but kernel checking is slow | Measure separately; use verified compact certificates or shared computations, retaining kernel checking. |
| Infinite-choice or missing exceptional-case loophole | Audit semantic admissibility and prove coverage, not only candidate validity. |
| Cubic elimination loses or invents folds | Prove reconstruction/completeness and check original constraints, including vertical and degree-drop cases. |
| Target root is ambiguous | Retain exact identity and prove equality or an isolating characterization. |
| GUI and proof disagree | Render identified exact objects and replay persisted instructions independently of the GUI. |
| Scope exceeds the initial week | Report evidence and remaining work; prioritize sound end-to-end milestones without silently dropping agreed requirements. |

Current status: Phase 5 is complete (2026-10-09), including the shared-program
repair; see [the audit](docs/phase-5.md).
Phase 4 is complete (2026-10-08); see [its audit](docs/phase-4.md).
Phase 3 is complete (2026-10-08). Phase 6 has not started.
Phase 2 is complete (2026-10-08). Phases 0 and 1 completed
on 2026-10-07. The previous implementation
is preserved in the verified remote archive, and the fresh dependency baseline
is pinned. Local library/test/demo builds, semantic proofs, native and
interpreter arithmetic tests, and widget insertion/replay checks passed.
Kernel timings and the checkpoint audit are recorded in
[the Phase 0 report](docs/phase-0.md), including the remaining adapter,
certificate, and editor-host limitations.

Phase 1 provides the executable real algebraic field, canonical valid lines,
proved reflection and intersection geometry, faithful Mathlib interpretation,
all seven fold relations, and real finite-choice legality. Separate examples,
axiom audits, and the full local validation script passed, including native
and interpreter execution and widget replay. See [the Phase 1 audit](docs/phase-1.md)
for the exceptional-case review and remaining solver/provenance obligations.
Phase 2 is complete (2026-10-08). Replayable programs now certify construction
histories from the two seeds, rules 1, 2, and 4, unique intersections, and
exact final-coordinate claims. The saved subdivision program proves the
axes and quarter-point outputs; malformed references, invalid steps, wrong
targets, forged outputs, and unsupported folds are rejected. General
soundness and end-to-end proofs passed the axiom audit. Full local validation,
including Hex construction execution and widget replay, passed after fixing
the runtime interpretation boundary. See [the Phase 2 audit](docs/phase-2.md)
for the module guide, evidence, and remaining scope.

Phase 3 complete: all seven saved-fold checks, complete real-crease discovery,
finite-admissibility classifications, and solution bounds are implemented.
Intersecting lines have exactly two bisectors; parallel and coincident cases
are classified separately. Exact Hex discovery distinguishes infinite families,
empty sets, and distinct finite choices, including degenerate and genuine
cubic cases. Coordinate placement, point/coordinate equivalence, and arithmetic
construction theorems are proved. Reusable recipes expand into ordinary
programs with relocated references. Kernel-checked demos cover all seven rules,
three axiom-6 branches, and composed signed arithmetic.

`LEAN_NUM_THREADS=1 bash scripts/validate.sh` passed: the library, every test
and demo, the older runtime suite, expanded Hex discovery/arithmetic/replay,
and widget insertion plus standalone proof replay. Key results passed the
transitive axiom audit using only ordinary Mathlib foundations. No proof holes,
project axioms, or native decision proofs were introduced. See
[the Phase 3 audit](docs/phase-3.md) for case coverage, implementation details,
and performance limits. Validation was local; no GitHub Actions run was needed.

Phase 5 repair complete: ordinary `RecipeBuilder` programs now serve text
assembly, native replay, and kernel-checked submission. `origami_check` proves
acceptance of the actual saved record; the duplicate proof-object interface
was removed. All four substantial root examples, a concrete Hex candidate,
rejection locations, candidate-order independence, and fresh artifact replay
passed local validation and transitive axiom checks. Production library source
shrunk by 82 lines. Automatic certificate extraction from arbitrary opaque Hex
values remains a limitation, not a completed feature. Phase 6 has not started.

## 6. Potential future work — interactive visual proving

These are exploratory directions, not additions to the implementation phases
or current release acceptance criteria. Prioritize the first two when
revisiting future scope. The aim is to let visual interaction help users
discover, state, and assemble mathematical arguments, with Lean checking
the resulting precise claims.

### Geometric claims made directly on the picture

Let users select constructed objects and mark a relationship: equal segment
lengths, perpendicular lines, collinear points, a point on a circle, or an
angle equal to one-third of another. Translate the selection into an explicit
Lean proposition and attempt to prove it from the construction history and
established geometric facts.

Show the exact claim and whether it is proved or remains a goal. A visual
mark creates a claim, never an assumption justified solely by appearance.
Preserve the proof in a form that replays without the GUI. This extends the
interface from proving constructibility to proving properties of constructions.

### Dragging a construction toward a general theorem

Let users designate starting objects as variable and drag them while dependent
objects update according to the same construction. For example, explore a
midpoint construction, then request a theorem that it produces the midpoint
for any two distinct input points.

Use the interaction to discover a conjecture and its required hypotheses.
Generalization must produce a symbolic statement and a proof for arbitrary
inputs satisfying those hypotheses; checking sampled positions is not proof.
Expose changes in validity, degeneracies, and branch choices rather than
silently assuming the concrete construction works everywhere. This would
provide a visual interface to the symbolic-program work described in Phase 9,
without expanding that phase's current commitments.

### Further directions to explore

- **Assemble arguments visually:** select objects and established facts to
  apply theorems such as triangle congruence. Display intermediate conclusions
  and remaining proof obligations, with each action producing a Lean proof step.
- **Explore loci and invariants:** move an input along a specified set, trace
  dependent objects, and propose claims about their positions or unchanged
  quantities. Distinguish containment in a proposed locus from equality with
  that locus, which also requires proving that every point on it is reachable.
- **Expose exceptional cases:** show why a construction fails or changes its
  number of solutions during dragging. Let users split an argument into cases,
  each with explicit hypotheses and separate proof obligations.
- **Compare and simplify constructions:** prove that two methods produce the
  same output under stated assumptions, or certify replacing a sequence with
  a reusable construction that preserves its result.
- **Replay proofs as explanations:** animate certified steps and let readers
  select a conclusion to inspect the earlier objects, facts, and theorems on
  which it depends.

## 7. References

- [Hex executable algebraic numbers and API overview](https://github.com/leanprover/hex-number-field)
- [Hex Mathlib correspondence](https://github.com/leanprover/hex-number-field-mathlib)
- [ProofWidgets4](https://github.com/leanprover-community/ProofWidgets4)
- [Alperin–Lang: One-, Two-, and Multi-Fold Origami Axioms](https://langorigami.com/wp-content/uploads/2015/09/o4_multifold_axioms.pdf)
- [Verifiable Origami Folding](https://www.scs.stanford.edu/~geoff/papers/7OSME-paper-revised.pdf)

Consult the dependency versions actually pinned in Phase 0. These references
guide the work; their claims do not replace Lean proofs or specification
audits, and unrelated simultaneous-fold machinery is outside scope.
