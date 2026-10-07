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

Implement scalar transport, points, normalized valid lines, incidence,
perpendicularity, reflection, and transverse intersection. Prove their
basic identities and geometric interpretation. Specify all seven fold
relations and the finite-choice construction semantics independently of
the executable solver.

Audit the intended case distinctions for every operation. In particular,
review whether coincident inputs leave finitely or infinitely many solutions
rather than rejecting them indiscriminately. Axiom 7 takes two input lines.

**Tests and acceptance:** reflection across `x=1` sends `x=0` to `x=2`;
normalization respects nonzero scaling; invalid lines are unrepresentable or
rejected; coincident-line intersections and underconstrained folds are not
legal steps. Include simple geometric examples of all seven relations.
Complete a specification audit before downstream automation relies on it.

### Phase 2 — Programs, checker soundness, and basic execution

Implement the program representation, exact object references, interpretation,
and certification. Support base points, operations 1, 2, and 4, and
intersections. Prove the general soundness argument and instantiate these
primitive cases. Add a minimal text entry point for replayable programs.

**Tests and acceptance:** build axes and rational subdivision points; prove
the final coordinates are `1/2`, `1/4`, and `3/4`. Reject malformed references,
wrong object types, inadmissible steps, and forged outputs. Check the exported
theorems' axiom dependencies and replay in a fresh Lean session.

### Phase 3 — Complete primitive folding and elementary arithmetic

Proceed in audited increments:

1. Implement operations 3 and 5, including both quadratic branches and
   degenerate finite cases; obtain a constructible point off the initial axis.
2. Develop concrete reusable constructions and general lemmas for signed
   coordinate placement, addition, subtraction, multiplication, and nonzero
   division. Establish that a point is constructible exactly when its two
   coordinates are constructible.
3. Implement operation 7 and the complete operation-6 solver, with the
   geometric/algebraic bridges, explicit guards, soundness, completeness,
   and finite-solution bounds for all seven primitives.

**Tests and acceptance:** successful examples of each operation, multiple
branches, no-solution and underconstrained inputs, vertical folds, repeated
roots, and degree drops. Demonstrate arithmetic recipes and macro expansion.
Give concrete examples exercising one, two, and three distinct axiom-6
solutions. Each result must satisfy the original geometric relation.

### Phase 4 — Encode quadratics and cubics as constructions

Prove constructibility of square roots of nonnegative constructible values
and of every real root of a cubic with constructible coefficients and
nonzero leading coefficient. Use Phase 3 arithmetic to construct the input
configurations; do not assume those inputs are available for free.

A preferred starting candidate for a monic cubic
`p(t) = t^3 + a*t^2 + b*t + c` is:

- `P₁ = (0,1)`, target `L₁: y = -1`;
- `P₂ = (c-a,b)`, target `L₂: x = -a-c`.

The first alignment excludes vertical creases and forces a crease
`F: y = t*x - t^2`. The horizontal displacement of `reflect F P₂` from
`L₂` is `2*p(t)/(1+t^2)`. Formalize this calculation and its converse, the
configuration's constructibility, finite admissibility, and extraction of
the root from the crease. The unknown root is not an input assumed already
constructible. This candidate is not yet Lean-verified; audit all cases,
including coincident input points, before adopting it as the final theorem.
Lill's method is a reference alternative if it gives a better specification.

Normalize a general cubic using the leading coefficient. State and prove
the theorem for every real root, not just existence of one selected root.
Handle lower-degree polynomials through separate linear/quadratic results.

**Tests and acceptance:** exact `√2` and `∛2` constructions, a concrete
trisection of a 60-degree angle with a proved angle/branch characterization,
and cubics with zero coefficients and repeated or three distinct real roots.
All demonstrations conclude the claimed value or geometric property, not
merely that some polynomial vanishes.

### Phase 5 — Stable text interface and proof artifacts

Complete readable commands for all primitives, branch selection, reusable
constructions, and final-coordinate submission. Persist exact choices and
provide errors at the responsible instruction. Printed/exported programs
must reconstruct the same exact values.

**Tests and acceptance:** replay the substantial Phase 4 examples through
the public interface; round-trip saved programs; check target mismatch and
invalid macro inputs; verify behavior is independent of candidate ordering.
Keep demos separate from implementation modules.

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

Current status: this document records the agreed implementation direction.
No restart phase is complete. The previous repository review and successful
legacy build are background evidence, not validation of the new design.
AGENTS.md has been added locally; preservation and reset remain pending.

## 6. References

- [Hex executable algebraic numbers and API overview](https://github.com/leanprover/hex-number-field)
- [Hex Mathlib correspondence](https://github.com/leanprover/hex-number-field-mathlib)
- [ProofWidgets4](https://github.com/leanprover-community/ProofWidgets4)
- [Alperin–Lang: One-, Two-, and Multi-Fold Origami Axioms](https://langorigami.com/wp-content/uploads/2015/09/o4_multifold_axioms.pdf)
- [Verifiable Origami Folding](https://www.scs.stanford.edu/~geoff/papers/7OSME-paper-revised.pdf)

Consult the dependency versions actually pinned in Phase 0. These references
guide the work; their claims do not replace Lean proofs or specification
audits, and unrelated simultaneous-fold machinery is outside scope.
