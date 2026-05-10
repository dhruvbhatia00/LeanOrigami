# Origami Tactic Plan

This document records the current plan for the proof-producing origami tactic.
The goal is to keep implementation steps small and mostly in new files, so the
core formalization files remain stable while teammates work.

## Goal

Build a text-first tactic that helps prove goals such as:

```lean
⊢ cons_point P
⊢ constructible_real_proj x
```

The user supplies a script describing an origami construction. The tactic
tracks the current paper state, checks that each construction step is valid,
creates proof terms for the corresponding `cons_point` or `cons_line`
judgments, and displays the current state in the infoview.

The initial tactic should be proof-oriented and text-based. Later versions can
add reusable macro steps and an interactive widget.

## Current Design Decisions

### Valid Lines

`cons_line` constructors now require `valid L`. This is important because the
zero line `![0, 0, 0]` would otherwise satisfy many incidence relations and
could collapse the intended constructibility theory.

Raw axiom predicates such as `Axiom1`, `Axiom2`, etc. may remain algebraic
relations. The constructibility layer is responsible for only admitting valid
fold lines.

### Canonical Objects

The tactic should prefer canonical point and line expressions over arbitrary
mathematically equal expressions. This helps unification and keeps generated
proof terms predictable.

Examples:

```lean
Axiom1Spec.lineThrough P Q
Axiom2Spec.perpendicularBisector P Q
intersectionPoint L M
```

The tactic may still store facts proving that a user-given object is equal to a
canonical one, but internally canonical forms should be the default.

### User Proof Obligations

The user should not be forced to manually unfold all coordinates just to prove
nondegeneracy facts. Each tactic step should add useful named facts to the local
context, such as:

```lean
h_l_def : l = Axiom1Spec.lineThrough P Q
h_l_valid : valid l
h_l_coeffs : l = ![...]
```

When a nondegeneracy proof is needed, the tactic should first try automation:

```lean
norm_num
positivity
ring_nf; nlinarith
aesop
```

If automation fails, the tactic should leave a subgoal with all accumulated
facts available.

### Proof Roots Versus Display Roots

For polynomial-based folds, the proof layer can use noncomputable roots chosen
by existence theorems:

```lean
noncomputable def chooseRoot (p : Polynomial ℝ) (h : ∃ r, p.IsRoot r) : ℝ :=
  Classical.choose h
```

The visualization layer can compute floating approximations separately. The
proof root and display root do not need to be definitionally equal.

## Proposed File Layout

New implementation should go into new files where possible.

### `LeanOrigami/ConstructibleLemmas.lean`

This file should import `LeanOrigami.constructible` and contain tactic-facing
construction lemmas.

Likely contents:

```lean
lemma valid_lineThrough
    {P Q : Point}
    (hsep : P 0 ≠ Q 0 ∨ P 1 ≠ Q 1) :
    valid (Axiom1Spec.lineThrough P Q)

lemma valid_perpendicularBisector
    {P Q : Point}
    (hsep : P 0 ≠ Q 0 ∨ P 1 ≠ Q 1) :
    valid (Axiom2Spec.perpendicularBisector P Q)

theorem cons_line_axiom1_lineThrough
    {P Q : Point}
    (hP : cons_point P) (hQ : cons_point Q)
    (hsep : P 0 ≠ Q 0 ∨ P 1 ≠ Q 1) :
    cons_line (Axiom1Spec.lineThrough P Q)

theorem cons_line_axiom2_perpendicularBisector
    {P Q : Point}
    (hP : cons_point P) (hQ : cons_point Q)
    (hsep : P 0 ≠ Q 0 ∨ P 1 ≠ Q 1) :
    cons_line (Axiom2Spec.perpendicularBisector P Q)
```

Also define canonical intersections:

```lean
noncomputable def intersectionPoint (L M : Line) : Point := ...

lemma intersects_at_intersectionPoint
    {L M : Line}
    (hdet : L 0 * M 1 - M 0 * L 1 ≠ 0) :
    intersects_at L M (intersectionPoint L M)

theorem cons_point_intersectionPoint
    {L M : Line}
    (hL : cons_line L) (hM : cons_line M)
    (hdet : L 0 * M 1 - M 0 * L 1 ≠ 0) :
    cons_point (intersectionPoint L M)
```

### `LeanOrigami/PolynomialTools.lean`

This file should contain polynomial utilities used by axiom specifications and
the tactic.

Use mathlib's `Polynomial ℝ` API rather than ad hoc polynomial predicates.

Likely definitions:

```lean
def quadraticPoly (A B C : ℝ) : Polynomial ℝ :=
  Polynomial.C A * Polynomial.X^2 + Polynomial.C B * Polynomial.X + Polynomial.C C

def cubicPoly (A B C D : ℝ) : Polynomial ℝ :=
  Polynomial.C A * Polynomial.X^3 +
    Polynomial.C B * Polynomial.X^2 +
    Polynomial.C C * Polynomial.X +
    Polynomial.C D
```

Bridge lemmas:

```lean
lemma quadraticPoly_isRoot_iff :
    (quadraticPoly A B C).IsRoot r ↔ A*r^2 + B*r + C = 0

lemma cubicPoly_isRoot_iff :
    (cubicPoly A B C D).IsRoot r ↔ A*r^3 + B*r^2 + C*r + D = 0
```

Quadratic existence:

```lean
lemma quadratic_exists_root_of_discriminant_nonneg
    {A B C : ℝ}
    (hA : A ≠ 0)
    (hdisc : 0 ≤ B^2 - 4*A*C) :
    ∃ r : ℝ, (quadraticPoly A B C).IsRoot r
```

Cubic existence:

```lean
lemma cubic_exists_root
    {A B C D : ℝ}
    (hA : A ≠ 0) :
    ∃ r : ℝ, (cubicPoly A B C D).IsRoot r
```

The cubic lemma may require IVT or a mathlib theorem about real polynomials of
odd degree. This is a likely roadblock and should be investigated before the
axiom 6 tactic work.

Choice helpers:

```lean
noncomputable def chooseRoot (p : Polynomial ℝ) (h : ∃ r, p.IsRoot r) : ℝ :=
  Classical.choose h

lemma chooseRoot_isRoot (p : Polynomial ℝ) (h : ∃ r, p.IsRoot r) :
    p.IsRoot (chooseRoot p h)
```

### `LeanOrigami/Tactic/State.lean`

This file should contain meta-level bookkeeping types.

Sketch:

```lean
structure PaperPoint where
  name : Name
  expr : Expr
  proof : Expr
  facts : Array (Name × Expr)

structure PaperLine where
  name : Name
  expr : Expr
  proof : Expr
  validProof : Expr
  facts : Array (Name × Expr)

structure PaperState where
  points : NameMap PaperPoint
  lines : NameMap PaperLine
  facts : Array (Name × Expr)
```

Here `NameMap α` is a finite meta-level map from Lean names to values of type
`α`. It is used to look up objects introduced by the DSL.

### `LeanOrigami/Tactic/Syntax.lean`

This file should define the first text DSL.

Initial commands:

```lean
point O := origin
point I := one
line l := axiom1 P Q
line m := axiom2 P Q
point X := intersection l m
exact_point X
exact_x X
exact_y X
```

Later commands:

```lean
line l := axiom3 ...
line l := axiom4 ...
line l := axiom5 ...
line l := axiom6 ...
line l := axiom7 ...
```

The syntax should allow optional proof blocks for nondegeneracy:

```lean
point X := intersection l m by
  ring_nf
  norm_num
```

### `LeanOrigami/Tactic/Elab.lean`

This file should elaborate the DSL and generate proof terms.

Responsibilities:

1. Maintain a `PaperState`.
2. Resolve names from the DSL.
3. Generate canonical expressions for new points and lines.
4. Generate proof terms using construction lemmas.
5. Try automation for side goals.
6. Add useful facts to the local context.
7. Log the state to the infoview after each step.
8. Close the final goal.

## First Implementation Milestone

The first working version should support only:

```lean
origin
one
axiom1
axiom2
intersection
exact_x
exact_y
```

This is enough to test the full architecture without polynomial roots.
Axiom 4 can be added soon after this first milestone, since the canonical
construction is already available as `Axiom4Spec.perpendicularLine` together
with `Axiom4Spec.axiom4_scaled_iff`.

Example target:

```lean
example : constructible_real_proj 0 := by
  origami_construct
    point O := origin
    exact_x O
```

More interesting examples should use canonical line and intersection
construction once those lemmas exist.

## Roadblocks To Watch

### Degenerate Geometry

The tactic must avoid:

* coincident points for unique lines;
* invalid fold lines;
* parallel or identical lines for intersections;
* zero leading coefficients in polynomial root steps.

### Equality Up To Scaling

Geometric lines are homogeneous, but Lean terms are exact coefficient vectors.
The tactic should store exact canonical lines initially. Scaling-equivalence
support can be added later.

### Polynomial Root Automation

Quadratic roots need discriminant nonnegativity. Cubics need an existence
theorem over `ℝ`. User proof blocks should be supported, but only after the
tactic has exposed all relevant coordinate facts.

### Widget Separation

The proof tactic should not depend on visualization. The widget or infoview
state display should consume a separate view of the paper state.

## Recommended Next Step

Create `LeanOrigami/ConstructibleLemmas.lean` and prove the canonical validity
and construction lemmas for:

1. axiom 1 line through two distinct points;
2. axiom 2 perpendicular bisector of two distinct points;
3. canonical intersection point of two transverse lines.

Then begin the tactic files with only origin, one, axiom 1, axiom 2, and
intersection support.
