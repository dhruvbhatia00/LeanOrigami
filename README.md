# Lean Origami

This project provides a formalization of Huzita–Hatori origami axioms in Lean 4. It enables users to perform geometric constructions on a virtual "piece of paper" (modeled as the real affine plane) and formally prove that resulting points and lines are origami-constructible.

The long-term goal of the project is to prove that origami-constructible numbers form a field closed under square and cube roots, and to provide an interactive graphical interface for building these proofs.

## Features

- **Analytic Foundation:** A robust coordinate-based model of points and lines in $\mathbb{R}^2$.
- **Formalized Axioms:** Implementation of the seven Huzita-Hatori axioms as algebraic predicates.
- **Constructibility Predicates:** A mutual inductive definition (`cons_point` and `cons_line`) that tracks the provenance of every geometric object.
- **Domain-Specific Tactic:** The `origami_construct` tactic, which allows users to write proofs using a natural, step-by-step construction language.

---

## Installation

### Prerequisites

- Lean 4 and `elan`
- `lake` (Lean's build system, included with Lean 4)

### Setup

Clone the repository:

```bash
git clone https://github.com/your-repo/lean-origami.git
cd lean-origami
```

Build the project:

```bash
lake build
```

---

## Usage

You can use the `origami_construct` tactic to prove that a specific value or point is constructible. The tactic manages the "paper state," allowing you to name new points and lines as you go.

```lean
import LeanOrigami.Elab

example : constructible_real_proj 0 := by
  origami_construct
    point O := origin
    point I := one
    line xAxis := axiom1 O I
    line yAxis := axiom4 xAxis O

    -- Axiom 5 (placing a point onto a line)
    line fold := axiom5_pos I O yAxis

    exact_y O
```

---

## Supported Tactic Commands

- `point <name> := origin | one`
- `line <name> := axiom1 <p1> <p2>`  
  *(Line through two points)*
- `line <name> := axiom2 <p1> <p2>`  
  *(Perpendicular bisector)*
- `line <name> := axiom4 <line> <point>`  
  *(Perpendicular through a point)*
- `line <name> := axiom5_pos/neg/linear <p1> <p2> <line>`  
  *(Fold point onto line)*
- `point <name> := intersection <line1> <line2>`
- `exact_x <point> / exact_y <point>`  
  *(Close the goal)*

---

## Project Structure

- `Basic.lean`  
  Definitions of `Point` and `Line`, and basic incidence geometry (e.g., `is_contained`, `reflection`, `intersection`).

- `Axioms.lean`  
  The core algebraic predicates for the 7 Huzita-Hatori axioms.

- `constructible.lean`  
  The bridge between geometry and algebra. Defines `cons_point`, `cons_line`, and the concept of constructible real numbers.

- `Elab.lean`  
  The metaprogramming core. Implements the `origami_construct` tactic and the `PaperState` logic.

- `TACTIC_PLAN.md`  
  A roadmap for ongoing development.

---

## Future Work

The project is currently in active development. Planned milestones include:

- **Axiom 6 & Cubics:**  
  Formalizing the "mighty" sixth axiom, which allows for trisecting angles and doubling the cube by solving cubic equations.

- **Field Theory:**  
  Formally proving that the set of constructible numbers forms a subfield of $\mathbb{R}$ closed under degree-2 and degree-3 extensions.

- **Interactive Widgets:**  
  Implementing `ProofWidgets4` interfaces to allow users to click and drag folds on a visual SVG canvas, which then generates the corresponding Lean code.

- **Tactic Automation:**  
  Extending the tactic to automatically find construction sequences for common targets (e.g., midpoints, angle trisectors).

---

## License

This project is released under the Apache 2.0 License.