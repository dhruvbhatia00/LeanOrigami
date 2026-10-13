# Constructing a proof visually

Phase 6 is under development. The procedures below describe the intended
interface; the checkpoint audit records which checks have actually passed.

To view a completed construction, open `LeanOrigamiDemos/Visual.lean` and put
your cursor on `origami saved` inside `half` or `squareRoot`. The panel restores
the drawing and lets you edit it even though the theorem is already proved.
Open **Lean 4: Toggle Infoview** from the command palette if the panel is hidden.
The `cubeRoot` and `trisection` theorems still provide empty starting panels;
keep their `all_goals` fallback lines while exploring. For a new construction,
use a fresh theorem with bare `origami`.

Import `LeanOrigami.Widget`. Inside a `ConstructibleNumber` proof, write
`origami` and place the cursor on that tactic. The panel starts with the two
seed points, `(0, 0)` and `(1, 0)`. The goal stays open while you construct.

Choose an operation, then fill its labelled input slots. You can use the
object dropdowns or select objects in the drawing. For a fold, click
**Preview folds**, inspect the orange candidates, then click **Use fold** for
the desired choice. For an intersection, select two lines and click
**Add intersection**. The object list gives stable numbers even when drawings
overlap. Empty canvas is for panning, not creating arbitrary points.

Canvas labels `P0`, `P1`, `L2`, … match the object references in the controls.
The grid labels show the displayed coordinate scale. Hover over a point or
line to see its approximate coordinates or equation below the canvas. Values
are rounded to six significant digits, with unnecessary trailing zeros omitted. Each
operation explains what its fold must do, and the selection hint names the
input that the next canvas click will fill.

Drag the canvas to pan. Use the zoom buttons or mouse wheel to zoom, and
**Reset view** to return to the seeds. **Refine display** asks Hex for tighter
approximations. Screen coordinates are approximate; the saved objects and
selected branches remain exact. At extreme magnification, floating-point
rendering can still make distinct objects overlap: select by object or choice
number. Refinement has a finite resource limit.

**Undo** removes the last committed operation. It also invalidates older
previews and pending submissions. Changing inputs invalidates old previews.
Changes to the source file require reopening the construction at the current
goal; an old session cannot overwrite the new source.

Select the final point and its x or y coordinate, then click **Submit**. Lean
checks the complete construction and proves that its coordinate equals the
original goal. Only after that succeeds does **Save construction** appear.
Saving replaces the tactic with `origami saved (...)`, containing the exact
program, submitted coordinate, and checked certificates. This tactic proves
the goal and remains a visual editor: put the cursor on `origami saved` to
restore the drawing and history, even after restarting Lean. Use Undo and new
operations to revise it, then Submit and Save construction again. Unsaved GUI
changes do not change the saved proof. You can fold the source block in VS Code.

## A first construction: one half

Start from `example : LeanOrigami.ConstructibleNumber (1 / 2 : ℝ) := by origami`
in a scratch file importing the widget. An unfinished-goal diagnostic is
expected until submission.

1. Axiom 1, points 0 and 1: preview and use the x-axis, object 2.
2. Axiom 2, points 0 and 1: preview and use the perpendicular bisector,
   object 3.
3. Intersect lines 2 and 3: object 4 is `(1/2, 0)`.
4. Submit point 4's x coordinate, then click **Save construction**.
5. Save, close, and reopen the file. The proof checks without a panel; placing the cursor on `origami saved` reopens it.

Before insertion, submitting point 1's x coordinate should fail: 1 is
constructible, but it is not the goal 1/2.

## Square root of two

Start a goal about `Real.sqrt 2` and make these selections:

1. Axiom 1 through points 0 and 1 gives the x-axis (2).
2. Axiom 4 through point 0, perpendicular to line 2 gives the y-axis (3).
3. Axiom 4 through point 1, perpendicular to line 2 gives `x = 1` (4).
4. Axiom 5 sends point 1 to line 3 while fixing point 0. Choose the crease
   rising to the right, `y = x` (5).
5. Intersect lines 4 and 5 to obtain `(1, 1)` (6).
6. Axiom 5 sends point 6 to line 2 while fixing point 0. Choose the crease
   whose reflected point lands on the positive x-axis (the shallower positive
   slope, about 0.4142). It becomes line 7.
7. Axiom 4 through point 6, perpendicular to line 7 gives line 8.
8. Intersect lines 8 and 2 to obtain `(√2, 0)` (9).
9. Submit point 9's x coordinate and save the construction.

The final check proves the square equation and the nonnegative branch. A
negative square root cannot close this goal.

## Cube root and trisection checks

For a cube-root goal, use `(2 : ℝ) ^ (1 / (3 : ℝ))`. First perform steps 1–5
of the square-root tutorial, then make the horizontal through point 6
(perpendicular to line 3), giving line 7; intersect lines 3 and 7 to get
point 8 at `(0,1)`.

Continue with these operations, committing each fold before continuing:

| New object | Operation | Inputs / branch |
| --- | --- | --- |
| 9 | Axiom 5 | point 1 onto line 3, fixing point 0; choose `y=-x` |
| 10 | Intersection | lines 4 and 9 |
| 11 | Axiom 4 | point 10, perpendicular to line 3 |
| 12 | Intersection | lines 7 and 9 |
| 13 | Axiom 4 | point 6, perpendicular to line 5 |
| 14 | Intersection | lines 13 and 2 |
| 15 | Axiom 4 | point 14, perpendicular to line 2 |
| 16 | Axiom 4 | point 12, perpendicular to line 9 |
| 17 | Intersection | lines 16 and 2 |
| 18 | Axiom 6 | points 8 and 17 onto lines 11 and 15, respectively |
| 19 | Axiom 4 | point 0, perpendicular to line 18 |
| 20 | Axiom 4 | point 0, perpendicular to line 19 |
| 21 | Intersection | lines 20 and 4 |

Submit the **y coordinate** of point 21. The selected cubic crease has slope
`∛2`; the final two folds transfer that slope to the vertical coordinate at
`x=1`.

For a three-branch trisection preview, start again and follow the same steps
through object 12. Instead of the cube-root suffix, make line 13 through
point 12 perpendicular to line 2; make line 14 through point 10 perpendicular
to line 9; intersect these at point 15, `(-1,-3)`. Preview axiom 6 sending
points 8 and 15 to lines 11 and 4. Its three crease slopes solve
`t³-3t-1=0`; the largest is `2*cos(π/9)`. Inspect and select each branch by
its preview number. This is an inspection check; matching a cosine goal is
outside the initial named-target matcher.

## Supported goals and limits

The initial goal matcher supports rational expressions, `Real.sqrt q` for
nonnegative rational q, and `q ^ (1 / (3 : ℝ))` for nonnegative rational q.
Reducible names for these expressions are supported. Other target expressions
are rejected explicitly; numerical proximity never closes a goal. This scope
can later be extended with more root-identification theorems.

The panel uses the existing seven-axiom solver. Inputs admitting infinitely
many folds are rejected, rather than represented as an arbitrary finite list.
Canonical exact arithmetic and certificate preparation can still take time for
large interacting algebraic fields. Undo remains available while waiting.

## Code map and trust boundary

- `Widget/Session.lean`: exact state changes, input validation, display views.
- `Widget/Goal.lean`: real target identification and square-root sign evidence.
- `Widget/Saved.lean`: persistent program/certificate, soundness, and display loading.
- `Widget.lean`: RPC snapshots, original-goal proof checking, versioned edits.
- `widget/construction.js`: rendering and user actions; no proof authority.
- `Text/Exact.lean`: shared standalone/local certificate serialization.
- `scripts/widget-construction-test.mjs`: rendering and event-wiring tests
  using a small React/editor adapter. These are not live infoview tests.

Native computation proposes choices and prepares certificates. Lean's kernel
checks the saved mathematical proof. The display can be inaccurate without
changing the exact construction. A JSON response or a successful native check
is not itself a proof.
