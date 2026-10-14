# Reusable visual recipes

For a saved example, open `LeanOrigamiDemos/Recipes.lean`. Place the cursor
on `origami_recipe midpoint` to view/edit the recipe, or on `origami history`
in `half` to inspect the proof made by calling it. Both were created through
the widget.

For an empty starter, open `LeanOrigamiDemos/RecipeSetup.lean`, or type a complete
bare command after importing the widget:

```lean
import LeanOrigami.Widget

origami_recipe
```

Place the cursor on `origami_recipe`. The setup screen asks for a recipe name
and named point/line inputs. Add inputs, place them on the canvas, or enter exact
integers and fractions. Point placement uses one click; line placement uses two
distinct grid points. Those two clicks define one line input, not two extra
parameters. Line equations use `a*x + b*y = c` with a nonzero normal.
Click **Start construction** to open the folding controls.

The older explicit syntax remains available:

```lean
open LeanOrigami LeanOrigami.Widget
origami_recipe myMidpoint samples
  ([("A", .point (0, 0)), ("B", .point (1, 0))])
```

Inputs are parameters; their coordinates are sample values for editing. They
are not added to the permitted seed objects of a proof. Existing exact algebraic
samples are preserved. If their coordinate fields are blank, enter every
coordinate to replace the input with a rational one; the approximate hover text
is never used as an exact replacement.

For a midpoint, join A to B (axiom 1), bisect them (axiom 2), then intersect the
two creases. Choose that point under **Recipe output**, click **Prepare recipe**,
then **Save recipe**. Lean writes a `saved` template into the same command.
The command remains editable. A recipe may also return a line. If edits elsewhere
in the file leave an older panel reporting “The source changed,” use Lean’s
**Restart File** and place the cursor on the command again.

Later commands and proofs in the file see the recipe in the operation menu.
Imported recipe declarations are available too. Select **Recipe · myMidpoint**,
fill its named inputs, and click **Run recipe**. A built-in midpoint recipe is
also available. Recipes can call earlier recipes: the operations are expanded,
with nested groups preserved for inspection. Editing an earlier recipe does
not silently change the already expanded steps of a saved caller.

Unique operations run automatically. When there is more than one fold, the
recipe pauses for a choice using the current inputs. The old sample's branch
number is never reused. For an ordinary recipe call, **Cancel recipe** or **Undo** removes the unfinished
call; undoing a completed call removes that whole group. If an operation fails,
the previous snapshot remains available and cancellation returns to the state
before the call. References to absent objects, wrong input kinds, and geometric
degeneracies produce errors.

**Edit samples** lets you explore the same instructions on new inputs, while
building or after reopening a saved recipe. Drag a sample point, use **Place**
to reposition a point/line, or enter fractions and click **Apply samples**.
Dragging shows tentative placement and runs exact replay on release. Input
names, kinds, and order remain fixed after setup so references retain their
meaning. Finish applying or resetting edits before leaving sample-editing mode.

Replay asks again at ambiguous folds. If a step fails, the history identifies
it and only the valid prefix remains visible. The complete instructions are
retained: edit the samples again or click **Reset samples** to recover. Reset
restores the saved example, or the initial setup values for an unsaved recipe.
An incomplete replay cannot overwrite the saved recipe. Saving a completed
construction keeps the current exact samples as its next saved example.

Hover or focus the recipe's entry in **Construction history** to see its
inputs and result. Expand it to inspect its primitive steps. Hover or focus a step to highlight
inputs and output. These groups remain available after saving and reopening a proof.

A saved recipe describes how to construct an output; it does not assert a
universal specification such as “this output is always the midpoint.” During a
proof, its expanded exact program is certified through the ordinary checker.
A general theorem about a user recipe's meaning is separate work. Recipes can
also have input restrictions: the built-in midpoint construction needs distinct
points because its first two folds require them.

Current recipes are finite sequences, with fresh interactive branch choices.
There are no conditional alternatives or predicate-based automatic branch
selectors yet. Arithmetic, root, projection, and coordinate-transfer recipes can
be added through this interface; the initial demonstration is midpoint.

## Code map and validation

- `LeanOrigami/Widget/Recipe.lean`: typed templates, reference validation,
  serialization, and the built-in midpoint sequence.
- `LeanOrigami/Widget/Session.lean`: exact execution, branch continuations,
  rollback, recording, and history groups.
- `LeanOrigami/Widget/Workspace.lean`: exact sample setup/replacement, retained
  preview/reset state, and the registry of named recipes. Its native evaluation serves exploration only.
- `LeanOrigami/Widget.lean`: the standalone command, proof tactic, and shared
  versioned RPC interface.
- `widget/construction.js`: the shared canvas and recipe controls.

The older `Construction/Recipe.lean` describes concrete programs with selected
exact outputs. Visual templates instead omit these outputs and rediscover them
when instantiated. They reuse its reference-renaming operations.

Focused validation (also included in `scripts/validate.sh`):

```sh
LEAN_NUM_THREADS=1 lake build LeanOrigami.Widget LeanOrigamiDemos.Recipes
node --experimental-vm-modules scripts/widget-construction-test.mjs
lake lean LeanOrigamiTests/RecipeRuntime.lean -- --run LeanOrigamiTests/RecipeRuntime.lean
lake lean .lake/recipes/Replay.lean
lake lean LeanOrigamiTests/SampleWorkspace.lean -- --run LeanOrigamiTests/SampleWorkspace.lean
```

`RecipeRuntime.lean` contains serialization checks and executable regressions.
Its generated `Replay.lean` checks both the saved recipe command and a grouped
proof, and prints the proof's transitive axiom dependencies.

## Declaring input requirements

After setting up samples, open **Requirements**. Choose a geometry condition
and its named inputs, then click **Add requirement**. Each entry reports whether
it holds on the currently applied exact samples. It is an author-declared
requirement, not a proof that the recipe computes its advertised result.
Changing samples rechecks requirements before replaying the affected steps.
If a requirement fails, change the samples or remove/change the requirement;
the saved instruction sequence is retained for recovery.

The initial families cover equal/distinct points or lines, incidence on a line
or either axis, collinearity, parallelism, perpendicularity, coordinate bounds,
and polynomial comparisons. Parallel includes coincident lines; collinear
includes repeated points. Add a distinctness requirement when needed. Lines
always have a nonzero normal and canonical coefficients.

Coordinate comparisons accept integers and fractions. To require a positive
coordinate, choose **Coordinate > value** and enter `0`. Polynomial comparisons
use one selected coordinate `t` and a comma-separated list of rational
coefficients, constant first: `-2, 0, 1` means `t² - 2`. The form permits up to
32 coefficients. The underlying Lean condition language also supports sums and
products involving multiple coordinates and canonical line coefficients.
It does not accept arbitrary Lean expressions, division by coordinate values,
or trigonometric functions.

All listed requirements must hold. AND, OR, and NOT replace the selected entries
with their combination. Nested recipe requirements are shown separately and
cannot be removed from the calling recipe independently of the call. They are
checked at the appropriate step during replay, including after saving and
reopening. The recipe menu also lists a recipe's input requirements.

For API users, `RecipeTemplate.requirements` contains input conditions;
`RecipeTemplate.checks` preserves conditions inherited from expanded calls,
with their check boundary and owning call. Ordinary templates without these
fields keep working. `Construction/Condition.lean` contains the mathematical
interpretation and exact checker; `Widget/Requirements.lean` contains the form
translation and readable/source serialization. `Condition.checkObjects_map_iff`
connects the executable decision to geometry after an ordered field embedding,
including `Scalar.realHom` into Mathlib's real numbers.

New sample inputs receive the first unused point name (`A`, `B`, …) or line name
(`ℓ₁`, `ℓ₂`, …). You may rename them before starting the construction. Hover over
or focus **Reset view** or **Refine display** for an explanation: the former
resets the camera; the latter improves drawing approximations without changing
any exact object or proof.

A ready-to-open example is `LeanOrigamiDemos/Requirements.lean`: place the
cursor on the first `origami_recipe` command to inspect the axis-midpoint
requirements, or on the bare command near the end to create a new draft.
