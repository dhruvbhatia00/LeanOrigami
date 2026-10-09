# Text constructions and saved proofs

A construction has two parts: a saved `Program` and a proof that this program
passes the checker. Building or editing the program does not construct proofs.
A future GUI can run exact computations to preview the available choices and
record the user's selection. At submission, Lean checks a proof about that
same saved program.

## Writing a construction

Use the existing `RecipeBuilder` with ordinary Lean `do` notation. Local names
hold point or line references; folds and intersections record exact selected
outputs. The builder assigns indices, so callers do not count intermediate
objects by hand.

```lean
import LeanOrigami.Text
open LeanOrigami

def midpoint : Recipe ℚ 2 := RecipeBuilder.build 2 do
  let origin : PointRef := ⟨0⟩
  let unit : PointRef := ⟨1⟩
  let axis ← RecipeBuilder.fold (.axiom1 origin unit) (Line.horizontal 0)
  let crease ← RecipeBuilder.fold (.axiom2 origin unit) (Line.chart 0 (1/2))
  RecipeBuilder.intersect axis crease (1/2, 0)
```

Certify and submit it separately:

```lean
theorem midpoint_accepts :
    Program.accepts midpoint.steps midpoint.output .x (1/2) = true := by
  origami_check

theorem midpoint_constructible : ConstructibleNumber (1/2 : ℝ) := by
  simpa using Program.accepts_sound (Rat.castHom ℝ) _ _ .x _ midpoint_accepts
```

`midpoint.steps` is the ordinary program, and `midpoint.output` is its result
reference. Its two argument slots are the two seeds when replayed on their own.
For reuse inside a larger construction, `RecipeBuilder.use recipe arguments`
expands the recipe and relocates its references. Arithmetic and root recipes
use exactly this mechanism; they do not introduce additional trusted rules.

`RecipeBuilder.fold` accepts all seven `FoldRequest` constructors, each taking
the appropriate point and line references. `RecipeBuilder.intersect` takes
two line references. A chart line has equation `x + b*y = c`, while
`Line.horizontal c` has equation `y = c`.

Typed references catch ordinary point/line mix-ups while writing Lean. A manually
forged reference can still name an absent object or the wrong object kind;
the checker rejects those cases. Normal Lean scope and binding rules apply.

## Previewing and certifying

`Program.run` computes the objects or an error. `Program.accepts` also checks
the submitted reference, coordinate, and exact target. Over `Scalar`, these
operations use Hex's executable algebraic numbers. Previewing need not generate
proofs and does not become evidence merely because it returned `true`.

`origami_check` proves an actual `Program.accepts ... = true` goal. It resolves
the saved references, checks every instruction (including unused ones), and
proves each geometric condition using the checker's step lemmas. It then checks
the final target. `Program.accepts_sound` converts this acceptance proof into
constructibility under a field embedding into the reals.

The tactic performs structural computation for references and uses algebraic
proofs for coordinates. It does not ask the kernel to execute Hex's entire
algorithm. `origami_check using ...` supplies a tactic for the geometric goals
and target equality when elementary arithmetic is insufficient. These proofs
must concern the exact saved choices; proving that some root exists is not
enough. Failures identify the primitive instruction or final submission.
Error messages number instructions from one; object references still start at zero.

`LeanOrigamiDemos/Text.lean` demonstrates symbolic root certificates over any
ordered field. `LeanOrigamiTests/TextScalar.lean` instantiates one at a concrete,
executable Hex square root and proves its interpretation is `Real.sqrt 2`.
`LeanOrigamiTests/RootInterpreter.lean` executes that same candidate and program.

This is not automatic discovery of a construction, nor automatic extraction of
a short certificate from every opaque Hex value. Difficult choices can require
explicit algebraic facts. All generated proof terms are checked by Lean's kernel.

## Choices and reusable roots

Saved choices are exact values, not positions in a solver's candidate list.
Reordering candidates therefore does not change a construction that selects
the same value. Algebraic root equations may need sign or interval information
to identify the intended root.

`RootRecipe.quadratic` rejects candidates that fail the original quadratic
(including an extraneous zero root of its cubic encoding).
`RootRecipe.squareRoot` checks both the equation and the nonnegative branch.
These constructors return `Option`; handle failure before using a recipe.
Division and nonmonic root recipes require nonzero leading coefficients.
Expanded primitive steps still undergo ordinary replay.

## Saving and reopening

After closing namespaces and sections, capture a checked, closed theorem:

```lean
origami_artifact MyNamespace.myTheorem as savedConstruction
```

The artifact stores a format version, theorem name, and exact source prefix.
That prefix includes the saved programs, selected expressions, helper recipes,
acceptance proofs, and final theorem. It preserves source context rather than
extracting a minimal dependency bundle; imports require the pinned project.

- `artifact.encode` and `Artifact.decode` handle JSON.
- `artifact.save path` and `Artifact.load path` handle files.
- `artifact.writeLean path` writes source for fresh kernel-checked replay.

Loading JSON is data handling, not proof checking. Run Lean on the emitted file
to verify the result. The validation script round-trips exact source and checks
the exported theorem and its transitive axioms in a fresh Lean process.
