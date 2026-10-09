# Text constructions and saved proofs

Import `LeanOrigami.Text`. This is a separate entry point from the native Hex
solver: opening a symbolic proof does not require loading Hex.

An `origami` block starts with named seed points, creates points, lines, or
numbers, and finishes by submitting a number against the theorem's target:

```lean
import LeanOrigami.Text
open LeanOrigami

example : ConstructibleNumber (Real.sqrt 2) := by
  origami
    point U := unit
    number one := x U
    number two := add one one
    number root := sqrt two choose (Real.sqrt 2) proving (by
      origami_values
      constructor
      · positivity
      · norm_num)
    submit root
```

`choose` records an exact expression, never a position in a solver's result
list. The square-root certificate checks both its equation and its sign.
A polynomial equation alone does not identify a particular conjugate.
Expressions such as `Real.sqrt 2`, a specified real power, and an explicitly
characterized algebraic root remain exact when saved as Lean source.

## Commands

| Command after `:=` | Result and required arguments |
| --- | --- |
| `origin`, `unit` | Seed point `(0,0)` or `(1,0)`. |
| `fold1 p q`, `fold2 p q` | Line, with a selected crease. |
| `fold3 l m` | Line, with a selected bisector. |
| `fold4 p l` | Line, perpendicular to `l` through `p`. |
| `fold5 p q l` | Line reflecting `p` onto `l` through `q`. |
| `fold6 p q l m` | Line reflecting `p` onto `l` and `q` onto `m`. |
| `fold7 p l m` | Line reflecting `p` onto `l`, perpendicular to `m`. |
| `intersect l m` | Point, with a selected intersection. |
| `x p`, `y p` | Number selected from a constructed point. |
| `pair a b` | Point with the two constructed coordinates. |
| `add a b`, `sub a b`, `mul a b`, `div a b` | Number; division requires a nonzero divisor. |
| `sqrt a` | Selected nonnegative square root. |
| `quadratic a b c` | Selected root of `a*t²+b*t+c`; `a ≠ 0`. |
| `cubic a b c d` | Selected root of `a*t³+b*t²+c*t+d`; `a ≠ 0`. |
| `use (expression)` | Invoke a reusable construction returning the declared object kind. |

Use `point name`, `line name`, or `number name` before `:=` as appropriate.
Folds, intersections, and roots require `choose (exactExpression)`.
They accept an optional `proving (by ...)` certificate; division accepts an
optional certificate for its nonzero divisor. With no explicit certificate,
`origami_check` tries symbolic simplification and elementary arithmetic.
Names refer only to existing objects, cannot be redeclared, and retain their
point/line/number types. Errors point to the responsible instruction. Every
instruction is checked, including instructions whose outputs are unused.
Unfinished certificates and dependencies on unapproved axioms are rejected.

For example:

```lean
line axis := fold1 O U choose (LeanOrigami.Line.horizontal 0)
line vertical := fold4 O axis choose (LeanOrigami.Line.chart 0 0)
```

A chart line has equation `x + b*y = c`; `horizontal c` has equation `y = c`.
All selected folds must be finite-choice requests. Merely exhibiting a line
satisfying an underconstrained rule is insufficient.

`submit n` proves the current `ConstructibleNumber target` goal after checking
`n.value = target`. An explicit `proving` certificate can identify a target
through a nontrivial equality. `finish n` instead returns a certified object,
for use when defining a reusable construction:

```lean
def twice (a : LeanOrigami.Text.Number) : LeanOrigami.Text.Number := by
  origami
    number result := add a a
    finish result
```

Call it with `number two := use (twice one)`. A helper's value lemmas or its
definition may need to be supplied to `simp` in subsequent certificates.
`origami_values` unfolds the standard operations and local saved values;
it does not automatically unfold every user-defined helper.

## Saving and reopening

After closing namespaces and sections, capture a checked, closed theorem:

```lean
origami_artifact MyNamespace.myTheorem as savedConstruction
```

The resulting `LeanOrigami.Text.Artifact` contains a format version, the
fully qualified theorem name, and the exact source prefix preceding this
command. The prefix retains imports, notation, helper definitions, and all
chosen expressions and certificates. It may include other preceding proofs;
this is deliberately a source artifact, not a minimal dependency extractor.

- `artifact.encode` and `Artifact.decode` serialize and deserialize JSON.
- `artifact.save path` and `Artifact.load path` handle files.
- `artifact.writeLean path` writes a replayable `.lean` file and appends a
  check of its named theorem and transitive axioms.

Loading JSON handles data only. Run Lean on the emitted source to verify the
proof. This is also how the validation script tests reopening: it writes an
artifact, reads it back, compares the exact source, and checks the emitted
file in a fresh Lean process. No GUI session or native success flag is needed.

## Proof and execution paths

The text commands use `Text.Point`, `Text.Line`, and `Text.Number`. These
carry exact real values and geometric construction histories. Each primitive
checks its actual selected output. Arithmetic and root commands apply the
proved construction algorithms to the supplied input histories.

The existing `Program Scalar` and `Scalar.folds` APIs remain the executable
path for numerical exploration and candidate discovery. A native solver can
suggest a value, but the saved text proof needs an exact expression and checked
certificate for that choice. This interface does not automatically translate
an arbitrary opaque Hex value into a short symbolic proof. Difficult algebraic
identities may require explicit proof arguments. Neither native execution nor
JSON decoding is used as evidence for a theorem.

Open `LeanOrigamiDemos/Text.lean` for square root, cube doubling, an iterated
root, a reusable construction, and the complete trisection point. Open
`LeanOrigamiTests/Text.lean` for all seven primitives and rejection examples.
