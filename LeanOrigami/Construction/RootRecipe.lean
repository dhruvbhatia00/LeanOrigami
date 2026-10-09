import LeanOrigami.Construction.ArithmeticRecipe
import LeanOrigami.Construction.RootGeometry

/-!
# Executable root constructions

Arguments begin with the origin, horizontal unit, x-axis, y-axis, and vertical
unit, followed by coefficient points on the x-axis. Roots name selected
outputs only; replay checks every step and rejects an incorrect root choice.
Nested arithmetic recipes construct the input configuration from coefficients.
-/

namespace LeanOrigami.RootRecipe
variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- References for the basis shared by root and arithmetic recipes. -/
structure BasisArguments where
  origin : PointRef
  unit : PointRef
  xAxis : LineRef
  yAxis : LineRef
  unitY : PointRef

/-- Assign the five basis slots followed by the supplied coefficient slots. -/
def BasisArguments.indices {n : Nat} (basis : BasisArguments) (coefficients : Fin n → PointRef) :
    Fin (5+n) → Nat := fun i =>
  if h : i.val < 5 then
    match i.val with
    | 0 => basis.origin.index
    | 1 => basis.unit.index
    | 2 => basis.xAxis.index
    | 3 => basis.yAxis.index
    | _ => basis.unitY.index
  else (coefficients ⟨i.val-5, by omega⟩).index

private def arithmetic (first second : PointRef) : Fin 7 → Nat :=
  (ArithmeticRecipe.Arguments.mk ⟨0⟩ ⟨1⟩ ⟨2⟩ ⟨3⟩ ⟨4⟩ first second).indices

private def subtract (x y : K) (first second : PointRef) : RecipeBuilder K PointRef :=
  RecipeBuilder.use (ArithmeticRecipe.sub x y) (arithmetic first second)

private def coordinate (p : Point K) (ref : PointRef) : RecipeBuilder K PointRef :=
  RecipeBuilder.use (ArithmeticRecipe.place p .y) (fun i =>
    match i.val with | 0 => ref.index | 1 => 0 | 2 => 1 | 3 => 2 | _ => 3)

/-- Construct a selected root of `t³+a*t²+b*t+c`. External coefficient
arguments are `(a,0)`, `(b,0)`, `(c,0)`, in that order. -/
def monicCubic (a b c t : K) : Recipe K 8 := RecipeBuilder.build 8 do
  let minusOne ← subtract 0 1 ⟨0⟩ ⟨1⟩
  -- Transfer an axis coordinate to a horizontal level through the constructed diagonal.
  let diagonal ← RecipeBuilder.fold (.axiom5 ⟨1⟩ ⟨0⟩ ⟨3⟩) (Line.chart (-1) 0)
  let minusVertical ← RecipeBuilder.fold (.axiom4 minusOne ⟨2⟩) (Line.chart 0 (-1))
  let minusDiagonal ← RecipeBuilder.intersect minusVertical diagonal (-1, -1)
  let firstTarget ← RecipeBuilder.fold (.axiom4 minusDiagonal ⟨3⟩) (Line.horizontal (-1))
  let difference ← subtract c a ⟨7⟩ ⟨5⟩
  let bVertical ← RecipeBuilder.fold (.axiom4 ⟨6⟩ ⟨2⟩) (Line.chart 0 b)
  let bDiagonal ← RecipeBuilder.intersect bVertical diagonal (b, b)
  let bHorizontal ← RecipeBuilder.fold (.axiom4 bDiagonal ⟨3⟩) (Line.horizontal b)
  let differenceVertical ← RecipeBuilder.fold (.axiom4 difference ⟨2⟩) (Line.chart 0 (c-a))
  let source ← RecipeBuilder.intersect differenceVertical bHorizontal (c-a, b)
  let negativeA ← subtract 0 a ⟨0⟩ ⟨5⟩
  let offset ← subtract (-a) c negativeA ⟨7⟩
  let secondTarget ← RecipeBuilder.fold (.axiom4 offset ⟨2⟩) (Line.chart 0 (-a-c))
  let selected ← RecipeBuilder.fold (.axiom6 ⟨4⟩ source firstTarget secondTarget)
    (RootGeometry.crease t)
  let atZero ← RecipeBuilder.intersect selected ⟨3⟩ (0, -t^2)
  let unitVertical ← RecipeBuilder.fold (.axiom4 ⟨1⟩ ⟨2⟩) (Line.chart 0 1)
  let atOne ← RecipeBuilder.intersect selected unitVertical (1, t-t^2)
  let first ← coordinate (0, -t^2) atZero
  let second ← coordinate (1, t-t^2) atOne
  subtract (t-t^2) (-t^2) second first

/-- Normalize a nonmonic cubic using constructed divisions. Coefficients
are supplied in descending order, and the leading coefficient must be nonzero. -/
def cubic (a b c d t : K) (hne : a ≠ 0) : Recipe K 9 := RecipeBuilder.build 9 do
  let quadratic ← RecipeBuilder.use (ArithmeticRecipe.div b a hne) (arithmetic ⟨6⟩ ⟨5⟩)
  let linear ← RecipeBuilder.use (ArithmeticRecipe.div c a hne) (arithmetic ⟨7⟩ ⟨5⟩)
  let constant ← RecipeBuilder.use (ArithmeticRecipe.div d a hne) (arithmetic ⟨8⟩ ⟨5⟩)
  RecipeBuilder.use (monicCubic (b/a) (c/a) (d/a) t) (fun i =>
    match i.val with
    | 5 => quadratic.index | 6 => linear.index | 7 => constant.index | n => n)

/-- Solve a quadratic by constructing a root of its product with the variable.
The caller supplies the selected root; the separate polynomial check below
rejects the added zero root when it is not a root of the original quadratic. -/
def quadratic (a b c t : K) (hne : a ≠ 0) : Option (Recipe K 8) :=
  if a*t^2+b*t+c = 0 then some (RecipeBuilder.build 8 do
    let linear ← RecipeBuilder.use (ArithmeticRecipe.div b a hne) (arithmetic ⟨6⟩ ⟨5⟩)
    let constant ← RecipeBuilder.use (ArithmeticRecipe.div c a hne) (arithmetic ⟨7⟩ ⟨5⟩)
    RecipeBuilder.use (monicCubic (b/a) (c/a) 0 t) (fun i =>
      match i.val with | 5 => linear.index | 6 => constant.index | 7 => 0 | n => n))
  else none

/-- Construct the nonnegative square-root branch. The scalar arguments are
checked exactly; an incorrect or negative selected root produces no recipe. -/
def squareRoot (a t : K) : Option (Recipe K 6) :=
  if 0 ≤ t ∧ t^2 = a then some (RecipeBuilder.build 6 do
    let negative ← subtract 0 a ⟨0⟩ ⟨5⟩
    RecipeBuilder.use (monicCubic 0 (-a) 0 t) (fun i =>
      match i.val with | 5 => 0 | 6 => negative.index | 7 => 0 | n => n))
  else none

end LeanOrigami.RootRecipe
