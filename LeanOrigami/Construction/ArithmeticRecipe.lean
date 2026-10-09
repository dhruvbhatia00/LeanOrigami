import LeanOrigami.Construction.Recipe
import LeanOrigami.Construction.Arithmetic

/-!
# Executable arithmetic recipes

Arithmetic arguments, in local order, are the origin, horizontal unit point,
x-axis, y-axis, vertical unit point, and the two operands placed on the x-axis.
The scalar arguments name saved coordinates; replay checks those claims against
the referenced objects. The builder assigns intermediate references, and recipe
expansion relocates them before the ordinary checker executes the program.
-/

namespace LeanOrigami.ArithmeticRecipe
variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Typed external references for every binary arithmetic recipe. -/
structure Arguments where
  origin : PointRef
  unit : PointRef
  xAxis : LineRef
  yAxis : LineRef
  unitY : PointRef
  first : PointRef
  second : PointRef

/-- Supply the seven local argument slots without erasing their input roles
from the public argument record. Replay still checks each actual object kind. -/
def Arguments.indices (args : Arguments) : Fin 7 → Nat :=
  fun i => match i.val with
  | 0 => args.origin.index
  | 1 => args.unit.index
  | 2 => args.xAxis.index
  | 3 => args.yAxis.index
  | 4 => args.unitY.index
  | 5 => args.first.index
  | _ => args.second.index

private def diagonal : RecipeBuilder K LineRef :=
  RecipeBuilder.fold (.axiom5 ⟨1⟩ ⟨0⟩ ⟨3⟩) (Line.chart (-1) 0)

private def atHeight (point : PointRef) (x y : K) (horizontal : LineRef) :
    RecipeBuilder K PointRef := do
  let vertical ← RecipeBuilder.fold (.axiom4 point ⟨2⟩) (Line.chart 0 x)
  RecipeBuilder.intersect vertical horizontal (x, y)

private def level (point : PointRef) (x : K) (diagonal : LineRef) :
    RecipeBuilder K LineRef := do
  let sameCoordinates ← atHeight point x x diagonal
  RecipeBuilder.fold (.axiom4 sameCoordinates ⟨3⟩) (Line.horizontal x)

private def project (point : PointRef) (x : K) : RecipeBuilder K PointRef := do
  let vertical ← RecipeBuilder.fold (.axiom4 point ⟨2⟩) (Line.chart 0 x)
  RecipeBuilder.intersect vertical ⟨2⟩ (x, 0)

/-- Add two signed axis coordinates by translating a line and taking its intercept.
The geometric construction is proved in `ConstructibleNumber.add`. -/
def add (x y : K) : Recipe K 7 := RecipeBuilder.build 7 do
  let horizontalOne ← RecipeBuilder.fold (.axiom4 ⟨4⟩ ⟨3⟩) (Line.horizontal 1)
  let lifted ← atHeight ⟨5⟩ x 1 horizontalOne
  let base := Line.chart y y
  let original ← RecipeBuilder.fold (.axiom1 ⟨4⟩ ⟨6⟩) base
  let perpendicular ← RecipeBuilder.fold (.axiom4 lifted original)
    (Line.perpendicularThrough (x, 1) base)
  let translated ← RecipeBuilder.fold (.axiom4 lifted perpendicular) (Line.chart y (x+y))
  RecipeBuilder.intersect translated ⟨2⟩ (x+y, 0)

/-- Subtract two signed axis coordinates, including equal or zero operands. -/
def sub (x y : K) : Recipe K 7 := RecipeBuilder.build 7 do
  let horizontalOne ← RecipeBuilder.fold (.axiom4 ⟨4⟩ ⟨3⟩) (Line.horizontal 1)
  let liftedX ← atHeight ⟨5⟩ x 1 horizontalOne
  let liftedY ← atHeight ⟨6⟩ y 1 horizontalOne
  let base := Line.chart (-y) 0
  let original ← RecipeBuilder.fold (.axiom1 ⟨0⟩ liftedY) base
  let perpendicular ← RecipeBuilder.fold (.axiom4 liftedX original)
    (Line.perpendicularThrough (x, 1) base)
  let translated ← RecipeBuilder.fold (.axiom4 liftedX perpendicular) (Line.chart (-y) (x-y))
  RecipeBuilder.intersect translated ⟨2⟩ (x-y, 0)

/-- Multiply using the line through the origin and `(x,1)`, at height `y`. -/
def mul (x y : K) : Recipe K 7 := RecipeBuilder.build 7 do
  let horizontalOne ← RecipeBuilder.fold (.axiom4 ⟨4⟩ ⟨3⟩) (Line.horizontal 1)
  let liftedX ← atHeight ⟨5⟩ x 1 horizontalOne
  let diagonal ← diagonal
  let horizontalY ← level ⟨6⟩ y diagonal
  let ray ← RecipeBuilder.fold (.axiom1 ⟨0⟩ liftedX) (Line.chart (-x) 0)
  let product ← RecipeBuilder.intersect ray horizontalY (x*y, y)
  project product (x*y)

/-- Divide using the line through the origin and `(1,y)`, at height `x`.
The proof argument prevents asking this recipe to divide by zero. -/
def div (x y : K) (_hne : y ≠ 0) : Recipe K 7 := RecipeBuilder.build 7 do
  let diagonal ← diagonal
  let horizontalY ← level ⟨6⟩ y diagonal
  let liftedUnit ← atHeight ⟨1⟩ 1 y horizontalY
  let horizontalX ← level ⟨5⟩ x diagonal
  let ray ← RecipeBuilder.fold (.axiom1 ⟨0⟩ liftedUnit) (Line.chart (-1/y) 0)
  let quotient ← RecipeBuilder.intersect ray horizontalX (x/y, x)
  project quotient (x/y)

/-- Place either coordinate of a known point on the x-axis. Local arguments
are the source point, origin, horizontal unit point, x-axis, and y-axis. -/
def place (p : Point K) (coordinate : Coordinate) : Recipe K 5 := RecipeBuilder.build 5 do
  match coordinate with
  | .x =>
      let vertical ← RecipeBuilder.fold (.axiom4 ⟨0⟩ ⟨3⟩) (Line.chart 0 p.1)
      RecipeBuilder.intersect vertical ⟨3⟩ (p.1, 0)
  | .y =>
      let diagonal ← RecipeBuilder.fold (.axiom5 ⟨2⟩ ⟨1⟩ ⟨4⟩) (Line.chart (-1) 0)
      let horizontal ← RecipeBuilder.fold (.axiom4 ⟨0⟩ ⟨4⟩) (Line.horizontal p.2)
      let sameCoordinates ← RecipeBuilder.intersect diagonal horizontal (p.2, p.2)
      let vertical ← RecipeBuilder.fold (.axiom4 sameCoordinates ⟨3⟩) (Line.chart 0 p.2)
      RecipeBuilder.intersect vertical ⟨3⟩ (p.2, 0)

/-- Combine two constructed axis coordinates into a point. The seven arguments
are the same basis and two operands as for binary arithmetic. -/
def pair (x y : K) : Recipe K 7 := RecipeBuilder.build 7 do
  let diagonal ← diagonal
  let horizontalY ← level ⟨6⟩ y diagonal
  atHeight ⟨5⟩ x y horizontalY

end LeanOrigami.ArithmeticRecipe
