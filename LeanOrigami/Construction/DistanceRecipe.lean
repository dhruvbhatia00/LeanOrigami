import LeanOrigami.Construction.RootOperation

/-!
# Distance transferred to an axis

The construction subtracts coordinates, squares and adds them, then takes the
nonnegative square root. Coincident inputs require no exceptional construction.
The input frame is explicit; a proposed distance is never an additional seed.
-/

namespace LeanOrigami.DistanceRecipe
variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Squared Euclidean distance, expressed using field arithmetic alone. -/
def squared (p q : Point K) : K := (p.1 - q.1)^2 + (p.2 - q.2)^2

/-- The nonnegative distance on the selected coordinate axis. -/
def value (axis : Coordinate) (d : K) : Point K :=
  match axis with | .x => (d, 0) | .y => (0, d)

/-- Both arbitrary points follow the five standard frame objects. -/
def inputs (p q : Point K) : Program.State K := CoordinateOperation.inputs p ++ [.point q]

private def unary (p : PointRef) : Fin 6 → Nat :=
  fun i => if i.val == 5 then p.index else i.val

private def binary (p q : PointRef) : Fin 7 → Nat :=
  (ArithmeticRecipe.Arguments.mk ⟨0⟩ ⟨1⟩ ⟨2⟩ ⟨3⟩ ⟨4⟩ p q).indices

/-- Coordinate arithmetic followed by the ordinary square-root fold recipe. -/
def recipe (axis : Coordinate) (p q : Point K) (d : K) : Recipe K 7 :=
  RecipeBuilder.build 7 do
    let px ← RecipeBuilder.use (CoordinateOperation.recipe .projectX p) (unary ⟨5⟩)
    let qx ← RecipeBuilder.use (CoordinateOperation.recipe .projectX q) (unary ⟨6⟩)
    let py ← RecipeBuilder.use (CoordinateOperation.recipe .transferY p) (unary ⟨5⟩)
    let qy ← RecipeBuilder.use (CoordinateOperation.recipe .transferY q) (unary ⟨6⟩)
    let dx ← RecipeBuilder.use (ArithmeticRecipe.sub p.1 q.1) (binary px qx)
    let dy ← RecipeBuilder.use (ArithmeticRecipe.sub p.2 q.2) (binary py qy)
    let xx ← RecipeBuilder.use (ArithmeticRecipe.mul (p.1-q.1) (p.1-q.1)) (binary dx dx)
    let yy ← RecipeBuilder.use (ArithmeticRecipe.mul (p.2-q.2) (p.2-q.2)) (binary dy dy)
    let sum ← RecipeBuilder.use (ArithmeticRecipe.add ((p.1-q.1)*(p.1-q.1))
      ((p.2-q.2)*(p.2-q.2))) (binary xx yy)
    let root ← RecipeBuilder.use (RootOperation.recipe .square (squared p q) d) (unary sum)
    match axis with
    | .x => pure root
    | .y => RecipeBuilder.use (CoordinateOperation.recipe .transferX (d, 0)) (unary root)

set_option maxHeartbeats 6000000 in
/-- The actual primitive program computes the distance, including zero, on
either axis. The sign condition excludes the negative square root. -/
theorem computes (axis : Coordinate) (p q : Point K) (d : K)
    (_hd : 0 ≤ d) (hs : d^2 = squared p q) :
    let r := recipe axis p q d
    let final := inputs p q ++ r.steps.map ArithmeticRecipe.selectedObject
    Program.execute (inputs p q) r.steps = .ok final ∧
      Program.point final r.output = .ok (value axis d) := by
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  cases axis <;> constructor
  all_goals first
    | rfl
    | (unfold inputs CoordinateOperation.inputs
       origami_execute using
         try simp only [zero_sub]
         try rw [RootOperation.square_satisfies_iff]
         try unfold RootGeometry.crease
         try origami_geometry
         all_goals try split_ifs
         all_goals simp_all [squared, pow_two]
         all_goals repeat' apply And.intro
         all_goals try first
           | (solve | ring)
           | (field_simp <;> first | (solve | ring) | nlinarith [sq_nonneg d]))

end LeanOrigami.DistanceRecipe
