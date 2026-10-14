import LeanOrigami.Construction.CoordinateRecipe
import LeanOrigami.Construction.RootGeometry

/-!
# Square and cube roots as primitive constructions

The common parabola tangent is `y = t*x - t²`. Passing it through `(0,-x)`
encodes a square root; the existing two-alignment configuration encodes a cube
root. A pair of perpendicular folds translates the tangent through the origin,
so its intersection at x = 1 recovers the slope without dividing by the root.
This works at zero. Inputs are the five frame objects and `(x,0)` only.
-/

namespace LeanOrigami

/-- The nonnegative square root or the unique real cube root. -/
inductive RootOperation where
  | square | cube
  deriving DecidableEq, Repr

namespace RootOperation
variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Algebraic specification, including the sign that distinguishes square roots. -/
def Relation (op : RootOperation) (x t : K) : Prop :=
  match op with
  | .square => 0 ≤ t ∧ t^2 = x
  | .cube => t^3 = x

/-- The construction's input domain; cube roots have no sign restriction. -/
def Domain (op : RootOperation) (x : K) : Prop :=
  match op with | .square => 0 ≤ x | .cube => True

private def arithmetic (first second : PointRef) : Fin 7 → Nat :=
  (ArithmeticRecipe.Arguments.mk ⟨0⟩ ⟨1⟩ ⟨2⟩ ⟨3⟩ ⟨4⟩ first second).indices

private def coordinate (point : PointRef) : Fin 6 → Nat :=
  fun i => if i.val == 5 then point.index else i.val

/-- A proposed root supplies selected outputs, never an extra input. The
ordinary primitive checker still checks its legality at every step. -/
def recipe (op : RootOperation) (x t : K) : Recipe K 6 := RecipeBuilder.build 6 do
  let minusOne ← RecipeBuilder.use (ArithmeticRecipe.sub 0 1) (arithmetic ⟨0⟩ ⟨1⟩)
  let minusUnit ← RecipeBuilder.use (CoordinateOperation.recipe .transferX (-1, 0))
    (coordinate minusOne)
  let target ← RecipeBuilder.fold (.axiom4 minusUnit ⟨3⟩) (Line.horizontal (-1))
  let negative ← RecipeBuilder.use (ArithmeticRecipe.sub 0 x) (arithmetic ⟨0⟩ ⟨5⟩)
  let selected ← match op with
    | .square => do
      let anchor ← RecipeBuilder.use (CoordinateOperation.recipe .transferX (-x, 0))
        (coordinate negative)
      RecipeBuilder.fold (.axiom5 ⟨4⟩ anchor target) (RootGeometry.crease t)
    | .cube => do
      let secondTarget ← RecipeBuilder.fold (.axiom4 ⟨5⟩ ⟨2⟩) (Line.chart 0 x)
      RecipeBuilder.fold (.axiom6 ⟨4⟩ negative target secondTarget) (RootGeometry.crease t)
  let perpendicular ← RecipeBuilder.fold (.axiom4 ⟨0⟩ selected) (Line.chart t 0)
  let parallel ← RecipeBuilder.fold (.axiom4 ⟨0⟩ perpendicular)
    (Line.normalize (-t) 1 0 (Or.inr one_ne_zero))
  let unitVertical ← RecipeBuilder.fold (.axiom4 ⟨1⟩ ⟨2⟩) (Line.chart 0 1)
  let slope ← RecipeBuilder.intersect parallel unitVertical (1, t)
  RecipeBuilder.use (CoordinateOperation.recipe .transferY (1, t)) (coordinate slope)

/-- The input point is a scalar on the x-axis, with the explicit standard frame. -/
def inputs (x : K) : Program.State K := CoordinateOperation.inputs (x, 0)

/-- Fixing the tangent's intercept encodes exactly the square equation. -/
theorem square_satisfies_iff (x t : K) :
    (FoldInput.axiom5 (0, 1) (0, -x) (Line.horizontal (-1))).Satisfies
      (RootGeometry.crease t) ↔ t^2 = x := by
  rw [FoldInput.axiom5_iff_equations, RootGeometry.first_alignment,
    RootGeometry.contains_crease]
  simp
  constructor <;> intro h <;> nlinarith

/-- The second alignment specializes the existing cubic encoding. -/
theorem cube_satisfies_iff (x t : K) :
    (FoldInput.axiom6 (0, 1) (-x, 0) (Line.horizontal (-1)) (Line.chart 0 x)).Satisfies
      (RootGeometry.crease t) ↔ t^3 = x := by
  simpa [RootGeometry.input, ← sub_eq_add_neg, sub_eq_zero] using
    RootGeometry.satisfies_iff (0 : K) 0 (-x) t

set_option maxHeartbeats 800000 in
/-- Every root satisfying the specification is produced by the actual saved
primitive program, with no exceptional case at zero. -/
theorem computes (op : RootOperation) (x t : K) (h : op.Relation x t) :
    let r := op.recipe x t
    let final := inputs x ++ r.steps.map ArithmeticRecipe.selectedObject
    Program.execute (inputs x) r.steps = .ok final ∧
      Program.point final r.output = .ok (t, 0) := by
  cases op <;> constructor
  all_goals first
    | rfl
    | (unfold inputs CoordinateOperation.inputs
       origami_execute using
         simp only [Relation] at h
         try simp only [zero_sub]
         try rw [square_satisfies_iff]
         try rw [cube_satisfies_iff]
         try unfold RootGeometry.crease
         try origami_geometry
         all_goals try split_ifs
         all_goals simp_all
         all_goals try (field_simp; first | (solve | ring) | nlinarith [sq_nonneg t]))

/-- The square-root sign restriction rules out the negative branch. Cube roots
are unique without a sign restriction, over any ordered field. -/
theorem Relation.unique {op : RootOperation} {x s t : K}
    (hs : op.Relation x s) (ht : op.Relation x t) : s = t := by
  cases op with
  | square => simp only [Relation] at hs ht; nlinarith [sq_nonneg (s - t)]
  | cube =>
    simp only [Relation] at hs ht
    have he : s^3 = t^3 := hs.trans ht.symm
    exact (Odd.pow_inj (by decide : Odd 3)).mp he

/-- Successful root specifications imply the advertised input condition. -/
theorem Relation.domain {op : RootOperation} {x t : K}
    (h : op.Relation x t) : op.Domain x := by
  cases op with
  | square => exact h.2 ▸ sq_nonneg t
  | cube => trivial

end RootOperation
end LeanOrigami
