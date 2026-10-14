import LeanOrigami.Construction.ArithmeticCorrectness

/-!
# Axis projections and signed coordinate transfer

The five frame objects precede one arbitrary input point. No distinctness or
nonzero assumptions are needed: in particular, points already on an axis work.
Every output is obtained by folds and intersections, including a zero output.
-/

namespace LeanOrigami

/-- Projection preserves an axis; transfer puts a coordinate on the other axis. -/
inductive CoordinateOperation where
  | projectX | projectY | transferX | transferY
  deriving DecidableEq, Repr

namespace CoordinateOperation
variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The advertised output, with signs retained. -/
def value (op : CoordinateOperation) (p : Point K) : Point K :=
  match op with
  | .projectX => (p.1, 0)
  | .projectY => (0, p.2)
  | .transferX => (0, p.1)
  | .transferY => (p.2, 0)

/-- Explicit coordinate frame and an arbitrary point. -/
def inputs (p : Point K) : Program.State K :=
  [.point (0, 0), .point (1, 0), .line (Line.horizontal 0),
   .line (Line.chart 0 0), .point (0, 1), .point p]

/-- All four operations use the same primitive executor as arithmetic. -/
def recipe (op : CoordinateOperation) (p : Point K) : Recipe K 6 :=
  RecipeBuilder.build 6 do
    match op with
    | .projectX =>
      let vertical ← RecipeBuilder.fold (.axiom4 ⟨5⟩ ⟨2⟩) (Line.chart 0 p.1)
      RecipeBuilder.intersect vertical ⟨2⟩ (p.1, 0)
    | .projectY =>
      let horizontal ← RecipeBuilder.fold (.axiom4 ⟨5⟩ ⟨3⟩) (Line.horizontal p.2)
      RecipeBuilder.intersect ⟨3⟩ horizontal (0, p.2)
    | .transferX =>
      let diagonal ← RecipeBuilder.fold (.axiom5 ⟨1⟩ ⟨0⟩ ⟨3⟩) (Line.chart (-1) 0)
      let vertical ← RecipeBuilder.fold (.axiom4 ⟨5⟩ ⟨2⟩) (Line.chart 0 p.1)
      let equal ← RecipeBuilder.intersect vertical diagonal (p.1, p.1)
      let horizontal ← RecipeBuilder.fold (.axiom4 equal ⟨3⟩) (Line.horizontal p.1)
      RecipeBuilder.intersect ⟨3⟩ horizontal (0, p.1)
    | .transferY =>
      RecipeBuilder.use (ArithmeticRecipe.place p .y) (fun i =>
        match i.val with | 0 => 5 | 1 => 0 | 2 => 1 | 3 => 2 | _ => 3)

/-- Every input point has a successful primitive execution with exactly the
specified output. The theorem includes coincident frame/input points. -/
theorem computes (op : CoordinateOperation) (p : Point K) :
    let r := op.recipe p
    let final := inputs p ++ r.steps.map ArithmeticRecipe.selectedObject
    Program.execute (inputs p) r.steps = .ok final ∧
      Program.point final r.output = .ok (op.value p) := by
  cases op <;> constructor
  all_goals first
    | rfl
    | (unfold inputs
       origami_execute using origami_geometry)

end CoordinateOperation
end LeanOrigami
