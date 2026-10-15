import LeanOrigami.Construction.DistanceRecipe
import LeanOrigami.Construction.RootRecipe
import LeanOrigami.Geometry.TrisectionModel

/-!
# Primitive folds for both interior trisectors

The eight inputs are the standard coordinate frame, vertex, and two ray
points. Root witnesses are selected outputs, never additional inputs. The
builder expands every arithmetic operation into ordinary folds/intersections.
-/

namespace LeanOrigami.TrisectionRecipe
variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Both rays are exposed as endpoints and lines through the original vertex. -/
structure Outputs where
  firstPoint : PointRef
  secondPoint : PointRef
  firstLine : LineRef
  secondLine : LineRef
  /-- Internal axis witnesses used by the exact output contract. -/
  witnesses : Trisection.Roots PointRef
  cosine : PointRef

/-- A local scalar annotation pairs a proposed exact value with its constructed
axis point. It is assembly data; execution still checks every primitive step. -/
private structure AxisValue (K : Type) (value : K) where
  ref : PointRef

private def AxisValue.value {value : K} (_ : AxisValue K value) : K := value

private def binary (p q : PointRef) : Fin 7 → Nat :=
  (ArithmeticRecipe.Arguments.mk ⟨0⟩ ⟨1⟩ ⟨2⟩ ⟨3⟩ ⟨4⟩ p q).indices

private def unary (p : PointRef) : Fin 6 → Nat :=
  fun i => if i.val == 5 then p.index else i.val

private def add {x y : K} (p : AxisValue K x) (q : AxisValue K y) : RecipeBuilder K (AxisValue K (x+y)) := do
  return ⟨← RecipeBuilder.use (ArithmeticRecipe.add p.value q.value) (binary p.ref q.ref)⟩

private def sub {x y : K} (p : AxisValue K x) (q : AxisValue K y) : RecipeBuilder K (AxisValue K (x-y)) := do
  return ⟨← RecipeBuilder.use (ArithmeticRecipe.sub p.value q.value) (binary p.ref q.ref)⟩

private def mul {x y : K} (p : AxisValue K x) (q : AxisValue K y) : RecipeBuilder K (AxisValue K (x*y)) := do
  return ⟨← RecipeBuilder.use (ArithmeticRecipe.mul p.value q.value) (binary p.ref q.ref)⟩

private def div {x y : K} (p : AxisValue K x) (q : AxisValue K y) (h : y ≠ 0) : RecipeBuilder K (AxisValue K (x/y)) := do
  return ⟨← RecipeBuilder.use (ArithmeticRecipe.div p.value q.value h) (binary p.ref q.ref)⟩

private def coordinates (p : Point K) (ref : PointRef) :
    RecipeBuilder K (AxisValue K p.1 × AxisValue K p.2) := do
  let x ← RecipeBuilder.use (CoordinateOperation.recipe .projectX p) (unary ref)
  let y ← RecipeBuilder.use (CoordinateOperation.recipe .transferY p) (unary ref)
  return (⟨x⟩, ⟨y⟩)

private def squareRoot {x : K} (p : AxisValue K x) (root : K) : RecipeBuilder K (AxisValue K root) := do
  return ⟨← RecipeBuilder.use (RootOperation.recipe .square p.value root) (unary p.ref)⟩

/-- Construct a translated linear combination of the two frame directions. -/
private def endpoint {vx vy ux uy wx wy x y : K}
    (vertex : AxisValue K vx × AxisValue K vy)
    (u : AxisValue K ux × AxisValue K uy)
    (w : AxisValue K wx × AxisValue K wy) (a : AxisValue K x) (b : AxisValue K y) :
    RecipeBuilder K PointRef := do
  let x ← add (← add vertex.1 (← mul a u.1)) (← mul b w.1)
  let y ← add (← add vertex.2 (← mul a u.2)) (← mul b w.2)
  RecipeBuilder.use (ArithmeticRecipe.pair x.value y.value) (binary x.ref y.ref)

/-- Assemble the actual fold program. Positivity is used only to supply
nonzero divisors and genuine output lines; replay independently checks them. -/
def assemble (vertex first second : Point K) (roots : Trisection.Roots K)
    (h : roots.Valid vertex first second) : RecipeBuilder K Outputs := do
  let zero : AxisValue K 0 := ⟨⟨0⟩⟩
  let one : AxisValue K 1 := ⟨⟨1⟩⟩
  let aRef ← RecipeBuilder.use (DistanceRecipe.recipe .x first vertex roots.firstLength) (binary ⟨6⟩ ⟨5⟩)
  let bRef ← RecipeBuilder.use (DistanceRecipe.recipe .x second vertex roots.secondLength) (binary ⟨7⟩ ⟨5⟩)
  let a : AxisValue K roots.firstLength := ⟨aRef⟩
  let b : AxisValue K roots.secondLength := ⟨bRef⟩
  let vtx ← coordinates vertex ⟨5⟩
  let p ← coordinates first ⟨6⟩
  let q ← coordinates second ⟨7⟩
  let ux ← div (← sub p.1 vtx.1) a (ne_of_gt h.1)
  let uy ← div (← sub p.2 vtx.2) a (ne_of_gt h.1)
  let vx ← div (← sub q.1 vtx.1) b (ne_of_gt h.2.2.1)
  let vy ← div (← sub q.2 vtx.2) b (ne_of_gt h.2.2.1)
  let c ← add (← mul ux vx) (← mul uy vy)
  let s ← squareRoot (← sub one (← mul c c)) roots.sine
  let wx ← div (← sub vx (← mul c ux)) s (ne_of_gt h.2.2.2.2.1)
  let wy ← div (← sub vy (← mul c uy)) s (ne_of_gt h.2.2.2.2.1)
  let two ← add one one
  let three ← add two one
  let four ← add two two
  let linear ← div (← sub zero three) four (by norm_num)
  let constant ← div (← sub zero c) four (by norm_num)
  let tRef ← RecipeBuilder.use (RootRecipe.monicCubic 0 linear.value constant.value roots.thirdCosine)
    (fun i => match i.val with | 5 => 0 | 6 => linear.ref.index | 7 => constant.ref.index | n => n)
  let t : AxisValue K roots.thirdCosine := ⟨tRef⟩
  let tt ← mul t t
  let r ← squareRoot (← sub one tt) roots.thirdSine
  let firstPoint ← endpoint vtx (ux, uy) (wx, wy) t r
  let doubleCosine ← sub (← mul two tt) one
  let doubleSine ← mul (← mul two t) r
  let secondPoint ← endpoint vtx (ux, uy) (wx, wy) doubleCosine doubleSine
  let firstLine ← RecipeBuilder.fold (.axiom1 ⟨5⟩ firstPoint)
    (Line.through vertex (roots.firstPoint vertex first second) (roots.output_ne _ _ _ h).1)
  let secondLine ← RecipeBuilder.fold (.axiom1 ⟨5⟩ secondPoint)
    (Line.through vertex (roots.secondPoint vertex first second) (roots.output_ne _ _ _ h).2)
  return ⟨firstPoint, secondPoint, firstLine, secondLine, ⟨aRef, bRef, s.ref, tRef, r.ref⟩, c.ref⟩

/-- The ordinary frame followed by the vertex and both arbitrary ray points. -/
def inputs (vertex first second : Point K) : Program.State K :=
  CoordinateOperation.inputs vertex ++ [.point first, .point second]

/-- Finish assembly with eight parameter slots, retaining all four outputs. -/
def build (vertex first second : Point K) (roots : Trisection.Roots K)
    (h : roots.Valid vertex first second) : Program K × Outputs :=
  let (outputs, state) := (assemble vertex first second roots h).run ⟨8, []⟩
  (state.reversed.reverse, outputs)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 400000 in
/-- All four result references select the intended geometric objects from
this program's claimed final state. Legality of the steps is proved separately. -/
theorem output_objects (vertex first second : Point K) (roots : Trisection.Roots K)
    (h : roots.Valid vertex first second) :
    let result := build vertex first second roots h
    let final := inputs vertex first second ++ result.1.map ArithmeticRecipe.selectedObject
    Program.point final result.2.firstPoint = .ok (roots.firstPoint vertex first second) ∧
      Program.point final result.2.secondPoint = .ok (roots.secondPoint vertex first second) ∧
      Program.line final result.2.firstLine =
        .ok (Line.through vertex (roots.firstPoint vertex first second) (roots.output_ne _ _ _ h).1) ∧
      Program.line final result.2.secondLine =
        .ok (Line.through vertex (roots.secondPoint vertex first second) (roots.output_ne _ _ _ h).2) := by
  origami_normalize build
  refine ⟨?_, ?_, ?_, ?_⟩
  · rfl
  · let u := Trisection.unitVector vertex first roots.firstLength
    let w := roots.perpendicularUnit vertex first second
    let t := roots.thirdCosine
    let r := roots.thirdSine
    change Except.ok
      (vertex.1+((1+1)*(t*t)-1)*u.1+((1+1)*t*r)*w.1,
       vertex.2+((1+1)*(t*t)-1)*u.2+((1+1)*t*r)*w.2) = _
    norm_num [Trisection.Roots.secondPoint, pow_two, u, w, t, r]
  · rfl
  · rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 400000 in
/-- Root witnesses and cosine are constructed axis points, not extra seeds. -/
theorem witness_objects (vertex first second : Point K) (roots : Trisection.Roots K)
    (h : roots.Valid vertex first second) :
    let result := build vertex first second roots h
    let final := inputs vertex first second ++ result.1.map ArithmeticRecipe.selectedObject
    Program.point final result.2.witnesses.firstLength = .ok (roots.firstLength, 0) ∧
    Program.point final result.2.witnesses.secondLength = .ok (roots.secondLength, 0) ∧
    Program.point final result.2.witnesses.sine = .ok (roots.sine, 0) ∧
    Program.point final result.2.witnesses.thirdCosine = .ok (roots.thirdCosine, 0) ∧
    Program.point final result.2.witnesses.thirdSine = .ok (roots.thirdSine, 0) ∧
    Program.point final result.2.cosine = .ok (roots.cosine vertex first second, 0) := by
  origami_normalize build
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl⟩
  change Except.ok (roots.thirdCosine-roots.thirdCosine^2-(-roots.thirdCosine^2), (0 : K)) = _
  congr 2; ring

set_option maxRecDepth 16384 in
-- The A1 guard below deliberately inspects a goal without changing it. The
-- unused-tactic linter flags that inspection when the replay tactic repeats it.
set_option linter.unusedTactic false in
set_option maxHeartbeats 32000000 in
/-- Every primitive step is legal under the exact root equations and branch
conditions. The initial state contains only the frame and the three inputs. -/
theorem executes (vertex first second : Point K) (roots : Trisection.Roots K)
    (h : roots.Valid vertex first second) :
    let result := build vertex first second roots h
    Program.execute (inputs vertex first second) result.1 =
      .ok (inputs vertex first second ++ result.1.map ArithmeticRecipe.selectedObject) := by
  change Program.execute (inputs vertex first second) (build vertex first second roots h).1 = .ok _
  have hout := roots.output_ne vertex first second h
  rcases h with ⟨ha, ha2, hb, hb2, hs, hs2, ht, ht1, ht3, hr, hr2⟩
  dsimp only [Trisection.Roots.cosine, Trisection.unitVector, Point.dot] at hs2 ht3
  have ha0 := ne_of_gt ha
  have hb0 := ne_of_gt hb
  have hs0 := ne_of_gt hs
  unfold inputs CoordinateOperation.inputs
  origami_normalize build
  origami_execute using
    try dsimp only [AxisValue.value]
    try solve
      | exact hout.1
      | simp only [FoldInput.FiniteCondition, pow_two, one_add_one_eq_two]
      | -- Only the final A1 folds need the expanded endpoint formulas.
        run_tac Lean.Elab.Tactic.withMainContext do
          let target ← Lean.Elab.Tactic.getMainTarget
          let args := target.getAppArgs
          let input ← if target.isAppOf ``FoldInput.Satisfies then
              pure args[args.size-2]!
            else if target.isAppOf ``FoldInput.FiniteCondition then pure args.back!
            else Lean.throwError "not a fold condition"
          unless (← Lean.Meta.whnf input).isAppOf ``FoldInput.axiom1 do
            Lean.throwError "not an A1 fold"
        first
          | simpa only [FoldInput.FiniteCondition, Trisection.Roots.secondPoint,
              Trisection.Roots.perpendicularUnit, Trisection.Roots.cosine,
              Trisection.unitVector, Point.dot, pow_two, one_add_one_eq_two] using hout.2
          | dsimp only [FoldInput.Satisfies, Trisection.Roots.secondPoint,
              Trisection.Roots.perpendicularUnit, Trisection.Roots.cosine,
              Trisection.unitVector, Point.dot]
            norm_num only [pow_two, one_add_one_eq_two]
            exact ⟨Line.through_left _ _ _, Line.through_right _ _ _⟩
    try rw [RootOperation.square_satisfies_iff]
    try solve
      | simpa [DistanceRecipe.squared, Point.sqNorm, pow_two] using ha2
      | simpa [DistanceRecipe.squared, Point.sqNorm, pow_two] using hb2
      | simpa [Trisection.Roots.cosine, Trisection.unitVector, Point.dot, pow_two] using hs2
      | simpa [pow_two] using hr2
    try unfold RootGeometry.crease
    try origami_geometry
    all_goals try split_ifs
    all_goals simp_all [Point.sqNorm, DistanceRecipe.squared, pow_two]
    all_goals generalize hc :
      (first.1-vertex.1)/roots.firstLength*((second.1-vertex.1)/roots.secondLength) +
        (first.2-vertex.2)/roots.firstLength*((second.2-vertex.2)/roots.secondLength) = c at *
    all_goals (have hneg :
      -((first.2-vertex.2)/roots.firstLength*((second.2-vertex.2)/roots.secondLength)) +
        -((first.1-vertex.1)/roots.firstLength*((second.1-vertex.1)/roots.secondLength)) = -c := by linarith only [hc])
    all_goals try rw [hneg]
    all_goals generalize hnx :
      (second.1-vertex.1)/roots.secondLength - c*((first.1-vertex.1)/roots.firstLength) = nx at *
    all_goals generalize hny :
      (second.2-vertex.2)/roots.secondLength - c*((first.2-vertex.2)/roots.firstLength) = ny at *
    all_goals try (casesm* _ ∧ _)
    all_goals repeat' apply And.intro
    all_goals simp only [← pow_two] at *
    all_goals try first
      | assumption
      | (solve | ring)
      | nlinarith only [ht3]
      | (field_simp <;> first
          | (solve | ring)
          | nlinarith only [ha2, sq_nonneg roots.firstLength]
          | nlinarith only [hb2, sq_nonneg roots.secondLength]
          | nlinarith only [hs2, sq_nonneg roots.sine]
          | nlinarith only [hr2, sq_nonneg roots.thirdSine]
          | nlinarith only [ht3])
      | linarith

end LeanOrigami.TrisectionRecipe
