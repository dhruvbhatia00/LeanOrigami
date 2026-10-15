import LeanOrigami.Widget.Measurements
import LeanOrigami.Construction.TrisectionRecipe
import LeanOrigami.Construction.TrisectionCondition
import LeanOrigami.Scalar.Trisection

/-!
# Visual trisection with an exact interior branch

The template erases a primitive construction, selects the unique cubic root
between one half and one, and checks a polynomial certificate for both rays.
Only the frame and original ray points are parameters.
-/

namespace LeanOrigami.Widget

/-- Denominator-free slope interval selecting the interior trisection branch. -/
def thirdCosineCondition (index : Nat) : Condition :=
  let a : ConditionExpr := .component index .a
  let b : ConditionExpr := .component index .b
  let numerator := ConditionExpr.neg (.mul a b)
  let denominator := ConditionExpr.mul b b
  .and (.lt denominator (.mul (.constant 2 1) numerator)) (.lt numerator denominator)

/-- The polynomial interval is exactly `1/2 < slope < 1`, independent of the
sign of the canonical line's second coefficient. -/
theorem thirdCosineCondition_iff {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (crease : Line K) (hb : crease.b ≠ 0) :
    (thirdCosineCondition 0).Holds (Component.value [.line crease]) ↔
      1/2 < -crease.a/crease.b ∧ -crease.a/crease.b < 1 := by
  simp only [thirdCosineCondition, Condition.Holds, ConditionExpr.eval,
    Component.value, List.getElem?_cons_zero, Int.cast_ofNat, Nat.cast_one, div_one]
  have hs : 0 < crease.b^2 := sq_pos_of_ne_zero hb
  have he : -crease.a/crease.b = -(crease.a*crease.b)/crease.b^2 := by
    field_simp
  rw [he]
  rw [lt_div_iff₀ hs, div_lt_iff₀ hs]
  simp only [pow_two]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- Among legal cubic creases, the branch condition admits precisely the
intended root. The solver's enumeration order has no role. -/
theorem trisection_cubic_policy {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (c t : K) (ht : 1/2 < t) (ht1 : t < 1) (ht3 : 4*t^3-3*t = c)
    (crease : Line K) (legal : (RootGeometry.input 0 (-3/4) (-c/4)).Satisfies crease) :
    (thirdCosineCondition 0).Holds (Component.value [.line crease]) ↔
      crease = RootGeometry.crease t := by
  have alignment := ((FoldInput.axiom6_iff_equations _ _ _ _ _).mp legal).1
  have hb := RootGeometry.nonvertical crease alignment
  have shape := RootGeometry.eq_crease_of_first_alignment crease alignment
  rw [thirdCosineCondition_iff crease hb]
  constructor
  · intro branch
    have equation := (RootGeometry.satisfies_iff 0 (-3/4) (-c/4) _).mp (shape ▸ legal)
    have cubic : 4*(-crease.a/crease.b)^3-3*(-crease.a/crease.b) = c := by
      nlinarith only [equation]
    exact shape.trans (congrArg RootGeometry.crease
      (Trisection.thirdCosine_unique branch.1 ht cubic ht3))
  · intro he
    have ht0 : t ≠ 0 := by linarith
    simpa [he, RootGeometry.crease, Line.normalize, ht0] using And.intro ht ht1

private def representative : Program ℚ × TrisectionRecipe.Outputs :=
  TrisectionRecipe.build (0, 0) (1, 0) (-117/125, 44/125)
    ⟨1, 1, 44/125, 3/5, 4/5⟩ (by
      norm_num [Trisection.Roots.Valid, Trisection.Roots.cosine,
        Trisection.unitVector, Point.dot, Point.sqNorm])

/-- The endpoint certificate also requires each output line to contain its
endpoint and the original vertex. -/
def trisectionPostcondition (outputs : TrisectionRecipe.Outputs) : Condition :=
  let refs := outputs.witnesses
  let rays := TrisectionCondition.condition 5 6 7 outputs.firstPoint.index outputs.secondPoint.index
    ⟨refs.firstLength.index, refs.secondLength.index, refs.sine.index,
      refs.thirdCosine.index, refs.thirdSine.index⟩ outputs.cosine.index
  .and rays (.and (.onLine 5 outputs.firstLine.index)
    (.and (.onLine outputs.firstPoint.index outputs.firstLine.index)
      (.and (.onLine 5 outputs.secondLine.index)
        (.onLine outputs.secondPoint.index outputs.secondLine.index))))

/-- Ordinary recipe operations with exact branch and final-output checks. -/
def trisectionTemplate : RecipeTemplate := Id.run do
  let steps := representative.1.map RecipeOperation.ofInstruction
  let outputs := representative.2
  let mut checks : Array RecipeRequirement := #[]
  for (step, i) in steps.zipIdx do
    match step with
    | .fold (.axiom5 source fixed target) =>
      let diagonal := source.index == 1 && fixed.index == 0 && target.index == 3
      checks := checks.push ⟨i+1, 0,
        if diagonal then RecipeFrame.lineIs (8+i) 1 (-1) 0 else nonnegativeSlope (8+i)⟩
    | .fold (.axiom6 ..) => checks := checks.push ⟨i+1, 0, thirdCosineCondition (8+i)⟩
    | _ => pure ()
  checks := checks.push ⟨steps.length, 0, trisectionPostcondition outputs⟩
  return {
    parameters := RecipeFrame.parameters ++ #[⟨"Vertex", .point⟩,
      ⟨"First ray point", .point⟩, ⟨"Second ray point", .point⟩]
    steps, output := outputs.firstPoint.index, checks
    requirements := RecipeFrame.requirements.push (.not (.collinear 5 6 7))
    outputs := #[⟨"First trisector point", outputs.firstPoint.index⟩,
      ⟨"Second trisector point", outputs.secondPoint.index⟩,
      ⟨"First trisector line", outputs.firstLine.index⟩,
      ⟨"Second trisector line", outputs.secondLine.index⟩] }

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- The same operations are used for every valid input and every exact witness. -/
theorem trisectionTemplate_steps {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (vertex first second : Point K) (roots : Trisection.Roots K)
    (h : roots.Valid vertex first second) :
    (TrisectionRecipe.build vertex first second roots h).1.map RecipeOperation.ofInstruction =
      trisectionTemplate.steps := by
  change _ = representative.1.map RecipeOperation.ofInstruction
  unfold representative
  origami_normalize TrisectionRecipe.build
  rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- Geometric outputs and internal witnesses retain the same references. -/
theorem trisectionTemplate_outputs {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (vertex first second : Point K) (roots : Trisection.Roots K)
    (h : roots.Valid vertex first second) :
    (TrisectionRecipe.build vertex first second roots h).2 = representative.2 := by
  unfold representative
  origami_normalize TrisectionRecipe.build
  rfl

/-- The exact output condition implies real trisection of the referenced rays.
Its validity component separately guarantees that the references are points. -/
theorem trisectionPostcondition_sound (outputs : TrisectionRecipe.Outputs)
    (objects : Program.State Scalar) (h : (trisectionPostcondition outputs).Satisfied objects) :
    let point := TrisectionCondition.point
      (fun i field => Scalar.realHom (Component.value objects i field))
    Trisection.IsTrisection (point 5) (point 6) (point 7)
      (point outputs.firstPoint.index) (point outputs.secondPoint.index) := by
  apply TrisectionCondition.sound
  exact (Condition.holds_map Scalar.realHom Scalar.toReal_le Scalar.toReal_lt _ _).mpr h.2.1

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
/-- A valid exact witness passes the input, branch, and final-output checks. -/
theorem trisectionTemplate_checks {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (vertex first second : Point K) (roots : Trisection.Roots K)
    (domain : Trisection.Domain vertex first second) (h : roots.Valid vertex first second) :
    let program := (TrisectionRecipe.build vertex first second roots h).1
    let final := TrisectionRecipe.inputs vertex first second ++
      program.map ArithmeticRecipe.selectedObject
    trisectionTemplate.requirements.all
      (Condition.checkObjects (TrisectionRecipe.inputs vertex first second)) = true ∧
      trisectionTemplate.checks.all (fun check =>
        check.condition.checkObjects (final.take (8 + check.before))) = true := by
  have hout := roots.output_ne vertex first second h
  have firstVertex := Line.through_left vertex (roots.firstPoint vertex first second) hout.1
  have firstEndpoint := Line.through_right vertex (roots.firstPoint vertex first second) hout.1
  have secondVertex := Line.through_left vertex (roots.secondPoint vertex first second) hout.2
  have secondEndpoint := Line.through_right vertex (roots.secondPoint vertex first second) hout.2
  simp only [← Array.all_toList]
  origami_normalize TrisectionRecipe.build
  run_tac Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let target ← Lean.Meta.transform (← goal.getType) (pre := fun e => do
      let type ← Lean.Meta.whnf (← Lean.Meta.inferType e)
      if type.isAppOf ``List && type.getAppArgs.back!.isAppOf ``Object then
        return .done e
      if type.isAppOf ``List || type.isAppOf ``Array then
        return .done (← Lean.Meta.withTransparency .all (Lean.Meta.reduce e))
      return .continue)
    Lean.Elab.Tactic.replaceMainGoal [← goal.change target]
  obtain ⟨ha, ha2, hb, hb2, hs, hs2, ht, ht1, ht3, hr, hr2⟩ := h
  have ha0 := ne_of_gt ha
  have hb0 := ne_of_gt hb
  have hs0 := ne_of_gt hs
  have ht0 : roots.thirdCosine ≠ 0 := by linarith
  have hr0 := ne_of_gt hr
  have firstSign := (root_crease_nonnegative_iff roots.firstLength).mpr ha.le
  have secondSign := (root_crease_nonnegative_iff roots.secondLength).mpr hb.le
  have sineSign := (root_crease_nonnegative_iff roots.sine).mpr hs.le
  have thirdSign := (root_crease_nonnegative_iff roots.thirdSine).mpr hr.le
  have cubicBranch := (thirdCosineCondition_iff (RootGeometry.crease roots.thirdCosine)
    (RootGeometry.nonvertical _ (RootGeometry.first_alignment _))).mpr
    (by simpa [RootGeometry.crease, Line.normalize, ht0] using And.intro ht ht1)
  simp only [List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  simp only [Condition.checkObjects, Condition.check, Bool.and_eq_true, decide_eq_true_eq,
    Condition.valid, ConditionExpr.valid, Condition.Holds, ConditionExpr.eval, Component.isPoint]
  -- Resolve each referenced object before algebraic simplification, so the
  -- simplifier never traverses hundreds of irrelevant intermediate objects.
  run_tac Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let (target, _) ← Lean.Meta.transformWithCache (← goal.getType) {}
      (skipInstances := true) (pre := fun e => do
        if e.isAppOf ``Component.value || e.isAppOf ``Component.pointAt ||
            e.isAppOf ``Component.lineAt then return .done (← Lean.Meta.whnf e)
        return .continue)
    Lean.Elab.Tactic.replaceMainGoal [← goal.replaceTargetDefEq target]
  norm_num [Trisection.Domain, Condition.Holds, ConditionExpr.eval, Component.value,
    TrisectionCondition.condition, thirdCosineCondition, nonnegativeSlope,
    Trisection.Roots.cosine, Trisection.Roots.firstPoint, Trisection.Roots.secondPoint,
    Trisection.Roots.perpendicularUnit, Trisection.unitVector, Point.dot, Point.det, Point.sqNorm,
    RootGeometry.crease, Line.normalize, Line.Contains, Line.chart,
    ha0, hb0, hs0, ht0, hr0, pow_two] at *
  all_goals repeat' apply And.intro
  all_goals first
    | assumption
    | rfl
    | positivity
    | (solve | field_simp; ring)
    | skip
  · exact @decide_eq_true _ _ (by
      intro equality
      apply domain
      simpa only [sub_eq_add_neg] using sub_eq_zero.mpr equality)
  · exact cubicBranch.1
  · exact cubicBranch.2
  · have squared := ha2
    dsimp [Point.sqNorm] at squared
    nlinarith only [squared]
  · have squared := hb2
    dsimp [Point.sqNorm] at squared
    nlinarith only [squared]
  · change roots.firstLength * roots.secondLength * roots.cosine vertex first second =
      (first.1 + -vertex.1) * (second.1 + -vertex.1) +
        (first.2 + -vertex.2) * (second.2 + -vertex.2)
    dsimp [Trisection.Roots.cosine, Trisection.unitVector, Point.dot]
    field_simp
    ring
  · change roots.sine*roots.sine = 1 +
      -(roots.cosine vertex first second * roots.cosine vertex first second)
    nlinarith only [hs2]
  · change 1/2 < roots.thirdCosine - roots.thirdCosine*roots.thirdCosine -
      (-(roots.thirdCosine*roots.thirdCosine))
    nlinarith only [ht]
  · change roots.thirdCosine - roots.thirdCosine*roots.thirdCosine -
      (-(roots.thirdCosine*roots.thirdCosine)) < 1
    nlinarith only [ht1]
  · change 4 * ((roots.thirdCosine - (roots.thirdCosine*roots.thirdCosine) - (-(roots.thirdCosine*roots.thirdCosine))) *
      (roots.thirdCosine - (roots.thirdCosine*roots.thirdCosine) - (-(roots.thirdCosine*roots.thirdCosine))) *
      (roots.thirdCosine - (roots.thirdCosine*roots.thirdCosine) - (-(roots.thirdCosine*roots.thirdCosine)))) +
      -(3 * (roots.thirdCosine - (roots.thirdCosine*roots.thirdCosine) - (-(roots.thirdCosine*roots.thirdCosine)))) =
        roots.cosine vertex first second
    nlinarith only [ht3]
  · change roots.thirdSine * roots.thirdSine = 1 +
      -((roots.thirdCosine - (roots.thirdCosine*roots.thirdCosine) - (-(roots.thirdCosine*roots.thirdCosine))) *
        (roots.thirdCosine - (roots.thirdCosine*roots.thirdCosine) - (-(roots.thirdCosine*roots.thirdCosine))))
    nlinarith only [hr2]
  · change roots.firstLength * roots.secondLength * roots.sine *
      ((roots.firstPoint vertex first second).1 + -vertex.1) =
        (roots.thirdCosine - roots.thirdCosine*roots.thirdCosine - (-(roots.thirdCosine*roots.thirdCosine))) * roots.secondLength * roots.sine * (first.1 + -vertex.1) +
          roots.thirdSine * (roots.firstLength * (second.1 + -vertex.1) +
            -(roots.secondLength * roots.cosine vertex first second * (first.1 + -vertex.1)))
    dsimp [Trisection.Roots.firstPoint, Trisection.Roots.perpendicularUnit,
      Trisection.Roots.cosine, Trisection.unitVector, Point.dot]
    field_simp
    ring
  · change roots.firstLength * roots.secondLength * roots.sine *
      ((roots.firstPoint vertex first second).2 + -vertex.2) =
        (roots.thirdCosine - roots.thirdCosine*roots.thirdCosine - (-(roots.thirdCosine*roots.thirdCosine))) * roots.secondLength * roots.sine * (first.2 + -vertex.2) +
          roots.thirdSine * (roots.firstLength * (second.2 + -vertex.2) +
            -(roots.secondLength * roots.cosine vertex first second * (first.2 + -vertex.2)))
    dsimp [Trisection.Roots.firstPoint, Trisection.Roots.perpendicularUnit,
      Trisection.Roots.cosine, Trisection.unitVector, Point.dot]
    field_simp
    ring
  · change roots.firstLength * roots.secondLength * roots.sine *
      (vertex.1 + (2*(roots.thirdCosine*roots.thirdCosine)-1)*
        (Trisection.unitVector vertex first roots.firstLength).1 +
        2*roots.thirdCosine*roots.thirdSine*(roots.perpendicularUnit vertex first second).1 +
        -vertex.1) =
        (2*((roots.thirdCosine - roots.thirdCosine*roots.thirdCosine - (-(roots.thirdCosine*roots.thirdCosine)))*(roots.thirdCosine - roots.thirdCosine*roots.thirdCosine - (-(roots.thirdCosine*roots.thirdCosine)))) + -1) * roots.secondLength * roots.sine * (first.1 + -vertex.1) +
          (2*(roots.thirdCosine - roots.thirdCosine*roots.thirdCosine - (-(roots.thirdCosine*roots.thirdCosine)))*roots.thirdSine) * (roots.firstLength * (second.1 + -vertex.1) +
            -(roots.secondLength * roots.cosine vertex first second * (first.1 + -vertex.1)))
    dsimp [Trisection.Roots.secondPoint, Trisection.Roots.perpendicularUnit,
      Trisection.Roots.cosine, Trisection.unitVector, Point.dot]
    field_simp
    ring
  · change roots.firstLength * roots.secondLength * roots.sine *
      (vertex.2 + (2*(roots.thirdCosine*roots.thirdCosine)-1)*
        (Trisection.unitVector vertex first roots.firstLength).2 +
        2*roots.thirdCosine*roots.thirdSine*(roots.perpendicularUnit vertex first second).2 +
        -vertex.2) =
        (2*((roots.thirdCosine - roots.thirdCosine*roots.thirdCosine - (-(roots.thirdCosine*roots.thirdCosine)))*(roots.thirdCosine - roots.thirdCosine*roots.thirdCosine - (-(roots.thirdCosine*roots.thirdCosine)))) + -1) * roots.secondLength * roots.sine * (first.2 + -vertex.2) +
          (2*(roots.thirdCosine - roots.thirdCosine*roots.thirdCosine - (-(roots.thirdCosine*roots.thirdCosine)))*roots.thirdSine) * (roots.firstLength * (second.2 + -vertex.2) +
            -(roots.secondLength * roots.cosine vertex first second * (first.2 + -vertex.2)))
    dsimp [Trisection.Roots.secondPoint, Trisection.Roots.perpendicularUnit,
      Trisection.Roots.cosine, Trisection.unitVector, Point.dot]
    field_simp
    ring

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- The advertised domain has a completion of precisely these primitive folds;
every accepted completion has the checked geometric output specification. -/
theorem trisectionTemplate_contract :
    RecipeContract trisectionTemplate
      (fun p : Point Scalar × Point Scalar × Point Scalar =>
        TrisectionRecipe.inputs p.1 p.2.1 p.2.2)
      (fun p => Trisection.Domain p.1 p.2.1 p.2.2)
      (trisectionPostcondition representative.2) := by
  constructor
  · intro parameters _ program final completion
    exact completion.final_condition
      ⟨trisectionTemplate.steps.length, 0, trisectionPostcondition representative.2⟩
      (by exact Array.mem_push_self) rfl
  · rintro ⟨vertex, first, second⟩ domain
    obtain ⟨roots, valid⟩ := Scalar.trisectionRoots_exists vertex first second domain
    let program := (TrisectionRecipe.build vertex first second roots valid).1
    refine ⟨program, TrisectionRecipe.inputs vertex first second ++
      program.map ArithmeticRecipe.selectedObject,
      trisectionTemplate_steps vertex first second roots valid,
      TrisectionRecipe.executes vertex first second roots valid, ?_,
      (trisectionTemplate_checks vertex first second roots domain valid).1, ?_, ?_⟩
    · have shape := congrArg List.length (trisectionTemplate_steps vertex first second roots valid)
      simpa [program] using congrArg
        (fun n => (TrisectionRecipe.inputs vertex first second).length + n) shape
    · simpa [TrisectionRecipe.inputs, CoordinateOperation.inputs, program] using
        (trisectionTemplate_checks vertex first second roots domain valid).2
    · constructor <;> rfl

/-- Recognition includes every operation and condition, so an edited template
cannot retain the built-in geometric guarantee. -/
def trisectionSpecification (recipe : RecipeTemplate) : Option String :=
  if recipe.source == trisectionTemplate.source then
    some "Returns two rays strictly inside the input angle, in order, dividing it into three equal angles."
  else none

end LeanOrigami.Widget
