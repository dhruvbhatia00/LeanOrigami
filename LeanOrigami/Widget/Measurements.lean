import LeanOrigami.Widget.Frame
import LeanOrigami.Construction.MeasurementSemantics
import LeanOrigami.Scalar.RootOperations

/-!
# Coordinate, distance, and root templates

This common interface connects the primitive recipes to visual-library
contracts. Samples supply parameters, never branch numbers. The positive
diagonal and nonnegative square-root slope are selected by exact conditions.
-/

namespace LeanOrigami.Widget
open RecipeFrame

/-- Measurement operations have either one point/scalar or two point inputs. -/
inductive MeasurementOperation where
  | projectX | projectY | transferX | transferY | distanceX | distanceY | sqrt | cbrt
  deriving DecidableEq, Repr

namespace MeasurementOperation
variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Five explicit frame objects, then the operands. -/
def arity : MeasurementOperation → Nat
  | .distanceX | .distanceY => 7
  | _ => 6

/-- Human-readable names distinguish signed coordinates from magnitudes. -/
def name : MeasurementOperation → String
  | .projectX => "Project onto X-axis" | .projectY => "Project onto Y-axis"
  | .transferX => "Signed X-coordinate to Y-axis" | .transferY => "Signed Y-coordinate to X-axis"
  | .distanceX => "Distance to nonnegative X-axis" | .distanceY => "Distance to nonnegative Y-axis"
  | .sqrt => "Nonnegative square root" | .cbrt => "Real cube root"

/-- Arbitrary point inputs, or a scalar represented on the x-axis. -/
def inputs (op : MeasurementOperation) (p q : Point K) : Program.State K :=
  match op with
  | .distanceX | .distanceY => DistanceRecipe.inputs p q
  | _ => CoordinateOperation.inputs p

/-- Only root operations require axis inputs; only square roots restrict sign. -/
def Valid (op : MeasurementOperation) (p : Point K) : Prop :=
  match op with
  | .sqrt => p.2 = 0 ∧ 0 ≤ p.1
  | .cbrt => p.2 = 0
  | _ => True

/-- A root witness identifies the selected exact geometry. It is never an input
object. Coordinate operations need no witness. -/
def Witness (op : MeasurementOperation) (p q : Point K) (t : K) : Prop :=
  match op with
  | .sqrt => RootOperation.square.Relation p.1 t
  | .cbrt => RootOperation.cube.Relation p.1 t
  | .distanceX | .distanceY => 0 ≤ t ∧ t^2 = DistanceRecipe.squared p q
  | _ => True

/-- Dispatch to the existing primitive recipes without introducing new rules. -/
def recipe (op : MeasurementOperation) (p q : Point K) (t : K) : Recipe K op.arity :=
  match op with
  | .projectX => CoordinateOperation.recipe .projectX p
  | .projectY => CoordinateOperation.recipe .projectY p
  | .transferX => CoordinateOperation.recipe .transferX p
  | .transferY => CoordinateOperation.recipe .transferY p
  | .distanceX => DistanceRecipe.recipe .x p q t
  | .distanceY => DistanceRecipe.recipe .y p q t
  | .sqrt => RootOperation.recipe .square p.1 t
  | .cbrt => RootOperation.recipe .cube p.1 t

/-- Exact output meaning; signed transfer is distinct from distance. -/
def value (op : MeasurementOperation) (p : Point K) (t : K) : Point K :=
  match op with
  | .projectX => (p.1, 0) | .projectY => (0, p.2)
  | .transferX => (0, p.1) | .transferY => (p.2, 0)
  | .distanceY => (0, t)
  | _ => (t, 0)

/-- The visual operation uses the program covered by its execution theorem. -/
theorem computes (op : MeasurementOperation) (p q : Point K) (t : K)
    (h : op.Valid p) (w : op.Witness p q t) :
    let r := op.recipe p q t
    let final := op.inputs p q ++ r.steps.map ArithmeticRecipe.selectedObject
    Program.execute (op.inputs p q) r.steps = .ok final ∧
      Program.point final r.output = .ok (op.value p t) := by
  cases op with
  | projectX => exact CoordinateOperation.computes .projectX p
  | projectY => exact CoordinateOperation.computes .projectY p
  | transferX => exact CoordinateOperation.computes .transferX p
  | transferY => exact CoordinateOperation.computes .transferY p
  | distanceX => exact DistanceRecipe.computes .x p q t w.1 w.2
  | distanceY => exact DistanceRecipe.computes .y p q t w.1 w.2
  | sqrt =>
    rcases p with ⟨x, y⟩
    rcases h with ⟨rfl, _⟩
    exact RootOperation.computes .square x t w
  | cbrt =>
    rcases p with ⟨x, y⟩
    change y = 0 at h
    subst y
    exact RootOperation.computes .cube x t w

/-- Every advertised scalar input has a witness; zero distance is included. -/
theorem witness_exists (op : MeasurementOperation) (p q : Point Scalar) (h : op.Valid p) :
    ∃ t : Scalar, op.Witness p q t := by
  have distance : ∃ t : Scalar, 0 ≤ t ∧ t^2 = DistanceRecipe.squared p q :=
    Scalar.rootOperation_exists .square _
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  cases op with
  | sqrt => exact Scalar.rootOperation_exists .square p.1 h.2
  | cbrt => exact Scalar.rootOperation_exists .cube p.1 trivial
  | distanceX | distanceY => exact distance
  | projectX | projectY | transferX | transferY => exact ⟨0, trivial⟩

/-- Polynomial output condition, checked on the exact objects. -/
def postcondition (op : MeasurementOperation) (output : Nat) : Condition :=
  let x := ConditionExpr.component 5 .x
  let y := ConditionExpr.component 5 .y
  let u := ConditionExpr.component output .x
  let v := ConditionExpr.component output .y
  let zero := ConditionExpr.constant 0 1
  let square (a : ConditionExpr) := ConditionExpr.mul a a
  let magnitude := if op == .distanceY then v else u
  let dx := ConditionExpr.add x (.neg (.component 6 .x))
  let dy := ConditionExpr.add y (.neg (.component 6 .y))
  match op with
  | .projectX => .and (.onXAxis output) (.eq u x)
  | .projectY => .and (.onYAxis output) (.eq v y)
  | .transferX => .and (.onYAxis output) (.eq v x)
  | .transferY => .and (.onXAxis output) (.eq u y)
  | .sqrt => .and (.onXAxis output) (.and (.le zero u) (.eq (square u) x))
  | .cbrt => .and (.onXAxis output) (.eq (.mul (square u) u) x)
  | .distanceX | .distanceY =>
    .and (if op == .distanceY then .onYAxis output else .onXAxis output)
      (.and (.le zero magnitude) (.eq (square magnitude) (.add (square dx) (square dy))))

end MeasurementOperation

/-- For a nonvertical crease, this polynomial sign is the sign of its slope.
The fold relation itself rules out vertical root creases. -/
def nonnegativeSlope (index : Nat) : Condition :=
  .le (.constant 0 1) (.neg (.mul (.component index .a) (.component index .b)))

/-- Erase a representative's geometry and enforce fresh exact branch choices. -/
def measurementTemplate (op : MeasurementOperation) : RecipeTemplate := Id.run do
  let representative := op.recipe ((1 : ℚ), 0) (0, 0) 1
  let steps := representative.steps.map RecipeOperation.ofInstruction
  let operandName := if op == .sqrt || op == .cbrt then "Scalar (x, 0)" else "Input point P"
  let parameters := RecipeFrame.parameters ++ #[⟨operandName, .point⟩, ⟨"Input point Q", .point⟩]
  let mut requirements := RecipeFrame.requirements
  if op == .sqrt || op == .cbrt then requirements := requirements.push (.onXAxis 5)
  if op == .sqrt then
    requirements := requirements.push (.le (.constant 0 1) (.component 5 .x))
  let mut checks : Array RecipeRequirement := #[]
  for (step, i) in steps.zipIdx do
    if let .fold (.axiom5 source fixed target) := step then
      let diagonal := source.index == 1 && fixed.index == 0 && target.index == 3
      checks := checks.push ⟨i + 1, 0,
        if diagonal then lineIs (op.arity + i) 1 (-1) 0 else nonnegativeSlope (op.arity + i)⟩
  let output := representative.output.index
  checks := checks.push ⟨steps.length, 0, op.postcondition output⟩
  return {
    parameters := parameters.extract 0 op.arity, steps, output, requirements, checks
    outputs := #[⟨"Result", output⟩] }

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Changing samples and roots preserves the template's operations. -/
theorem measurementTemplate_steps {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (op : MeasurementOperation) (p q : Point K) (t : K) :
    (op.recipe p q t).steps.map RecipeOperation.ofInstruction = (measurementTemplate op).steps := by
  cases op <;> cbv

set_option maxHeartbeats 2000000 in
/-- Template and execution select the same result reference. -/
theorem measurementTemplate_output {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (op : MeasurementOperation) (p q : Point K) (t : K) :
    (op.recipe p q t).output.index = (measurementTemplate op).output := by
  cases op <;> rfl

/-- The polynomial slope test identifies the nonnegative tangent parameter,
including the horizontal crease at zero. -/
theorem root_crease_nonnegative_iff {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (t : K) : 0 ≤ -((RootGeometry.crease t).a * (RootGeometry.crease t).b) ↔ 0 ≤ t := by
  by_cases ht : t = 0
  · simp [ht, RootGeometry.crease, Line.normalize]
  · simp [RootGeometry.crease, Line.normalize, ht, inv_nonneg]

/-- Among legal square-root creases, the exact sign policy admits only the
desired root. It does not depend on the solver's enumeration order. -/
theorem square_root_policy {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (x t : K) (ht : RootOperation.square.Relation x t) (crease : Line K)
    (legal : (FoldInput.axiom5 (0, 1) (0, -x) (Line.horizontal (-1))).Satisfies crease) :
    0 ≤ -(crease.a * crease.b) ↔ crease = RootGeometry.crease t := by
  constructor
  · intro sign
    have alignment := ((FoldInput.axiom5_iff_equations _ _ _ _).mp legal).1
    have shape := RootGeometry.eq_crease_of_first_alignment crease alignment
    have equation := (RootOperation.square_satisfies_iff x (-crease.a / crease.b)).mp
      (shape ▸ legal)
    have nonneg : 0 ≤ -crease.a / crease.b :=
      (root_crease_nonnegative_iff _).mp (shape ▸ sign)
    have equal := RootOperation.Relation.unique (op := .square) ⟨nonneg, equation⟩ ht
    exact shape.trans (congrArg RootGeometry.crease equal)
  · rintro rfl
    exact (root_crease_nonnegative_iff t).mpr ht.1

/-- Cube-root folds have one real crease; no hidden positive-input restriction
or branch-index convention is necessary. -/
theorem cube_root_policy {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (x t : K) (ht : RootOperation.cube.Relation x t) (crease : Line K)
    (legal : (FoldInput.axiom6 (0, 1) (-x, 0) (Line.horizontal (-1))
      (Line.chart 0 x)).Satisfies crease) : crease = RootGeometry.crease t := by
  have alignment := ((FoldInput.axiom6_iff_equations _ _ _ _ _).mp legal).1
  have shape := RootGeometry.eq_crease_of_first_alignment crease alignment
  have equation : RootOperation.cube.Relation x (-crease.a / crease.b) :=
    (RootOperation.cube_satisfies_iff x _).mp (shape ▸ legal)
  exact shape.trans (congrArg RootGeometry.crease (equation.unique ht))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
/-- The successful primitive execution passes the input, branch, and output
conditions used by the visual template. -/
theorem measurementTemplate_checks {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (op : MeasurementOperation) (p q : Point K) (t : K)
    (h : op.Valid p) (w : op.Witness p q t) :
    let r := op.recipe p q t
    let final := op.inputs p q ++ r.steps.map ArithmeticRecipe.selectedObject
    (measurementTemplate op).requirements.all (Condition.checkObjects (op.inputs p q)) = true ∧
      (measurementTemplate op).checks.all (fun check =>
        check.condition.checkObjects (final.take (op.arity + check.before))) = true := by
  cases op
  all_goals
    run_tac Lean.Elab.Tactic.withMainContext do
      let goal ← Lean.Elab.Tactic.getMainGoal
      let target ← Lean.Meta.transform (← goal.getType) (pre := fun e => do
        let type ← Lean.Meta.whnf (← Lean.Meta.inferType e)
        if type.isAppOf ``List || type.isAppOf ``Array then
          return .done (← Lean.Meta.withTransparency .all (Lean.Meta.reduce e))
        return .continue)
      Lean.Elab.Tactic.replaceMainGoal [← goal.change target]
    norm_num [Condition.checkObjects, Condition.check, Condition.valid, ConditionExpr.valid,
      Condition.Holds, ConditionExpr.eval, Component.isPoint, Component.pointAt,
      Component.lineAt, Component.value, MeasurementOperation.Valid,
      MeasurementOperation.Witness, RootOperation.Relation] at *
    all_goals repeat' apply And.intro
    all_goals first
      | assumption
      | rfl
      | exact neg_nonneg.mp ((root_crease_nonnegative_iff t).mpr w.1)
      | (try simp_all [DistanceRecipe.squared, pow_two]
         all_goals nlinarith)

set_option maxHeartbeats 2000000 in
/-- Every accepted completion has the advertised meaning, and every valid
exact input has a successful completion of these same primitives and checks. -/
theorem measurementTemplate_contract (op : MeasurementOperation) :
    RecipeContract (measurementTemplate op)
      (fun p : Point Scalar × Point Scalar => op.inputs p.1 p.2)
      (fun p => op.Valid p.1)
      (op.postcondition (measurementTemplate op).output) := by
  constructor
  · intro parameters _ program final completion
    exact completion.final_condition
      ⟨(measurementTemplate op).steps.length, 0,
        op.postcondition (measurementTemplate op).output⟩
      (by cases op <;> exact Array.mem_push_self) rfl
  · rintro ⟨p, q⟩ h
    obtain ⟨t, witness⟩ := op.witness_exists p q h
    let r := op.recipe p q t
    refine ⟨r.steps, op.inputs p q ++ r.steps.map ArithmeticRecipe.selectedObject,
      measurementTemplate_steps op p q t, (op.computes p q t h witness).1, ?_,
      (measurementTemplate_checks op p q t h witness).1, ?_, ?_⟩
    · have shape := congrArg List.length (measurementTemplate_steps op p q t)
      simpa [r] using congrArg (fun n => (op.inputs p q).length + n) shape
    · have checks := (measurementTemplate_checks op p q t h witness).2
      cases op <;> simpa [MeasurementOperation.inputs, MeasurementOperation.arity,
        CoordinateOperation.inputs, DistanceRecipe.inputs, r] using checks
    · cases op <;> constructor <;> rfl

/-- An edited template cannot retain a built-in specification badge. -/
def measurementSpecification (recipe : RecipeTemplate) : Option String := do
  let operations : List MeasurementOperation :=
    [.projectX, .projectY, .transferX, .transferY, .distanceX, .distanceY, .sqrt, .cbrt]
  let op ← operations.find? fun op => (measurementTemplate op).source == recipe.source
  return conditionDescription (fun i => (recipe.parameters[i]?.map (·.name)).getD
    (if i == recipe.output then "Result" else s!"object {i}")) (op.postcondition recipe.output)

end LeanOrigami.Widget
