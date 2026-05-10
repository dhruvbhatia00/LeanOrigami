import Lean
import LeanOrigami.ConstructibleLemmas

/-!
# Elaboration for the first text-based origami tactic

The initial version supports introducing the two base points and closing goals
with the x- or y-coordinate of a known constructible point.
-/

open Lean Meta Elab Tactic

/-! ## Syntax -/

declare_syntax_cat origami_step

syntax "point" ident ":=" "origin" : origami_step
syntax "point" ident ":=" "one" : origami_step
syntax "line" ident ":=" "axiom1" ident ident : origami_step
syntax "line" ident ":=" "axiom2" ident ident : origami_step
syntax "line" ident ":=" "axiom4" ident ident : origami_step
syntax "line" ident ":=" "axiom5_pos" ident ident ident : origami_step
syntax "line" ident ":=" "axiom5_neg" ident ident ident : origami_step
syntax "line" ident ":=" "axiom5_linear" ident ident ident : origami_step
syntax "point" ident ":=" "intersection" ident ident : origami_step
syntax "exact_x" ident : origami_step
syntax "exact_y" ident : origami_step

syntax (name := origamiConstruct) "origami_construct" ppLine origami_step* : tactic

/-! ## Paper state -/

structure PaperPoint where
  name : Name
  expr : Expr
  proof : Expr
  facts : Array (Name × Expr) := #[]

structure PaperLine where
  name : Name
  expr : Expr
  proof : Expr
  validProof : Expr
  facts : Array (Name × Expr) := #[]

structure PaperState where
  points : NameMap PaperPoint
  lines : NameMap PaperLine
  pointOrder : Array Name
  lineOrder : Array Name
  facts : Array (Name × Expr) := #[]

namespace PaperState

def empty : PaperState :=
  { points := {}, lines := {}, pointOrder := #[], lineOrder := #[], facts := #[] }

def insertPoint (st : PaperState) (p : PaperPoint) : PaperState :=
  { st with
    points := st.points.insert p.name p
    pointOrder := st.pointOrder.push p.name }

def insertLine (st : PaperState) (l : PaperLine) : PaperState :=
  { st with
    lines := st.lines.insert l.name l
    lineOrder := st.lineOrder.push l.name }

def findPoint? (st : PaperState) (n : Name) : Option PaperPoint :=
  NameMap.find? st.points n

def findLine? (st : PaperState) (n : Name) : Option PaperLine :=
  NameMap.find? st.lines n

def insertFact (st : PaperState) (n : Name) (e : Expr) : PaperState :=
  { st with facts := st.facts.push (n, e) }

end PaperState

theorem constructible_real_proj_of_eq {x y : ℝ}
    (hxy : x = y) (hx : constructible_real_proj x) :
    constructible_real_proj y := by
  rw [← hxy]
  exact hx

namespace OrigamiTacticAxiom5

def quadraticEval (A B C x : ℝ) : ℝ :=
  A * x ^ 2 + B * x + C

def quadraticDiscriminant (A B C : ℝ) : ℝ :=
  B ^ 2 - 4 * A * C

noncomputable def quadraticRoot (A B C : ℝ) (sign : Bool) : ℝ :=
  if sign then
    (-B + Real.sqrt (quadraticDiscriminant A B C)) / (2 * A)
  else
    (-B - Real.sqrt (quadraticDiscriminant A B C)) / (2 * A)

lemma quadraticRoot_is_root {A B C : ℝ} (hA : A ≠ 0)
    (hdisc : 0 ≤ quadraticDiscriminant A B C) (sign : Bool) :
    quadraticEval A B C (quadraticRoot A B C sign) = 0 := by
  have hdisc' : 0 ≤ B ^ 2 - A * C * 4 := by
    rw [quadraticDiscriminant] at hdisc
    nlinarith
  have hsqrt :
      (Real.sqrt (B ^ 2 - A * C * 4)) ^ 2 = B ^ 2 - A * C * 4 :=
    Real.sq_sqrt hdisc'
  unfold quadraticEval quadraticRoot quadraticDiscriminant
  by_cases hs : sign
  · simp [hs]
    field_simp [hA]
    ring_nf
    nlinarith [hsqrt]
  · simp [hs]
    field_simp [hA]
    ring_nf
    nlinarith [hsqrt]

lemma linearRoot_is_root {B C : ℝ} (hB : B ≠ 0) :
    quadraticEval 0 B C (-C / B) = 0 := by
  simp [quadraticEval]
  field_simp [hB]
  ring

def coeffA (P₁ P₂ : Point) (L₁ : Line) : ℝ :=
  L₁ 0 * (2 * P₂ 0 - P₁ 0) + L₁ 1 * P₁ 1 - L₁ 2

def coeffB (P₁ P₂ : Point) (L₁ : Line) : ℝ :=
  2 * L₁ 0 * (P₁ 1 - P₂ 1) - 2 * L₁ 1 * (P₂ 0 - P₁ 0)

def coeffC (P₁ P₂ : Point) (L₁ : Line) : ℝ :=
  L₁ 0 * P₁ 0 + L₁ 1 * (2 * P₂ 1 - P₁ 1) - L₁ 2

def discriminant (P₁ P₂ : Point) (L₁ : Line) : ℝ :=
  quadraticDiscriminant (coeffA P₁ P₂ L₁) (coeffB P₁ P₂ L₁) (coeffC P₁ P₂ L₁)

def quadraticCase (P₁ P₂ : Point) (L₁ : Line) : Prop :=
  coeffA P₁ P₂ L₁ ≠ 0 ∧ 0 ≤ discriminant P₁ P₂ L₁

def linearCase (P₁ P₂ : Point) (L₁ : Line) : Prop :=
  coeffA P₁ P₂ L₁ = 0 ∧ coeffB P₁ P₂ L₁ ≠ 0

noncomputable def linearRootSlope (P₁ P₂ : Point) (L₁ : Line) : ℝ :=
  -coeffC P₁ P₂ L₁ / coeffB P₁ P₂ L₁

set_option linter.flexible false in
lemma slopeQuadratic_iff_eval (P₁ P₂ : Point) (L₁ : Line) (m : ℝ) :
    Axiom5Spec.slopeQuadratic P₁ P₂ L₁ m ↔
      quadraticEval (coeffA P₁ P₂ L₁) (coeffB P₁ P₂ L₁) (coeffC P₁ P₂ L₁) m = 0 := by
  simp [Axiom5Spec.slopeQuadratic, quadraticEval, coeffA, coeffB, coeffC]
  constructor <;> intro h <;> nlinarith

theorem cons_line_quadraticRoot {P₁ P₂ : Point} {L₁ : Line}
    (hP₁ : cons_point P₁) (hP₂ : cons_point P₂) (hL₁ : cons_line L₁)
    (hcase : quadraticCase P₁ P₂ L₁) (sign : Bool) :
    cons_line
      (point_slope_form
        (some (quadraticRoot (coeffA P₁ P₂ L₁) (coeffB P₁ P₂ L₁) (coeffC P₁ P₂ L₁) sign))
        P₂) := by
  apply cons_line.axiom5 hP₁ hP₂ hL₁
  · exact valid_point_slope_form _ _
  · apply Axiom5Spec.axiom5_of_slopeQuadratic
    apply (slopeQuadratic_iff_eval P₁ P₂ L₁ _).2
    apply quadraticRoot_is_root hcase.1
    simpa [discriminant] using hcase.2

set_option linter.flexible false in
theorem cons_line_linearRoot {P₁ P₂ : Point} {L₁ : Line}
    (hP₁ : cons_point P₁) (hP₂ : cons_point P₂) (hL₁ : cons_line L₁)
    (hcase : linearCase P₁ P₂ L₁) :
    cons_line
      (point_slope_form (some (linearRootSlope P₁ P₂ L₁)) P₂) := by
  apply cons_line.axiom5 hP₁ hP₂ hL₁
  · exact valid_point_slope_form _ _
  · apply Axiom5Spec.axiom5_of_slopeQuadratic
    apply (slopeQuadratic_iff_eval P₁ P₂ L₁ _).2
    simp [linearRootSlope]
    rw [hcase.1]
    exact linearRoot_is_root hcase.2

end OrigamiTacticAxiom5

namespace LeanOrigami.Tactic

private def pointOfConsPointProof (proof : Expr) : MetaM Expr := do
  let proofType ← inferType proof
  let proofType ← whnf proofType
  match proofType with
  | Expr.app (Expr.const ``cons_point _) p => pure p
  | _ =>
      throwError "expected a proof of cons_point, got{indentExpr proofType}"

private def lineOfConsLineProof (proof : Expr) : MetaM Expr := do
  let proofType ← inferType proof
  let proofType ← whnf proofType
  match proofType with
  | Expr.app (Expr.const ``cons_line _) l => pure l
  | _ =>
      throwError "expected a proof of cons_line, got{indentExpr proofType}"

private def addBasePoint
    (st : PaperState) (name : Name) (proofConst : Name) :
    MetaM PaperState := do
  if (st.findPoint? name).isSome then
    throwError "point '{name}' is already defined"
  let proof := mkConst proofConst
  let expr ← pointOfConsPointProof proof
  return st.insertPoint { name, expr, proof }

private def ppExprString (e : Expr) : TacticM String := do
  return toString (← ppExpr e)

private def ppTypeString (e : Expr) : TacticM String := do
  return toString (← liftMetaM <| inferType e >>= ppExpr)

private def paperStateString (st : PaperState) : TacticM String := do
  let mut lines := #["origami paper state"]
  if st.pointOrder.isEmpty then
    lines := lines.push "points: none"
  else
    lines := lines.push "points:"
    for name in st.pointOrder do
      let some p := st.findPoint? name
        | continue
      lines := lines.push s!"  {name} := {← ppExprString p.expr}"
      lines := lines.push s!"    proof : {← ppTypeString p.proof}"
  if st.lineOrder.isEmpty then
    lines := lines.push "lines: none"
  else
    lines := lines.push "lines:"
    for name in st.lineOrder do
      let some l := st.findLine? name
        | continue
      lines := lines.push s!"  {name} := {← ppExprString l.expr}"
      lines := lines.push s!"    proof : {← ppTypeString l.proof}"
      lines := lines.push s!"    valid : {← ppTypeString l.validProof}"
  return "\n".intercalate lines.toList

private def logPaperStateAt (ref : Syntax) (st : PaperState) : TacticM Unit := do
  logInfoAt ref (← paperStateString st)

private def proveSideConditionWith (type : Expr) (tacticCode : Syntax) : TacticM Expr := do
  let mvar ← mkFreshExprMVar (some type)
  let (goals, _) ← liftMetaM <| runTactic mvar.mvarId! tacticCode
  unless goals.isEmpty do
    throwError "side-condition tactic left goals"
  instantiateMVars mvar

private def proveSideCondition (type : Expr) : TacticM Expr := do
  let attempts := #[
    ← `(tactic| simp),
    ← `(tactic| norm_num),
    ← `(tactic| simp [is_transverse, is_parallel,
        Axiom1Spec.lineThrough, Axiom2Spec.perpendicularBisector,
        Axiom4Spec.perpendicularLine, point_slope_form, intersectionPoint,
        OrigamiTacticAxiom5.quadraticCase, OrigamiTacticAxiom5.linearCase,
        OrigamiTacticAxiom5.coeffA, OrigamiTacticAxiom5.coeffB,
        OrigamiTacticAxiom5.coeffC, OrigamiTacticAxiom5.discriminant,
        OrigamiTacticAxiom5.quadraticDiscriminant,
        OrigamiTacticAxiom5.quadraticRoot, OrigamiTacticAxiom5.linearRootSlope]),
    ← `(tactic| simp [is_transverse, is_parallel,
        Axiom1Spec.lineThrough, Axiom2Spec.perpendicularBisector,
        Axiom4Spec.perpendicularLine, point_slope_form, intersectionPoint,
        OrigamiTacticAxiom5.quadraticCase, OrigamiTacticAxiom5.linearCase,
        OrigamiTacticAxiom5.coeffA, OrigamiTacticAxiom5.coeffB,
        OrigamiTacticAxiom5.coeffC, OrigamiTacticAxiom5.discriminant,
        OrigamiTacticAxiom5.quadraticDiscriminant,
        OrigamiTacticAxiom5.quadraticRoot, OrigamiTacticAxiom5.linearRootSlope] <;> norm_num)]
  for tacticCode in attempts do
    try
      return ← proveSideConditionWith type tacticCode
    catch _ =>
      pure ()
  throwError "failed to prove side condition by simp/norm_num:{indentExpr type}"

private def finTwoZero : Expr :=
  toExpr (0 : Fin 2)

private def finTwoOne : Expr :=
  toExpr (1 : Fin 2)

private def addAxiomLine
    (st : PaperState) (name pName qName : Name) (lemmaName : Name) :
    TacticM PaperState := do
  if (st.findLine? name).isSome then
    throwError "line '{name}' is already defined"
  let some p := st.findPoint? pName
    | throwError "unknown point '{pName}'"
  let some q := st.findPoint? qName
    | throwError "unknown point '{qName}'"
  let hsepType ←
    mkAppM ``Or #[
      ← mkAppM ``Ne #[mkApp p.expr finTwoZero, mkApp q.expr finTwoZero],
      ← mkAppM ``Ne #[mkApp p.expr finTwoOne, mkApp q.expr finTwoOne]]
  let hsep ← proveSideCondition hsepType
  let proof ← mkAppM lemmaName #[p.proof, q.proof, hsep]
  let expr ← lineOfConsLineProof proof
  let hvalid ←
    match lemmaName with
    | ``cons_line_axiom1_lineThrough => mkAppM ``valid_lineThrough #[hsep]
    | ``cons_line_axiom2_perpendicularBisector => mkAppM ``valid_perpendicularBisector #[hsep]
    | _ => throwError "internal error: unsupported axiom-line lemma"
  return st.insertLine { name, expr, proof, validProof := hvalid }

private def addAxiom4Line
    (st : PaperState) (name lineName pointName : Name) :
    TacticM PaperState := do
  if (st.findLine? name).isSome then
    throwError "line '{name}' is already defined"
  let some l := st.findLine? lineName
    | throwError "unknown line '{lineName}'"
  let some p := st.findPoint? pointName
    | throwError "unknown point '{pointName}'"
  let proof ← mkAppM ``cons_line_axiom4_perpendicularLine #[l.proof, p.proof, l.validProof]
  let expr ← lineOfConsLineProof proof
  let hvalid := mkAppN (mkConst ``valid_perpendicularLine) #[l.expr, p.expr, l.validProof]
  return st.insertLine { name, expr, proof, validProof := hvalid }

private def mkAxiom5Slope (p q : PaperPoint) (l : PaperLine) (sign : Bool) :
    MetaM Expr := do
  let a ← mkAppM ``OrigamiTacticAxiom5.coeffA #[p.expr, q.expr, l.expr]
  let b ← mkAppM ``OrigamiTacticAxiom5.coeffB #[p.expr, q.expr, l.expr]
  let c ← mkAppM ``OrigamiTacticAxiom5.coeffC #[p.expr, q.expr, l.expr]
  mkAppM ``OrigamiTacticAxiom5.quadraticRoot #[a, b, c, toExpr sign]

private def mkSomeReal (x : Expr) : Expr :=
  mkApp2 (mkConst ``Option.some [Level.zero]) (mkConst ``Real) x

private def addAxiom5QuadraticLine
    (st : PaperState) (name pName qName lineName : Name) (sign : Bool) :
    TacticM PaperState := do
  if (st.findLine? name).isSome then
    throwError "line '{name}' is already defined"
  let some p := st.findPoint? pName
    | throwError "unknown point '{pName}'"
  let some q := st.findPoint? qName
    | throwError "unknown point '{qName}'"
  let some l := st.findLine? lineName
    | throwError "unknown line '{lineName}'"
  let hcaseType ← mkAppM ``OrigamiTacticAxiom5.quadraticCase #[p.expr, q.expr, l.expr]
  let hcase ← proveSideCondition hcaseType
  let proof ← mkAppM ``OrigamiTacticAxiom5.cons_line_quadraticRoot
    #[p.proof, q.proof, l.proof, hcase, toExpr sign]
  let expr ← lineOfConsLineProof proof
  let slope ← mkAxiom5Slope p q l sign
  let hvalid := mkAppN (mkConst ``valid_point_slope_form) #[mkSomeReal slope, q.expr]
  return st.insertLine { name, expr, proof, validProof := hvalid }

private def addAxiom5LinearLine
    (st : PaperState) (name pName qName lineName : Name) :
    TacticM PaperState := do
  if (st.findLine? name).isSome then
    throwError "line '{name}' is already defined"
  let some p := st.findPoint? pName
    | throwError "unknown point '{pName}'"
  let some q := st.findPoint? qName
    | throwError "unknown point '{qName}'"
  let some l := st.findLine? lineName
    | throwError "unknown line '{lineName}'"
  let hcaseType ← mkAppM ``OrigamiTacticAxiom5.linearCase #[p.expr, q.expr, l.expr]
  let hcase ← proveSideCondition hcaseType
  let proof ← mkAppM ``OrigamiTacticAxiom5.cons_line_linearRoot
    #[p.proof, q.proof, l.proof, hcase]
  let expr ← lineOfConsLineProof proof
  let slope ← mkAppM ``OrigamiTacticAxiom5.linearRootSlope #[p.expr, q.expr, l.expr]
  let hvalid := mkAppN (mkConst ``valid_point_slope_form) #[mkSomeReal slope, q.expr]
  return st.insertLine { name, expr, proof, validProof := hvalid }

private def addIntersectionPoint
    (st : PaperState) (name leftName rightName : Name) :
    TacticM PaperState := do
  if (st.findPoint? name).isSome then
    throwError "point '{name}' is already defined"
  let some left := st.findLine? leftName
    | throwError "unknown line '{leftName}'"
  let some right := st.findLine? rightName
    | throwError "unknown line '{rightName}'"
  let htransType ← mkAppM ``is_transverse #[left.expr, right.expr]
  let htrans ← proveSideCondition htransType
  let proof ← mkAppM ``cons_point_intersectionPoint_of_transverse
    #[left.proof, right.proof, htrans]
  let expr ← pointOfConsPointProof proof
  return st.insertPoint { name, expr, proof }

private def exactCoord (st : PaperState) (name : Name) (coord : Nat) : TacticM Unit := do
  let some p := st.findPoint? name
    | throwError "unknown point '{name}'"
  let coordExpr ←
    match coord with
    | 0 => pure (mkApp p.expr finTwoZero)
    | 1 => pure (mkApp p.expr finTwoOne)
    | _ => throwError "internal error: point coordinates are indexed by 0 or 1"
  let proof ←
    match coord with
    | 0 => mkAppM ``constructible_real_of_point_x #[p.proof]
    | 1 => mkAppM ``constructible_real_of_point_y #[p.proof]
    | _ => throwError "internal error: point coordinates are indexed by 0 or 1"
  let target ← getMainTarget
  let targetCoord ←
    match target with
    | Expr.app (Expr.const ``constructible_real_proj _) x => pure x
    | _ =>
        throwError "expected a goal of the form constructible_real_proj x, \
          got{indentExpr target}"
  let hEqType ← mkAppM ``Eq #[coordExpr, targetCoord]
  let hEq ← proveSideCondition hEqType
  let proof ← mkAppM ``constructible_real_proj_of_eq #[hEq, proof]
  closeMainGoal `origami_construct proof

private def evalStep (st : PaperState) : Syntax → TacticM PaperState
  | `(origami_step| point $id:ident := origin) => do
      addBasePoint st id.getId ``cons_point_origin
  | `(origami_step| point $id:ident := one) => do
      addBasePoint st id.getId ``cons_point_one
  | `(origami_step| line $id:ident := axiom1 $p:ident $q:ident) => do
      addAxiomLine st id.getId p.getId q.getId ``cons_line_axiom1_lineThrough
  | `(origami_step| line $id:ident := axiom2 $p:ident $q:ident) => do
      addAxiomLine st id.getId p.getId q.getId ``cons_line_axiom2_perpendicularBisector
  | `(origami_step| line $id:ident := axiom4 $l:ident $p:ident) => do
      addAxiom4Line st id.getId l.getId p.getId
  | `(origami_step| line $id:ident := axiom5_pos $p:ident $q:ident $l:ident) => do
      addAxiom5QuadraticLine st id.getId p.getId q.getId l.getId true
  | `(origami_step| line $id:ident := axiom5_neg $p:ident $q:ident $l:ident) => do
      addAxiom5QuadraticLine st id.getId p.getId q.getId l.getId false
  | `(origami_step| line $id:ident := axiom5_linear $p:ident $q:ident $l:ident) => do
      addAxiom5LinearLine st id.getId p.getId q.getId l.getId
  | `(origami_step| point $id:ident := intersection $l:ident $m:ident) => do
      addIntersectionPoint st id.getId l.getId m.getId
  | `(origami_step| exact_x $id:ident) => do
      exactCoord st id.getId 0
      return st
  | `(origami_step| exact_y $id:ident) => do
      exactCoord st id.getId 1
      return st
  | _ => throwUnsupportedSyntax

elab_rules : tactic
  | `(tactic| origami_construct $steps:origami_step*) => do
      let mut st := PaperState.empty
      for step in steps do
        st ← withRef step <| evalStep st step
        logPaperStateAt step st

end LeanOrigami.Tactic

/-! ## Examples

Small examples live here while the tactic is under active development.  Keeping
the syntax, elaborator, and examples in one file avoids stale imports during the
hackathon loop; we can split this back out once the interface settles.
-/

example : constructible_real_proj 0 := by
  origami_construct
    point O := origin
    exact_x O

example : constructible_real_proj 0 := by
  origami_construct
    point O := origin
    exact_y O

example : constructible_real_proj 1 := by
  origami_construct
    point I := one
    exact_x I

example : constructible_real_proj 0 := by
  origami_construct
    point I := one
    exact_y I

example : constructible_real_proj 0 := by
  origami_construct
    point O := origin
    point I := one
    line l := axiom1 O I
    exact_x O

example : constructible_real_proj 1 := by
  origami_construct
    point O := origin
    point I := one
    line l := axiom2 O I
    exact_x I

example : constructible_real_proj 0 := by
  origami_construct
    point O := origin
    point I := one
    line xAxis := axiom1 O I
    line yAxis := axiom4 xAxis O
    point X := intersection xAxis yAxis
    exact_x X

example : constructible_real_proj 0 := by
  origami_construct
    point O := origin
    point I := one
    line xAxis := axiom1 O I
    line yAxis := axiom4 xAxis O
    point X := intersection xAxis yAxis
    exact_y X

example : constructible_real_proj (1 / 2 : ℝ) := by
  origami_construct
    point O := origin
    point I := one
    line xAxis := axiom1 O I
    line halfLine := axiom2 O I
    point H := intersection xAxis halfLine
    exact_x H

example : constructible_real_proj (1 / 4 : ℝ) := by
  origami_construct
    point O := origin
    point I := one
    line xAxis := axiom1 O I
    line halfLine := axiom2 O I
    point H := intersection xAxis halfLine
    line quarterLine := axiom2 O H
    point Q := intersection xAxis quarterLine
    exact_x Q

example : constructible_real_proj (3 / 4 : ℝ) := by
  origami_construct
    point O := origin
    point I := one
    line xAxis := axiom1 O I
    line halfLine := axiom2 O I
    point H := intersection xAxis halfLine
    line threeQuarterLine := axiom2 H I
    point T := intersection xAxis threeQuarterLine
    exact_x T

example : constructible_real_proj 0 := by
  origami_construct
    point O := origin
    point I := one
    line xAxis := axiom1 O I
    line fold := axiom5_linear O I xAxis
    exact_y O

example : constructible_real_proj 0 := by
  origami_construct
    point O := origin
    point I := one
    line xAxis := axiom1 O I
    line yAxis := axiom4 xAxis O
    line fold := axiom5_pos I O yAxis
    exact_y O

/-!
Next examples to enable:

```lean
example : constructible_real_proj 0 := by
  origami_construct
    point O := origin
    point I := one
    line xAxis := axiom1 O I
    line yAxis := axiom4 xAxis O
    point X := intersection yAxis xAxis
    exact_x X
```

The natural next stress target is:

```lean
example : constructible_real_proj (2 : ℝ) := by
  origami_construct
    ...
```

With only axioms 1, 2, 4, and intersections, starting from `0` and `1`, the
current DSL easily builds dyadic subdivision points on the x-axis but does not
yet have an operation that extrapolates to `2`.  This should become reachable
after we add a derived construction macro or one of the richer fold axioms.

Planned unsupported commands:

* explicit proof blocks for side conditions automation cannot close
* polynomial/root-based folds for axioms 3, 5, 6, and 7
-/
