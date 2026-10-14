import LeanOrigami.Construction.Program
import Lean.Data.Json.FromToJson

/-!
# Exact polynomial conditions

Conditions use coordinates and canonical line coefficients, rational constants,
and polynomial arithmetic. They contain no Lean expressions or approximate
numbers. Reference and denominator validity is checked before Boolean logic,
so negating a malformed condition never makes it acceptable.
-/

namespace LeanOrigami

/-- A typed component of a geometric object. Lines use their canonical coefficients. -/
inductive Component where
  | x | y | a | b | c
  deriving BEq, Repr, Lean.ToJson, Lean.FromJson

/-- Whether a component belongs to a point (rather than a line). -/
def Component.isPoint : Component → Bool
  | .x | .y => true
  | _ => false

/-- An exact polynomial expression. A rational constant requires a positive denominator. -/
inductive ConditionExpr where
  | constant (numerator : Int) (denominator : Nat)
  | component (index : Nat) (field : Component)
  | add (left right : ConditionExpr)
  | mul (left right : ConditionExpr)
  | neg (value : ConditionExpr)
  deriving Repr, Lean.ToJson, Lean.FromJson

/-- Typed reference requirements and rational-denominator validity. -/
def ConditionExpr.valid (pointAt lineAt : Nat → Bool) : ConditionExpr → Bool
  | .constant _ d => d != 0
  | .component i f => if f.isPoint then pointAt i else lineAt i
  | .add a b | .mul a b => a.valid pointAt lineAt && b.valid pointAt lineAt
  | .neg a => a.valid pointAt lineAt

/-- Polynomial interpretation in a field, with explicit component values. -/
def ConditionExpr.eval {K : Type*} [Field K] (value : Nat → Component → K) : ConditionExpr → K
  | .constant n d => (n : K) / (d : K)
  | .component i f => value i f
  | .add a b => a.eval value + b.eval value
  | .mul a b => a.eval value * b.eval value
  | .neg a => -(a.eval value)

/-- Relocate all object references without changing the polynomial. -/
def ConditionExpr.remap (f : Nat → Nat) : ConditionExpr → ConditionExpr
  | .constant n d => .constant n d
  | .component i field => .component (f i) field
  | .add a b => .add (a.remap f) (b.remap f)
  | .mul a b => .mul (a.remap f) (b.remap f)
  | .neg a => .neg (a.remap f)

/-- Polynomial interpretation commutes with field embeddings. -/
theorem ConditionExpr.eval_map {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (value : Nat → Component → K) (e : ConditionExpr) :
    e.eval (fun i field => f (value i field)) = f (e.eval value) := by
  induction e with
  | constant n d => simp [eval]
  | component i field => rfl
  | add a b ha hb => simp [eval, ha, hb]
  | mul a b ha hb => simp [eval, ha, hb]
  | neg a ha => simp [eval, ha]

/-- Finite Boolean combinations of polynomial comparisons. Geometric families
expand into this one language rather than maintaining separate checkers. -/
inductive Condition where
  | eq (left right : ConditionExpr)
  | le (left right : ConditionExpr)
  | lt (left right : ConditionExpr)
  | and (left right : Condition)
  | or (left right : Condition)
  | not (condition : Condition)
  deriving Repr, Lean.ToJson, Lean.FromJson

/-- Validate every branch, including branches not needed by short-circuit evaluation. -/
def Condition.valid (pointAt lineAt : Nat → Bool) : Condition → Bool
  | .eq a b | .le a b | .lt a b => a.valid pointAt lineAt && b.valid pointAt lineAt
  | .and a b | .or a b => a.valid pointAt lineAt && b.valid pointAt lineAt
  | .not a => a.valid pointAt lineAt

/-- Mathematical meaning of a well-formed formula. -/
def Condition.Holds {K : Type*} [Field K] [LinearOrder K]
    (value : Nat → Component → K) : Condition → Prop
  | .eq a b => a.eval value = b.eval value
  | .le a b => a.eval value ≤ b.eval value
  | .lt a b => a.eval value < b.eval value
  | .and a b => a.Holds value ∧ b.Holds value
  | .or a b => a.Holds value ∨ b.Holds value
  | .not a => ¬a.Holds value

instance instDecidableHolds {K : Type*} [Field K] [LinearOrder K] (value : Nat → Component → K) :
    (condition : Condition) → Decidable (condition.Holds value)
  | .eq a b => inferInstanceAs (Decidable (a.eval value = b.eval value))
  | .le a b => inferInstanceAs (Decidable (a.eval value ≤ b.eval value))
  | .lt a b => inferInstanceAs (Decidable (a.eval value < b.eval value))
  | .and a b => @instDecidableAnd _ _ (instDecidableHolds value a) (instDecidableHolds value b)
  | .or a b => @instDecidableOr _ _ (instDecidableHolds value a) (instDecidableHolds value b)
  | .not a => @instDecidableNot _ (instDecidableHolds value a)

/-- Exact decision, including validity. No classical decision or real-number
interpretation is involved in execution. -/
def Condition.check {K : Type*} [Field K] [LinearOrder K]
    (pointAt lineAt : Nat → Bool) (value : Nat → Component → K) (condition : Condition) : Bool :=
  condition.valid pointAt lineAt && decide (condition.Holds value)

/-- Acceptance is exactly well-formedness and the stated polynomial relation. -/
theorem Condition.check_iff {K : Type*} [Field K] [LinearOrder K]
    (pointAt lineAt : Nat → Bool) (value : Nat → Component → K) (condition : Condition) :
    condition.check pointAt lineAt value = true ↔
      condition.valid pointAt lineAt = true ∧ condition.Holds value := by
  simp [check]

/-- The meaning is unchanged by an order-preserving field embedding, in
particular by the exact scalar embedding into Mathlib's real numbers. -/
theorem Condition.holds_map {K L : Type*} [Field K] [LinearOrder K]
    [Field L] [LinearOrder L] (f : K →+* L)
    (hle : ∀ a b, f a ≤ f b ↔ a ≤ b) (hlt : ∀ a b, f a < f b ↔ a < b)
    (value : Nat → Component → K) (condition : Condition) :
    condition.Holds (fun i field => f (value i field)) ↔ condition.Holds value := by
  induction condition with
  | eq a b => simp only [Holds, ConditionExpr.eval_map, f.injective.eq_iff]
  | le a b => simp only [Holds, ConditionExpr.eval_map, hle]
  | lt a b => simp only [Holds, ConditionExpr.eval_map, hlt]
  | and a b ha hb => simp only [Holds, ha, hb]
  | or a b ha hb => simp only [Holds, ha, hb]
  | not a ha => simp only [Holds, ha]

/-- Relocate a condition when expanding a nested recipe. -/
def Condition.remap (f : Nat → Nat) : Condition → Condition
  | .eq a b => .eq (a.remap f) (b.remap f)
  | .le a b => .le (a.remap f) (b.remap f)
  | .lt a b => .lt (a.remap f) (b.remap f)
  | .and a b => .and (a.remap f) (b.remap f)
  | .or a b => .or (a.remap f) (b.remap f)
  | .not a => .not (a.remap f)

/-- Read components only after validity checks. Zero on invalid references is
an implementation convenience; `checkObjects` rejects those references first. -/
def Component.value {K : Type*} [Field K] (objects : List (Object K))
    (index : Nat) (field : Component) : K :=
  match objects[index]?, field with
  | some (.point p), .x => p.1
  | some (.point p), .y => p.2
  | some (.line l), .a => l.a
  | some (.line l), .b => l.b
  | some (.line l), .c => l.c
  | _, _ => 0

/-- Identify valid typed references without inspecting numerical values. -/
def Component.pointAt {K : Type*} [Field K] (objects : List (Object K)) (i : Nat) : Bool :=
  match objects[i]? with | some (.point _) => true | _ => false

/-- Identify valid line references. -/
def Component.lineAt {K : Type*} [Field K] (objects : List (Object K)) (i : Nat) : Bool :=
  match objects[i]? with | some (.line _) => true | _ => false

/-- Check a condition against exact geometric objects. -/
def Condition.checkObjects {K : Type*} [Field K] [LinearOrder K]
    (objects : List (Object K)) (condition : Condition) : Bool :=
  condition.check (Component.pointAt objects) (Component.lineAt objects) (Component.value objects)

/-- Exact geometry interpretation: references exist with their stated kinds and
canonical coordinates satisfy the formula. -/
def Condition.Satisfied {K : Type*} [Field K] [LinearOrder K]
    (objects : List (Object K)) (condition : Condition) : Prop :=
  condition.valid (Component.pointAt objects) (Component.lineAt objects) = true ∧
    condition.Holds (Component.value objects)

/-- The object-level API cannot turn invalid references into successful checks. -/
theorem Condition.checkObjects_iff {K : Type*} [Field K] [LinearOrder K]
    (objects : List (Object K)) (condition : Condition) :
    condition.checkObjects objects = true ↔ condition.Satisfied objects :=
  condition.check_iff _ _ _

/-- Reading exact coordinates commutes with interpretation in another field. -/
theorem Component.value_map {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (objects : List (Object K)) (index : Nat) (field : Component) :
    Component.value (objects.map (Object.map f)) index field =
      f (Component.value objects index field) := by
  simp only [Component.value, List.getElem?_map]
  cases h : objects[index]? with
  | none => cases field <;> simp [map_zero]
  | some object => cases object <;> cases field <;> simp [Object.map, Line.map]

/-- The object checker agrees with geometry in any ordered extension field.
Instantiate with `Scalar.realHom`, `Scalar.toReal_le`, and `Scalar.toReal_lt`
to obtain the Mathlib-real interpretation without executing real arithmetic. -/
theorem Condition.checkObjects_map_iff {K L : Type*} [Field K] [LinearOrder K]
    [Field L] [LinearOrder L] (f : K →+* L)
    (hle : ∀ a b, f a ≤ f b ↔ a ≤ b) (hlt : ∀ a b, f a < f b ↔ a < b)
    (objects : List (Object K)) (condition : Condition) :
    condition.checkObjects objects = true ↔
      condition.Satisfied (objects.map (Object.map f)) := by
  have hp : Component.pointAt (objects.map (Object.map f)) = Component.pointAt objects := by
    funext i
    simp only [Component.pointAt, List.getElem?_map]
    cases objects[i]? with
    | none => rfl
    | some object => cases object <;> rfl
  have hl : Component.lineAt (objects.map (Object.map f)) = Component.lineAt objects := by
    funext i
    simp only [Component.lineAt, List.getElem?_map]
    cases objects[i]? with
    | none => rfl
    | some object => cases object <;> rfl
  have hv : Component.value (objects.map (Object.map f)) =
      fun i field => f (Component.value objects i field) := by
    funext i field
    exact Component.value_map f objects i field
  rw [Condition.checkObjects_iff, Condition.Satisfied, Condition.Satisfied, hp, hl, hv,
    Condition.holds_map f hle hlt]

namespace Condition

private def zero : ConditionExpr := .constant 0 1
private def sub (a b : ConditionExpr) : ConditionExpr := .add a (.neg b)

/-- Equality of both point coordinates. Negate this for distinct points. -/
def samePoint (p q : Nat) : Condition :=
  .and (.eq (.component p .x) (.component q .x)) (.eq (.component p .y) (.component q .y))

/-- Equality of canonical line equations, hence geometric line equality. -/
def sameLine (l m : Nat) : Condition :=
  .and (.eq (.component l .a) (.component m .a))
    (.and (.eq (.component l .b) (.component m .b)) (.eq (.component l .c) (.component m .c)))

/-- Incidence in the canonical equation `a*x + b*y = c`. -/
def onLine (p l : Nat) : Condition :=
  .eq (.add (.mul (.component l .a) (.component p .x))
    (.mul (.component l .b) (.component p .y))) (.component l .c)

/-- Incidence on a coordinate axis. -/
def onXAxis (p : Nat) : Condition := .eq (.component p .y) zero

/-- Incidence on the vertical coordinate axis. -/
def onYAxis (p : Nat) : Condition := .eq (.component p .x) zero

/-- Vanishing signed area; repeated points are collinear by convention. -/
def collinear (p q r : Nat) : Condition :=
  .eq (.mul (sub (.component q .x) (.component p .x))
      (sub (.component r .y) (.component p .y)))
    (.mul (sub (.component q .y) (.component p .y))
      (sub (.component r .x) (.component p .x)))

/-- Parallel normals; includes coincident lines. Add distinctness when needed. -/
def parallel (l m : Nat) : Condition :=
  .eq (.mul (.component l .a) (.component m .b))
    (.mul (.component l .b) (.component m .a))

/-- Orthogonal normals. Valid lines cannot have a zero normal. -/
def perpendicular (l m : Nat) : Condition :=
  .eq (.add (.mul (.component l .a) (.component m .a))
    (.mul (.component l .b) (.component m .b))) zero

/-- The incidence family expresses the actual geometric relation. -/
theorem onLine_holds {K : Type*} [Field K] [LinearOrder K] (p : Point K) (l : Line K) :
    (onLine 0 1).Holds (Component.value [.point p, .line l]) ↔ l.Contains p := by
  rfl

/-- The perpendicular family expresses the actual geometric relation. -/
theorem perpendicular_holds {K : Type*} [Field K] [LinearOrder K] (l m : Line K) :
    (perpendicular 0 1).Holds (Component.value [.line l, .line m]) ↔ l.Perpendicular m := by
  simp [perpendicular, Holds, ConditionExpr.eval, Component.value, zero, Line.Perpendicular]

/-- Point equality is geometric equality, not a comparison of renderings. -/
theorem samePoint_holds {K : Type*} [Field K] [LinearOrder K] (p q : Point K) :
    (samePoint 0 1).Holds (Component.value [.point p, .point q]) ↔ p = q := by
  simp [samePoint, Holds, ConditionExpr.eval, Component.value, Prod.ext_iff]

end Condition

end LeanOrigami
