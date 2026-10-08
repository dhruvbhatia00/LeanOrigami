import LeanOrigami.Folds

/-!
# Mathematical construction histories

Only the two initial points, legal folds on previously constructed inputs,
and unique intersections generate constructible objects. These rules are
independent of program execution and already cover all seven fold relations.
-/

namespace LeanOrigami

/-- A construction produces either a point or a line. -/
inductive Object (K : Type*) [Zero K] [One K] where
  | point (value : Point K)
  | line (value : Line K)
  deriving DecidableEq

namespace FoldInput
/-- The geometric objects required by a fold, in their input order. -/
def objects {K : Type*} [Zero K] [One K] : FoldInput K → List (Object K)
  | .axiom1 p q | .axiom2 p q => [.point p, .point q]
  | .axiom3 l m => [.line l, .line m]
  | .axiom4 p l => [.point p, .line l]
  | .axiom5 p q l => [.point p, .point q, .line l]
  | .axiom6 p q l m => [.point p, .point q, .line l, .line m]
  | .axiom7 p l m => [.point p, .line l, .line m]

/-- Every input has the required provenance. -/
def Available {K : Type*} [Zero K] [One K]
    (available : Object K → Prop) (input : FoldInput K) : Prop :=
  ∀ o ∈ input.objects, available o
end FoldInput

/-- Objects obtainable from the two seeds by finite-choice folds and unique intersections.
The recursive input evidence records provenance; arbitrary coordinates are not seeds. -/
inductive Constructible : Object ℝ → Prop where
  | origin : Constructible (.point (0, 0))
  | unit : Constructible (.point (1, 0))
  | fold (input : FoldInput ℝ) (crease : Line ℝ)
      (inputs : ∀ o ∈ input.objects, Constructible o) (legal : input.Legal crease) :
      Constructible (.line crease)
  | intersection (l m : Line ℝ) (p : Point ℝ)
      (left : Constructible (.line l)) (right : Constructible (.line m))
      (unique : LegalIntersection l m p) : Constructible (.point p)

/-- A number is constructed by selecting either coordinate of a constructed point. -/
def ConstructibleNumber (x : ℝ) : Prop :=
  ∃ p : Point ℝ, Constructible (.point p) ∧ (x = p.1 ∨ x = p.2)

end LeanOrigami
