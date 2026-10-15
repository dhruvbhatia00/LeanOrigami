import LeanOrigami.Construction.Condition
import LeanOrigami.Geometry.Trisection

/-!
# Polynomial certificates for the two interior trisectors

The root witnesses are references to constructed axis points. Positive lengths,
root intervals, and denominator-cleared endpoint equations make the output
condition imply the full real geometric statement, not just a cubic identity.
-/

namespace LeanOrigami.TrisectionCondition

/-- Exact polynomial contract, independent of a particular recipe's numbering. -/
def condition (vertex first second firstOutput secondOutput : Nat)
    (roots : Trisection.Roots Nat) (cosine : Nat) : Condition :=
  let zero : ConditionExpr := .constant 0 1
  let one : ConditionExpr := .constant 1 1
  let two : ConditionExpr := .constant 2 1
  let three : ConditionExpr := .constant 3 1
  let four : ConditionExpr := .constant 4 1
  let square (x : ConditionExpr) := ConditionExpr.mul x x
  let sub (x y : ConditionExpr) := ConditionExpr.add x (.neg y)
  let dx (i : Nat) (f : Component) := sub (.component i f) (.component vertex f)
  let a : ConditionExpr := .component roots.firstLength .x
  let b : ConditionExpr := .component roots.secondLength .x
  let s : ConditionExpr := .component roots.sine .x
  let t : ConditionExpr := .component roots.thirdCosine .x
  let r : ConditionExpr := .component roots.thirdSine .x
  let c : ConditionExpr := .component cosine .x
  let norm (i : Nat) := ConditionExpr.add (square (dx i .x)) (square (dx i .y))
  let dot := ConditionExpr.add (.mul (dx first .x) (dx second .x))
    (.mul (dx first .y) (dx second .y))
  let endpoint (out : Nat) (u v : ConditionExpr) (f : Component) :=
    Condition.eq (.mul (.mul (.mul a b) s) (dx out f))
      (.add (.mul (.mul (.mul u b) s) (dx first f))
        (.mul v (sub (.mul a (dx second f)) (.mul (.mul b c) (dx first f)))))
  let doubleCosine := sub (.mul two (square t)) one
  let doubleSine := ConditionExpr.mul (.mul two t) r
  [Condition.lt zero a, .eq (square a) (norm first),
    .lt zero b, .eq (square b) (norm second),
    .eq (.mul (.mul a b) c) dot,
    .lt zero s, .eq (square s) (sub one (square c)),
    .lt (.constant 1 2) t, .lt t one,
    .eq (sub (.mul four (.mul (square t) t)) (.mul three t)) c,
    .lt zero r, .eq (square r) (sub one (square t)),
    endpoint firstOutput t r .x, endpoint firstOutput t r .y,
    endpoint secondOutput doubleCosine doubleSine .x,
    endpoint secondOutput doubleCosine doubleSine .y].foldr Condition.and (.eq zero zero)

/-- Interpret a referenced point by its two exact components. Reference validity
is separately enforced by the ordinary condition checker. -/
def point {K : Type*} (value : Nat → Component → K) (i : Nat) : Point K :=
  (value i .x, value i .y)

/-- Interpret the five constructed scalar witnesses. -/
def witnesses {K : Type*} (value : Nat → Component → K) (refs : Trisection.Roots Nat) :
    Trisection.Roots K :=
  ⟨value refs.firstLength .x, value refs.secondLength .x, value refs.sine .x,
    value refs.thirdCosine .x, value refs.thirdSine .x⟩

/-- Clearing the endpoint denominators preserves the exact geometric formulas. -/
theorem sound (value : Nat → Component → ℝ) (vertex first second firstOutput secondOutput : Nat)
    (refs : Trisection.Roots Nat) (cosine : Nat)
    (h : (condition vertex first second firstOutput secondOutput refs cosine).Holds value) :
    Trisection.IsTrisection (point value vertex) (point value first) (point value second)
      (point value firstOutput) (point value secondOutput) := by
  simp only [condition, List.foldr, Condition.Holds, ConditionExpr.eval,
    Int.cast_ofNat, Nat.cast_ofNat, Int.cast_one, Nat.cast_one, div_one, Int.cast_zero,
    and_true, eq_self] at h
  rcases h with ⟨ha, ha2, hb, hb2, hc, hs, hs2, ht, ht1, ht3, hr, hr2, hx, hy, hx2, hy2⟩
  let roots := witnesses value refs
  have ha0 := ne_of_gt ha
  have hb0 := ne_of_gt hb
  have hs0 := ne_of_gt hs
  have hcos : roots.cosine (point value vertex) (point value first) (point value second) =
      value cosine .x := by
    dsimp [roots, witnesses, Trisection.Roots.cosine, Trisection.unitVector, point, Point.dot]
    field_simp
    nlinarith only [hc]
  have valid : roots.Valid (point value vertex) (point value first) (point value second) := by
    unfold Trisection.Roots.Valid
    rw [hcos]
    dsimp [roots, witnesses, point, Point.sqNorm]
    refine ⟨ha, ?_, hb, ?_, hs, ?_, ht, ht1, ?_, hr, ?_⟩ <;>
      nlinarith only [ha2, hb2, hs2, ht3, hr2]
  have firstEq : point value firstOutput =
      roots.firstPoint (point value vertex) (point value first) (point value second) := by
    unfold Trisection.Roots.firstPoint Trisection.Roots.perpendicularUnit
    rw [hcos]
    apply Prod.ext <;>
      dsimp [Trisection.unitVector, roots, witnesses, point] <;>
      field_simp <;> nlinarith only [hx, hy]
  have secondEq : point value secondOutput =
      roots.secondPoint (point value vertex) (point value first) (point value second) := by
    unfold Trisection.Roots.secondPoint Trisection.Roots.perpendicularUnit
    rw [hcos]
    apply Prod.ext <;>
      dsimp [Trisection.unitVector, roots, witnesses, point] <;>
      field_simp <;> nlinarith only [hx2, hy2]
  rw [firstEq, secondEq]
  exact roots.isTrisection _ _ _ valid

end LeanOrigami.TrisectionCondition
