import LeanOrigami.Folds

/-!
# Unique crease solutions for rules 1, 2, and 4

The formulas work over ordered fields. Completeness and finite-choice
admissibility are stated over all real creases, independently of execution.
-/

namespace LeanOrigami
namespace Line
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The perpendicular bisector of two distinct points. -/
def bisector (p q : Point K) (h : p ≠ q) : Line K :=
  normalize (q.1-p.1) (q.2-p.2)
    ((q.1^2+q.2^2-p.1^2-p.2^2)/2) (by
      by_contra hn
      push Not at hn
      exact h (Prod.ext (sub_eq_zero.mp hn.1).symm (sub_eq_zero.mp hn.2).symm))

/-- The perpendicular through a point, including points on the input line. -/
def perpendicularThrough (p : Point K) (l : Line K) : Line K :=
  normalize (-l.b) l.a (-l.b*p.1+l.a*p.2) (by
    rcases l.normal_ne_zero with h | h
    · exact Or.inr h
    · exact Or.inl (neg_ne_zero.mpr h))

/-- Points on the bisector have exactly equal squared distances to its inputs. -/
theorem contains_bisector (p q r : Point K) (h : p ≠ q) :
    (bisector p q h).Contains r ↔ distanceSq r p = distanceSq r q := by
  rw [bisector, contains_normalize]
  dsimp [distanceSq]
  constructor <;> intro hr <;> nlinarith

/-- The computed bisector reflects the first point onto the second. -/
theorem bisector_reflect (p q : Point K) (h : p ≠ q) :
    (bisector p q h).reflect p = q := by
  have hn : (q.1-p.1)^2+(q.2-p.2)^2 ≠ 0 := by
    intro hz
    have hx : q.1-p.1 = 0 := by nlinarith [sq_nonneg (q.2-p.2)]
    have hy : q.2-p.2 = 0 := by nlinarith [sq_nonneg (q.1-p.1)]
    exact h (Prod.ext (sub_eq_zero.mp hx).symm (sub_eq_zero.mp hy).symm)
  by_cases hx : q.1-p.1 = 0
  · have hy : q.2-p.2 ≠ 0 := by intro hy; simp [hx, hy] at hn
    have heq : q.1 = p.1 := sub_eq_zero.mp hx
    apply Prod.ext <;> simp [bisector, normalize, hx, reflect, residual, normalSq]
    · exact heq.symm
    · rw [heq]
      field_simp
      ring
  · apply Prod.ext <;> simp only [bisector, normalize, hx, ite_false, reflect, residual,
      normalSq, one_mul, one_pow]
    all_goals field_simp
    all_goals nlinarith

/-- A line contained in another valid line is the same line. -/
theorem eq_of_contains_imp (l m : Line K) (h : ∀ p, l.Contains p → m.Contains p) : l = m := by
  rcases l.normalized with ha | ⟨ha, hb⟩
  · apply eq_of_common_points l m (l.c, 0) (l.c-l.b, 1)
    · intro heq; have := congrArg Prod.snd heq; simp at this
    · simp [Contains, ha]
    · simp [Contains, ha]
    · exact h _ (by simp [Contains, ha])
    · exact h _ (by simp [Contains, ha])
  · apply eq_of_common_points l m (0, l.c) (1, l.c)
    · intro heq; have := congrArg Prod.fst heq; simp at this
    · simp [Contains, ha, hb]
    · simp [Contains, ha, hb]
    · exact h _ (by simp [Contains, ha, hb])
    · exact h _ (by simp [Contains, ha, hb])

/-- Any real reflection carrying distinct points to one another is their bisector. -/
theorem bisector_unique (p q : Point K) (h : p ≠ q) (l : Line K)
    (hl : l.reflect p = q) : l = bisector p q h := by
  apply eq_of_contains_imp
  intro r hr
  apply (contains_bisector p q r h).mpr
  have hd := l.distanceSq_reflect r p
  rw [(l.reflect_eq_self r).mpr hr, hl] at hd
  exact hd.symm

/-- The computed perpendicular passes through its requested point. -/
theorem perpendicularThrough_mem (p : Point K) (l : Line K) :
    (perpendicularThrough p l).Contains p := by
  simp [perpendicularThrough]

/-- The computed perpendicular has the required direction. -/
theorem perpendicularThrough_perpendicular (p : Point K) (l : Line K) :
    (perpendicularThrough p l).Perpendicular l := by
  by_cases hb : l.b = 0
  · simp [perpendicularThrough, normalize, hb, Perpendicular]
  · simp [perpendicularThrough, normalize, hb, Perpendicular]
    field_simp
    ring

/-- Two perpendiculars to the same line with a shared point coincide. -/
theorem perpendicular_unique (p : Point K) (l m n : Line K)
    (hm : m.Contains p) (hn : n.Contains p)
    (hml : m.Perpendicular l) (hnl : n.Perpendicular l) : m = n := by
  apply eq_of_determinant_zero_of_mem m n _ p hm hn
  dsimp [Perpendicular] at hml hnl
  dsimp [determinant]
  rcases l.normal_ne_zero with ha | hb
  · apply (mul_eq_zero.mp (show (m.a*n.b-n.a*m.b)*l.a = 0 by
      linear_combination n.b*hml-m.b*hnl)).resolve_right ha
  · apply (mul_eq_zero.mp (show (m.a*n.b-n.a*m.b)*l.b = 0 by
      linear_combination m.a*hnl-n.a*hml)).resolve_right hb

/-- The computed perpendicular is the only possible crease for rule 4. -/
theorem perpendicularThrough_unique (p : Point K) (l m : Line K)
    (hp : m.Contains p) (hl : m.Perpendicular l) : m = perpendicularThrough p l :=
  perpendicular_unique p l m _ hp (perpendicularThrough_mem p l) hl
    (perpendicularThrough_perpendicular p l)

end Line
namespace FoldInput

/-- Rule 2 has precisely one real solution when its points differ. -/
theorem axiom2_solutions (p q : Point ℝ) (h : p ≠ q) :
    (axiom2 p q).solutions = {Line.bisector p q h} := by
  ext l
  constructor
  · exact fun hl => Line.bisector_unique p q h l hl
  · intro hl
    have heq : l = Line.bisector p q h := hl
    subst l
    exact Line.bisector_reflect p q h

/-- Rule 2's executable distinctness guard exactly captures admissibility. -/
theorem axiom2_admissible_iff (p q : Point ℝ) : (axiom2 p q).Admissible ↔ p ≠ q := by
  constructor
  · intro h heq
    subst q
    exact axiom2_same_not_admissible p h
  · intro h
    unfold Admissible
    rw [axiom2_solutions p q h]
    exact Set.finite_singleton _

/-- Rule 4 always has exactly one real solution. -/
theorem axiom4_solutions (p : Point ℝ) (l : Line ℝ) :
    (axiom4 p l).solutions = {Line.perpendicularThrough p l} := by
  ext m
  constructor
  · exact fun hm => Line.perpendicularThrough_unique p l m hm.1 hm.2
  · intro hm
    have heq : m = Line.perpendicularThrough p l := hm
    subst m
    exact ⟨Line.perpendicularThrough_mem p l, Line.perpendicularThrough_perpendicular p l⟩

/-- There is no exceptional invalid point position in rule 4. -/
theorem axiom4_admissible (p : Point ℝ) (l : Line ℝ) : (axiom4 p l).Admissible := by
  unfold Admissible
  rw [axiom4_solutions]
  exact Set.finite_singleton _

end FoldInput
end LeanOrigami
