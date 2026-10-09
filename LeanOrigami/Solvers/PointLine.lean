import LeanOrigami.Solvers.Basic
import LeanOrigami.Algebra.LowDegree

/-!
# Rule 5 through landing points

Reflecting a source while fixing another point preserves their distance.
The possible landing points therefore lie on a circle and the target line.
When the two input points differ, each landing point determines one crease,
even when the landing point is the source itself.
-/

namespace LeanOrigami
namespace Line
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Parameterize every point of a canonical line without a square root. -/
def pointAt (l : Line K) (t : K) : Point K :=
  if l.a = 0 then (t, l.c) else (l.c - l.b * t, t)

/-- Parameter values always give points on the line. -/
theorem pointAt_mem (l : Line K) (t : K) : l.Contains (l.pointAt t) := by
  rcases l.normalized with ha | ⟨ha, hb⟩
  · simp [pointAt, ha, Contains]
  · simp [pointAt, ha, hb, Contains]

/-- Every point on the line is represented in its parameterization. -/
theorem exists_pointAt (l : Line K) (p : Point K) (h : l.Contains p) :
    ∃ t, l.pointAt t = p := by
  rcases l.normalized with ha | ⟨ha, hb⟩
  · refine ⟨p.2, ?_⟩
    simp only [Contains, ha, one_mul] at h
    simp only [pointAt, ha, one_ne_zero, ite_false]
    exact Prod.ext (by linarith) rfl
  · refine ⟨p.1, ?_⟩
    simp only [Contains, ha, hb, zero_mul, one_mul, zero_add] at h
    simp only [pointAt, ha, ite_true]
    exact Prod.ext rfl h.symm

/-- The circle/line equation, in increasing coefficient order for exact root search. -/
def circleCoefficients (l : Line K) (q : Point K) (radiusSq : K) : List K :=
  if l.a = 0 then [q.1^2+(q.2-l.c)^2-radiusSq, -2*q.1, 1]
  else [(q.1-l.c)^2+q.2^2-radiusSq, 2*((q.1-l.c)*l.b-q.2), 1+l.b^2]

omit [IsStrictOrderedRing K] in
/-- The encoded polynomial vanishes exactly at circle/line landing points. -/
theorem circleCoefficients_eval (l : Line K) (q : Point K) (radiusSq t : K) :
    (l.circleCoefficients q radiusSq).foldr (fun a value => a+t*value) 0 =
      distanceSq q (l.pointAt t) - radiusSq := by
  by_cases ha : l.a = 0 <;>
    simp only [circleCoefficients, pointAt, ha, ite_true, ite_false,
      List.foldr_cons, List.foldr_nil, distanceSq] <;> ring

/-- Its leading coefficient is positive, so this equation is never the zero polynomial. -/
theorem circleCoefficients_leading_pos (l : Line K) (q : Point K) (radiusSq : K) :
    0 < (l.circleCoefficients q radiusSq).getD 2 0 := by
  by_cases ha : l.a = 0
  · simp [circleCoefficients, ha]
  · simp only [circleCoefficients, ha, ite_false, List.getD_cons_succ, List.getD_cons_zero]
    positivity

/-- A line meets a circle in at most two points, also for zero or impossible radii. -/
theorem circle_intersection_subset_pair (l : Line K) (q : Point K) (radiusSq : K) :
    ∃ r s : Point K, ∀ p, l.Contains p → distanceSq q p = radiusSq → p = r ∨ p = s := by
  have hparams : ∃ r s : K, ∀ t, distanceSq q (l.pointAt t) = radiusSq → t = r ∨ t = s := by
    rcases l.normalized with ha | ⟨ha, hb⟩
    · have hn : 1 + l.b^2 ≠ 0 := by nlinarith [sq_nonneg l.b]
      obtain ⟨r, s, hrs⟩ := Univariate.quadratic_zeros_subset_pair (1+l.b^2)
        (2*((q.1-l.c)*l.b-q.2)) ((q.1-l.c)^2+q.2^2-radiusSq) (Or.inl hn)
      refine ⟨r, s, ?_⟩
      intro t ht
      apply hrs
      simp only [pointAt, ha, one_ne_zero, ite_false, distanceSq] at ht
      nlinarith [ht]
    · obtain ⟨r, s, hrs⟩ := Univariate.quadratic_zeros_subset_pair 1 (-2*q.1)
        (q.1^2+(q.2-l.c)^2-radiusSq) (Or.inl one_ne_zero)
      refine ⟨r, s, ?_⟩
      intro t ht
      apply hrs
      simp only [pointAt, ha, ite_true, distanceSq] at ht
      nlinarith [ht]
  obtain ⟨r, s, hrs⟩ := hparams
  refine ⟨l.pointAt r, l.pointAt s, ?_⟩
  intro p hp hd
  obtain ⟨t, rfl⟩ := l.exists_pointAt p hp
  exact (hrs t hd).imp (congrArg l.pointAt) (congrArg l.pointAt)

/-- In particular the set of landing points is finite. -/
theorem finite_circle_intersection (l : Line K) (q : Point K) (radiusSq : K) :
    {p : Point K | l.Contains p ∧ distanceSq q p = radiusSq}.Finite := by
  obtain ⟨r, s, hrs⟩ := l.circle_intersection_subset_pair q radiusSq
  apply (Set.toFinite ({r, s} : Set (Point K))).subset
  exact fun p hp => hrs p hp.1 hp.2

/-- The crease determined by a landing point, including an unmoved source. -/
def landingCrease (source fixedPoint landing : Point K) (h : source ≠ fixedPoint) : Line K :=
  if hm : source = landing then through source fixedPoint h else bisector source landing hm

/-- Reflecting to a specified landing point determines the crease when another
distinct point is fixed. This also covers the source landing on itself. -/
theorem eq_landingCrease (p q r : Point K) (h : p ≠ q) (crease : Line K)
    (hq : crease.Contains q) (hr : crease.reflect p = r) :
    crease = landingCrease p q r h := by
  unfold landingCrease
  split
  · rename_i hp
    have hmem : crease.Contains p := (crease.reflect_eq_self p).mp (hr.trans hp.symm)
    exact through_unique p q h crease hmem hq
  · rename_i hp
    exact bisector_unique p r hp crease hr

/-- The chosen crease realizes the landing point exactly when the distances agree. -/
theorem landingCrease_spec (p q r : Point K) (h : p ≠ q)
    (hd : distanceSq q p = distanceSq q r) :
    (landingCrease p q r h).reflect p = r ∧ (landingCrease p q r h).Contains q := by
  unfold landingCrease
  split
  · rename_i hp
    exact ⟨((through p q h).reflect_eq_self p).mpr (through_left p q h) |>.trans hp,
      through_right p q h⟩
  · rename_i hp
    exact ⟨bisector_reflect p r hp, (contains_bisector p r q hp).mpr hd⟩

end Line
namespace FoldInput

/-- With distinct source and fixed point, every possible landing point gives
one crease, and every crease arises this way. -/
theorem axiom5_iff_landing {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (p q : Point K) (l crease : Line K) (h : p ≠ q) :
    (axiom5 p q l).Satisfies crease ↔
      ∃ r, l.Contains r ∧ Line.distanceSq q p = Line.distanceSq q r ∧
        crease = Line.landingCrease p q r h := by
  constructor
  · intro hc
    refine ⟨crease.reflect p, hc.1, ?_, Line.eq_landingCrease p q _ h crease hc.2 rfl⟩
    have hd := crease.distanceSq_reflect q p
    rw [(crease.reflect_eq_self q).mpr hc.2] at hd
    exact hd.symm
  · rintro ⟨r, hr, hd, rfl⟩
    obtain ⟨href, hq⟩ := Line.landingCrease_spec p q r h hd
    exact ⟨by rwa [href], hq⟩

/-- The bound of two counts distinct creases, not polynomial multiplicities. -/
theorem axiom5_solutions_subset_pair (p q : Point ℝ) (l : Line ℝ) (h : p ≠ q) :
    ∃ first second : Line ℝ,
      (axiom5 p q l).solutions ⊆ {first, second} := by
  obtain ⟨r, s, hrs⟩ := l.circle_intersection_subset_pair q (Line.distanceSq q p)
  refine ⟨Line.landingCrease p q r h, Line.landingCrease p q s h, ?_⟩
  intro crease hc
  obtain ⟨landing, hl, hd, rfl⟩ := (axiom5_iff_landing p q l crease h).mp hc
  exact (hrs landing hl hd.symm).imp
    (congrArg (fun x => Line.landingCrease p q x h))
    (congrArg (fun x => Line.landingCrease p q x h))

/-- With distinct input points, rule 5 has only finitely many real creases. -/
theorem axiom5_admissible_of_ne (p q : Point ℝ) (l : Line ℝ) (h : p ≠ q) :
    (axiom5 p q l).Admissible := by
  obtain ⟨first, second, hsubset⟩ := axiom5_solutions_subset_pair p q l h
  exact (Set.toFinite ({first, second} : Set (Line ℝ))).subset hsubset

/-- Identifying source and fixed point is impossible unless the source is
already on its target; in that case it leaves infinitely many creases. -/
theorem axiom5_admissible_iff (p q : Point ℝ) (l : Line ℝ) :
    (axiom5 p q l).Admissible ↔ p ≠ q ∨ ¬l.Contains p := by
  by_cases hpq : p = q
  · subst q
    by_cases hl : l.Contains p
    · have hs : (axiom5 p p l).solutions = {crease | crease.Contains p} := by
        ext crease
        constructor
        · exact fun h => h.2
        · intro h
          exact ⟨by rwa [(crease.reflect_eq_self p).mpr h], h⟩
      simp only [Admissible, hs, ne_eq, not_true_eq_false, hl, or_self]
      exact iff_false_intro (infinite_lines_through p)
    · have hs : (axiom5 p p l).solutions = ∅ := by
        ext crease
        constructor
        · intro h
          have hm := h.1
          rw [(crease.reflect_eq_self p).mpr h.2] at hm
          exact hl hm
        · intro h; cases h
      simp [Admissible, hs, hl]
  · exact ⟨fun _ => Or.inl hpq, fun _ => axiom5_admissible_of_ne p q l hpq⟩

/-- The bound of two covers every admissible request, including coincident
source/fixed points with an empty solution set. -/
theorem axiom5_solutions_bound (p q : Point ℝ) (l : Line ℝ)
    (h : (axiom5 p q l).Admissible) :
    ∃ first second : Line ℝ, (axiom5 p q l).solutions ⊆ {first, second} := by
  by_cases hp : p = q
  · subst q
    have hn := ((axiom5_admissible_iff p p l).mp h).resolve_left (by simp)
    refine ⟨Line.perpendicularThrough p l, Line.perpendicularThrough p l, ?_⟩
    intro crease hc
    have hm := hc.1
    rw [(crease.reflect_eq_self p).mpr hc.2] at hm
    exact False.elim (hn hm)
  · exact axiom5_solutions_subset_pair p q l hp

end FoldInput
end LeanOrigami
