import LeanOrigami.Construction.History
import LeanOrigami.Solvers.Basic

/-!
# Geometric operations on construction histories

These lemmas package legal primitive steps with explicit input provenance.
They do not add construction rules: each proof uses the existing fold or
unique-intersection constructor. Coordinates alone never supply provenance.
-/

namespace LeanOrigami.Constructible

/-- A line through two distinct constructed points is constructed by rule 1. -/
theorem through {p q : Point ℝ} {l : Line ℝ}
    (hp : Constructible (.point p)) (hq : Constructible (.point q)) (hne : p ≠ q)
    (hlp : l.Contains p) (hlq : l.Contains q) : Constructible (.line l) := by
  apply Constructible.fold (.axiom1 p q) l
  · simpa [FoldInput.objects] using And.intro hp hq
  · exact ⟨(FoldInput.axiom1_admissible_iff p q).mpr hne, hlp, hlq⟩

/-- Rule 4 constructs a specified perpendicular through a constructed point. -/
theorem perpendicular {p : Point ℝ} {l m : Line ℝ}
    (hp : Constructible (.point p)) (hl : Constructible (.line l))
    (hmp : m.Contains p) (hml : m.Perpendicular l) : Constructible (.line m) := by
  apply Constructible.fold (.axiom4 p l) m
  · simpa [FoldInput.objects] using And.intro hp hl
  · exact ⟨FoldInput.axiom4_admissible p l, hmp, hml⟩

/-- Nonparallel constructed lines supply their specified common point. -/
theorem of_intersection {l m : Line ℝ} {p : Point ℝ}
    (hl : Constructible (.line l)) (hm : Constructible (.line m))
    (hd : l.determinant m ≠ 0) (hpl : l.Contains p) (hpm : m.Contains p) :
    Constructible (.point p) := by
  apply Constructible.intersection l m p hl hm
  refine ⟨hpl, hpm, ?_⟩
  intro q hql hqm
  exact (l.intersection_unique m hd q hql hqm).trans
    (l.intersection_unique m hd p hpl hpm).symm

/-- Two rule-4 steps draw a parallel through a constructed point. Matching
canonical normals expresses parallelism without introducing a new rule. -/
theorem parallel {p : Point ℝ} {l m : Line ℝ}
    (hp : Constructible (.point p)) (hl : Constructible (.line l))
    (ha : m.a = l.a) (hb : m.b = l.b) (hm : m.Contains p) : Constructible (.line m) := by
  let n := Line.perpendicularThrough p l
  have hn : Constructible (.line n) := perpendicular hp hl
    (Line.perpendicularThrough_mem p l) (Line.perpendicularThrough_perpendicular p l)
  apply perpendicular hp hn hm
  have h := (Line.perpendicular_comm n l).mp (Line.perpendicularThrough_perpendicular p l)
  simpa only [Line.Perpendicular, ha, hb] using h

/-- The initial horizontal axis is obtained from the two permitted seeds. -/
theorem xAxis : Constructible (.line (⟨0, 1, 0, Or.inr ⟨rfl, rfl⟩⟩ : Line ℝ)) := by
  apply through Constructible.origin Constructible.unit
  · norm_num
  · norm_num [Line.Contains]
  · norm_num [Line.Contains]

/-- A perpendicular at the origin supplies the other axis. -/
theorem yAxis : Constructible (.line (⟨1, 0, 0, Or.inl rfl⟩ : Line ℝ)) := by
  apply perpendicular Constructible.origin xAxis
  · norm_num [Line.Contains]
  · norm_num [Line.Perpendicular]

end LeanOrigami.Constructible
