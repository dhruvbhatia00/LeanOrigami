import LeanOrigami.Solvers.LineLine

/-!
# Rule 7: point-to-line folding in a prescribed direction

All creases perpendicular to the supplied line have one canonical normal.
Alignment either determines their offset, holds for every offset, or holds
for none. No root search is needed for this operation.
-/

namespace LeanOrigami
namespace Line
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Perpendiculars to the same line share their canonical normal. -/
theorem normal_eq_of_perpendicular (l m n : Line K)
    (hl : l.Perpendicular n) (hm : m.Perpendicular n) : l.a = m.a ∧ l.b = m.b := by
  let l₀ : Line K := {l with c := 0}
  let m₀ : Line K := {m with c := 0}
  have he := perpendicular_unique (0, 0) n l₀ m₀
    (by simp [l₀, Contains]) (by simp [m₀, Contains]) hl hm
  constructor
  · simpa only [l₀, m₀] using congrArg Line.a he
  · simpa only [l₀, m₀] using congrArg Line.b he

/-- The target-normal dot product for the prescribed perpendicular direction. -/
def perpendicularAlignmentDot (target direction : Line K) : K :=
  let n := perpendicularThrough (0, 0) direction
  target.a*n.a + target.b*n.b

/-- The unique candidate when the target actually constrains the offset. -/
def alignPerpendicular (p : Point K) (target direction : Line K)
    (_h : target.perpendicularAlignmentDot direction ≠ 0) : Line K :=
  let n := perpendicularThrough (0, 0) direction
  {n with c := n.a*p.1 + n.b*p.2 -
    target.residual p*n.normalSq/(2*target.perpendicularAlignmentDot direction)}

/-- The alignment equation in the fixed perpendicular direction. -/
theorem alignmentEquation_perpendicular (target direction crease : Line K) (p : Point K)
    (hp : crease.Perpendicular direction) :
    crease.alignmentEquation target p =
      let n := perpendicularThrough (0, 0) direction
      target.residual p*n.normalSq -
        2*(n.a*p.1+n.b*p.2-crease.c)*target.perpendicularAlignmentDot direction := by
  obtain ⟨ha, hb⟩ := normal_eq_of_perpendicular crease
    (perpendicularThrough (0, 0) direction) direction hp
    (perpendicularThrough_perpendicular _ _)
  dsimp [alignmentEquation, residual, normalSq, perpendicularAlignmentDot]
  rw [ha, hb]

/-- The candidate has the prescribed perpendicular direction. -/
theorem alignPerpendicular_perpendicular (p : Point K) (target direction : Line K)
    (h : target.perpendicularAlignmentDot direction ≠ 0) :
    (alignPerpendicular p target direction h).Perpendicular direction :=
  perpendicularThrough_perpendicular (0, 0) direction

/-- Its chosen offset places the reflected source exactly on the target. -/
theorem alignPerpendicular_mem (p : Point K) (target direction : Line K)
    (h : target.perpendicularAlignmentDot direction ≠ 0) :
    target.Contains ((alignPerpendicular p target direction h).reflect p) := by
  rw [← alignmentEquation_zero_iff, alignmentEquation_perpendicular _ _ _ _
    (alignPerpendicular_perpendicular p target direction h)]
  dsimp only [alignPerpendicular]
  field_simp
  ring

/-- Every solution in this direction has the computed offset. -/
theorem alignPerpendicular_unique (p : Point K) (target direction crease : Line K)
    (h : target.perpendicularAlignmentDot direction ≠ 0)
    (ht : target.Contains (crease.reflect p)) (hp : crease.Perpendicular direction) :
    crease = alignPerpendicular p target direction h := by
  obtain ⟨ha, hb⟩ := normal_eq_of_perpendicular crease
    (perpendicularThrough (0, 0) direction) direction hp
    (perpendicularThrough_perpendicular _ _)
  have he := (alignmentEquation_zero_iff crease target p).mpr ht
  rw [alignmentEquation_perpendicular target direction crease p hp] at he
  apply Line.ext
  · exact ha
  · exact hb
  · dsimp only [alignPerpendicular]
    field_simp
    nlinarith [he]

/-- When the target does not constrain the offset, every allowed crease
succeeds precisely when the source is already on the target. -/
theorem alignment_perpendicular_zero (p : Point K) (target direction crease : Line K)
    (hd : target.perpendicularAlignmentDot direction = 0)
    (hp : crease.Perpendicular direction) :
    target.Contains (crease.reflect p) ↔ target.Contains p := by
  rw [← alignmentEquation_zero_iff, alignmentEquation_perpendicular _ _ _ _ hp]
  simp only [hd, mul_zero, sub_zero, mul_eq_zero,
    (perpendicularThrough (0, 0) direction).normalSq_ne_zero, or_false, residual_eq_zero]

/-- The offset guard commutes with field embeddings; no ordering assumption
on the embedding is needed. -/
theorem perpendicularAlignmentDot_map {L : Type*} [Field L] [LinearOrder L]
    [IsStrictOrderedRing L] (f : K →+* L) (target direction : Line K) :
    (target.map f).perpendicularAlignmentDot (direction.map f) =
      f (target.perpendicularAlignmentDot direction) := by
  obtain ⟨ha, hb⟩ := normal_eq_of_perpendicular
    ((perpendicularThrough (0, 0) direction).map f)
    (perpendicularThrough (0, 0) (direction.map f)) (direction.map f)
    ((perpendicular_map f _ _).mpr (perpendicularThrough_perpendicular _ _))
    (perpendicularThrough_perpendicular _ _)
  dsimp only [perpendicularAlignmentDot]
  rw [← ha, ← hb]
  simp [map, map_add, map_mul]

end Line
namespace FoldInput
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The single candidate is equivalent to the complete rule-7 relation. -/
theorem axiom7_iff_candidate (p : Point K) (l m crease : Line K)
    (h : l.perpendicularAlignmentDot m ≠ 0) :
    (axiom7 p l m).Satisfies crease ↔ crease = Line.alignPerpendicular p l m h := by
  constructor
  · exact fun hc => Line.alignPerpendicular_unique p l m crease h hc.1 hc.2
  · rintro rfl
    exact ⟨Line.alignPerpendicular_mem p l m h, Line.alignPerpendicular_perpendicular p l m h⟩

/-- A vanishing dot product gives either all perpendiculars or no solution. -/
theorem axiom7_zero_iff (p : Point K) (l m crease : Line K)
    (h : l.perpendicularAlignmentDot m = 0) :
    (axiom7 p l m).Satisfies crease ↔ l.Contains p ∧ crease.Perpendicular m := by
  constructor
  · exact fun hc => ⟨(Line.alignment_perpendicular_zero p l m crease h hc.2).mp hc.1, hc.2⟩
  · exact fun hc => ⟨(Line.alignment_perpendicular_zero p l m crease h hc.2).mpr hc.1, hc.2⟩

/-- The precise finite-choice classification for rule 7. -/
theorem axiom7_admissible_iff (p : Point ℝ) (l m : Line ℝ) :
    (axiom7 p l m).Admissible ↔ l.perpendicularAlignmentDot m ≠ 0 ∨ ¬l.Contains p := by
  by_cases hd : l.perpendicularAlignmentDot m = 0
  · have hs : (axiom7 p l m).solutions = {crease | l.Contains p ∧ crease.Perpendicular m} := by
      ext crease
      exact axiom7_zero_iff p l m crease hd
    by_cases hp : l.Contains p
    · simp only [Admissible, hs, hp, true_and, hd, ne_eq, not_true_eq_false, or_self]
      exact iff_false_intro (infinite_perpendicular_lines m)
    · simp [Admissible, hs, hp]
  · have hs : (axiom7 p l m).solutions = {Line.alignPerpendicular p l m hd} := by
      ext crease
      exact axiom7_iff_candidate p l m crease hd
    simp [Admissible, hs, hd]

/-- Every admissible rule-7 request has at most one crease, including empty cases. -/
theorem axiom7_solutions_subsingleton (p : Point ℝ) (l m : Line ℝ)
    (h : (axiom7 p l m).Admissible) : (axiom7 p l m).solutions.Subsingleton := by
  intro first hf second hs
  by_cases hd : l.perpendicularAlignmentDot m = 0
  · have hn := ((axiom7_admissible_iff p l m).mp h).resolve_left (not_not.mpr hd)
    exact False.elim (hn ((axiom7_zero_iff p l m first hd).mp hf).1)
  · exact ((axiom7_iff_candidate p l m first hd).mp hf).trans
      ((axiom7_iff_candidate p l m second hd).mp hs).symm

end FoldInput
end LeanOrigami
