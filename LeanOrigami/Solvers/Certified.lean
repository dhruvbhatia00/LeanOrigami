import LeanOrigami.Solvers.Basic
import LeanOrigami.Construction.Program

/-!
# Certified primitive execution

For a requested fold, compute its unique candidate and carry a proof of real
finite-choice legality. These proofs have no runtime role. Unsupported rules
are explicit errors until their complete solvers are implemented.
-/

namespace LeanOrigami
namespace Solver
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Coordinate transport through a field embedding preserves distinct points. -/
theorem map_point_ne (f : K →+* ℝ) {p q : Point K} (h : p ≠ q) :
    (f p.1, f p.2) ≠ (f q.1, f q.2) := by
  intro heq
  exact h (Prod.ext (f.injective (congrArg Prod.fst heq))
    (f.injective (congrArg Prod.snd heq)))

/-- An exact crease together with its legality in the whole real plane. -/
abbrev Solution (input : FoldInput K) :=
  {crease : Line K // ∀ f : K →+* ℝ, (input.map f).Legal (crease.map f)}

/-- Compute the one available result for rules 1, 2, and 4.
No candidate list or caller assertion is used to justify admissibility. -/
def fold (input : FoldInput K) : Except ConstructionError (Solution input) :=
  match input with
  | .axiom1 p q =>
      if h : p ≠ q then
        .ok ⟨Line.through p q h, by
          intro f
          refine ⟨(FoldInput.axiom1_admissible_iff _ _).mpr (map_point_ne f h), ?_⟩
          exact ⟨(Line.contains_map f _ _).mpr (Line.through_left p q h),
            (Line.contains_map f _ _).mpr (Line.through_right p q h)⟩⟩
      else .error .coincidentPoints
  | .axiom2 p q =>
      if h : p ≠ q then
        .ok ⟨Line.bisector p q h, by
          intro f
          refine ⟨(FoldInput.axiom2_admissible_iff _ _).mpr (map_point_ne f h), ?_⟩
          change ((Line.bisector p q h).map f).reflect (f p.1, f p.2) = (f q.1, f q.2)
          rw [Line.reflect_map, Line.bisector_reflect]⟩
      else .error .coincidentPoints
  | .axiom4 p l =>
      .ok ⟨Line.perpendicularThrough p l, by
        intro f
        refine ⟨FoldInput.axiom4_admissible _ _, ?_⟩
        exact ⟨(Line.contains_map f _ _).mpr (Line.perpendicularThrough_mem p l),
          (Line.perpendicular_map f _ _).mpr (Line.perpendicularThrough_perpendicular p l)⟩⟩
  | .axiom3 .. => .error (.unsupportedFold 3)
  | .axiom5 .. => .error (.unsupportedFold 5)
  | .axiom6 .. => .error (.unsupportedFold 6)
  | .axiom7 .. => .error (.unsupportedFold 7)

/-- A nonzero determinant computes a point with unique-intersection evidence. -/
def intersect (l m : Line K) :
    Except ConstructionError
      {p : Point K // ∀ f : K →+* ℝ, LegalIntersection (l.map f) (m.map f) (f p.1, f p.2)} :=
  if h : l.determinant m ≠ 0 then
    .ok ⟨l.intersection m h, by
      intro f
      have hd : (l.map f).determinant (m.map f) ≠ 0 := by
        change f l.a * f m.b - f m.a * f l.b ≠ 0
        rw [← map_mul, ← map_mul, ← map_sub, ← map_zero f]
        exact fun hz => h (f.injective hz)
      have hl := (Line.contains_map f _ _).mpr (l.intersection_mem m h).1
      have hm := (Line.contains_map f _ _).mpr (l.intersection_mem m h).2
      refine ⟨hl, hm, ?_⟩
      intro q hql hqm
      exact ((l.map f).intersection_unique (m.map f) hd q hql hqm).trans
        ((l.map f).intersection_unique (m.map f) hd _ hl hm).symm⟩
  else if l = m then .error .coincidentLines else .error .parallelLines

end Solver
end LeanOrigami
