import LeanOrigami.Scalar
import LeanOrigami.Geometry.Euclidean
import LeanOrigami.Folds

/-!
# Exact objects and their real meaning

Exact points and lines use `Scalar`. Their interpretation is injective and
preserves the geometric operations. Legal exact selections are judged by the
fold relation and finite solution set over the whole real plane, not just
by algebraic candidate enumeration.
-/

namespace LeanOrigami

namespace Point
/-- Interpret exact coordinates as real coordinates. -/
noncomputable def toReal (p : Point Scalar) : Point ℝ :=
  (Scalar.realHom p.1, Scalar.realHom p.2)

/-- Different exact points remain different real points. -/
theorem toReal_injective : Function.Injective toReal := by
  intro p q h
  exact Prod.ext (Scalar.toReal_injective (congrArg Prod.fst h))
    (Scalar.toReal_injective (congrArg Prod.snd h))
end Point

namespace Line
/-- Interpret exact line coefficients as real coefficients. -/
noncomputable def toReal (l : Line Scalar) : Line ℝ := l.map Scalar.realHom

/-- Canonical exact lines retain their identity in the real plane. -/
theorem toReal_injective : Function.Injective toReal := map_injective Scalar.realHom

/-- Incidence is unchanged under real interpretation. -/
@[simp] theorem contains_toReal (l : Line Scalar) (p : Point Scalar) :
    l.toReal.Contains p.toReal ↔ l.Contains p := contains_map Scalar.realHom l p

/-- Perpendicularity is unchanged under real interpretation. -/
@[simp] theorem perpendicular_toReal (l m : Line Scalar) :
    l.toReal.Perpendicular m.toReal ↔ l.Perpendicular m := perpendicular_map Scalar.realHom l m

/-- Exact reflection and real reflection compute the same coordinates. -/
theorem toReal_reflect (l : Line Scalar) (p : Point Scalar) :
    (l.reflect p).toReal = l.toReal.reflect p.toReal := (reflect_map Scalar.realHom l p).symm

/-- Exact reflection denotes Mathlib's geometric reflection in the real plane. -/
theorem exact_reflect_eq_mathlib (l : Line Scalar) (p : Point Scalar) :
    (l.reflect p).toReal.toPlane =
      EuclideanGeometry.reflection l.toReal.affine p.toReal.toPlane := by
  rw [toReal_reflect, reflect_eq_mathlib]

/-- Nonzero determinants remain nonzero under real interpretation. -/
theorem determinant_toReal_ne_zero (l m : Line Scalar) (h : l.determinant m ≠ 0) :
    l.toReal.determinant m.toReal ≠ 0 := by
  change Scalar.realHom l.a * Scalar.realHom m.b -
    Scalar.realHom m.a * Scalar.realHom l.b ≠ 0
  rw [← map_mul, ← map_mul, ← map_sub, ← map_zero Scalar.realHom]
  exact fun hz => h (Scalar.realHom.injective hz)

/-- Interpreting an exact intersection gives the unique real intersection. -/
theorem toReal_intersection (l m : Line Scalar) (h : l.determinant m ≠ 0) :
    (l.intersection m h).toReal =
      l.toReal.intersection m.toReal (determinant_toReal_ne_zero l m h) := by
  apply intersection_unique
  · exact (contains_toReal _ _).mpr (intersection_mem l m h).1
  · exact (contains_toReal _ _).mpr (intersection_mem l m h).2
end Line

namespace FoldInput
/-- Real geometric inputs corresponding to the stored exact input objects. -/
noncomputable def toReal (input : FoldInput Scalar) : FoldInput ℝ := input.map Scalar.realHom

/-- Legality of an exact crease is judged against all real crease solutions.
This is a specification, not an executable checker or evidence of input provenance. -/
def LegalExact (input : FoldInput Scalar) (crease : Line Scalar) : Prop :=
  input.toReal.Legal crease.toReal
end FoldInput

/-- An exact transverse intersection is a legal real geometric intersection. -/
theorem exact_intersection_legal (l m : Line Scalar) (h : l.determinant m ≠ 0) :
    LegalIntersection l.toReal m.toReal (l.intersection m h).toReal := by
  rw [Line.toReal_intersection]
  exact legalIntersection_of_determinant _ _ _

end LeanOrigami
