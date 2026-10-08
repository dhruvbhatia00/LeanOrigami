import LeanOrigami.Geometry.Reflection
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Projection
import Mathlib.Tactic.FinCases

/-!
# Meaning in Mathlib's Euclidean plane

Coordinate incidence describes an affine subspace. Coordinate reflection is
Mathlib's reflection in that subspace, and perpendicularity is orthogonality
of the nonzero direction vectors. This checks the geometric meaning of the
executable formulas independently of any fold solver.
-/

namespace LeanOrigami

/-- Mathlib's usual two-dimensional real inner product space. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

namespace Point
/-- Interpret a pair as a vector in the Euclidean plane. -/
def toPlane (p : Point ℝ) : Plane := WithLp.toLp 2 ![p.1, p.2]

/-- Coordinate interpretation is injective. -/
theorem toPlane_injective : Function.Injective toPlane := by
  intro p q h
  exact Prod.ext (congrArg (fun v : Plane => v 0) h)
    (congrArg (fun v : Plane => v 1) h)
end Point

namespace Line

/-- The affine subspace described by a real line's equation. -/
def affine (l : Line ℝ) : AffineSubspace ℝ Plane where
  carrier := {v | l.a*v 0 + l.b*v 1 = l.c}
  smul_vsub_vadd_mem' := by
    intro t p q r hp hq hr
    change l.a*(t*(p 0-q 0)+r 0) + l.b*(t*(p 1-q 1)+r 1) = l.c
    change l.a*p 0+l.b*p 1 = l.c at hp
    change l.a*q 0+l.b*q 1 = l.c at hq
    change l.a*r 0+l.b*r 1 = l.c at hr
    linear_combination t*hp-t*hq+hr

/-- Membership in the Mathlib affine subspace is exactly coordinate incidence. -/
@[simp] theorem mem_affine (l : Line ℝ) (p : Point ℝ) :
    p.toPlane ∈ l.affine ↔ l.Contains p := Iff.rfl

/-- Every valid line has a point; reflection never uses an empty subspace. -/
theorem affine_nonempty (l : Line ℝ) : (l.affine : Set Plane).Nonempty := by
  rcases l.normalized with ha | ⟨ha, hb⟩
  · exact ⟨Point.toPlane (l.c, 0), by simp [mem_affine, Contains, ha]⟩
  · exact ⟨Point.toPlane (0, l.c), by simp [mem_affine, Contains, ha, hb]⟩

instance (l : Line ℝ) : Nonempty l.affine :=
  l.affine_nonempty.to_subtype

/-- Direction vectors satisfy the homogeneous line equation. -/
theorem direction_equation (l : Line ℝ) (v : Plane) (hv : v ∈ l.affine.direction) :
    l.a*v 0 + l.b*v 1 = 0 := by
  obtain ⟨p, hp, q, hq, rfl⟩ :=
    (AffineSubspace.mem_direction_iff_eq_vsub l.affine_nonempty v).mp hv
  change l.a*p 0+l.b*p 1 = l.c at hp
  change l.a*q 0+l.b*q 1 = l.c at hq
  change l.a*(p 0-q 0)+l.b*(p 1-q 1) = 0
  linear_combination hp-hq

/-- The homogeneous equation describes the entire direction subspace. -/
theorem mem_direction_iff (l : Line ℝ) (v : Plane) :
    v ∈ l.affine.direction ↔ l.a*v 0 + l.b*v 1 = 0 := by
  refine ⟨direction_equation l v, ?_⟩
  intro hv
  obtain ⟨p, hp⟩ := l.affine_nonempty
  apply (AffineSubspace.vadd_mem_iff_mem_direction v hp).mp
  change l.a*p 0+l.b*p 1 = l.c at hp
  change l.a*(v 0+p 0)+l.b*(v 1+p 1) = l.c
  linear_combination hv+hp

/-- A nonzero direction vector tangent to the line. -/
def directionVector (l : Line ℝ) : Plane := Point.toPlane (-l.b, l.a)

/-- The chosen direction vector cannot vanish. -/
theorem directionVector_ne_zero (l : Line ℝ) : l.directionVector ≠ 0 := by
  intro h
  have ha := congrArg (fun v : Plane => v 1) h
  have hb := congrArg (fun v : Plane => v 0) h
  change l.a = 0 at ha
  change -l.b = 0 at hb
  rcases l.normal_ne_zero with h | h
  · exact h ha
  · exact h (neg_eq_zero.mp hb)

/-- The selected tangent belongs to the line's direction subspace. -/
theorem directionVector_mem (l : Line ℝ) : l.directionVector ∈ l.affine.direction := by
  rw [mem_direction_iff]
  change l.a*(-l.b)+l.b*l.a = 0
  ring

/-- Every direction is a scalar multiple of the selected nonzero tangent. -/
theorem direction_eq_smul (l : Line ℝ) (v : Plane) (hv : v ∈ l.affine.direction) :
    ∃ t : ℝ, v = t • l.directionVector := by
  have hd := direction_equation l v hv
  rcases l.normalized with ha | ⟨ha, hb⟩
  · refine ⟨v 1, ?_⟩
    ext i
    fin_cases i <;> simp [directionVector, Point.toPlane, ha] at *
    all_goals linarith
  · refine ⟨-v 0, ?_⟩
    ext i
    fin_cases i <;> simp [directionVector, Point.toPlane, ha, hb] at *
    all_goals linarith

/-- Coordinate perpendicularity is orthogonality in Mathlib's inner product. -/
theorem perpendicular_iff_inner (l m : Line ℝ) :
    l.Perpendicular m ↔ inner ℝ l.directionVector m.directionVector = 0 := by
  simp [Perpendicular, directionVector, Point.toPlane, PiLp.inner_apply, Fin.sum_univ_two]
  ring_nf

/-- Perpendicularity agrees with orthogonality of the full direction subspaces. -/
theorem perpendicular_iff_isOrtho (l m : Line ℝ) :
    l.Perpendicular m ↔ l.affine.direction.IsOrtho m.affine.direction := by
  rw [perpendicular_iff_inner]
  constructor
  · intro h v hv w hw
    obtain ⟨t, rfl⟩ := direction_eq_smul l v hv
    obtain ⟨u, rfl⟩ := direction_eq_smul m w hw
    have hr : inner ℝ m.directionVector l.directionVector = 0 :=
      (real_inner_comm _ _).trans h
    simp [inner_smul_left, inner_smul_right, hr]
  · intro h
    exact h.inner_eq (directionVector_mem l) (directionVector_mem m)

/-- The coordinate midpoint is Mathlib's orthogonal projection onto the line. -/
theorem orthogonalProjection_eq_midpoint (l : Line ℝ) (p : Point ℝ) :
    (EuclideanGeometry.orthogonalProjection l.affine p.toPlane : Plane) =
      Point.toPlane ((p.1+(l.reflect p).1)/2, (p.2+(l.reflect p).2)/2) := by
  apply EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem.mpr
  constructor
  · exact (mem_affine _ _).mpr (midpoint_mem l p)
  · apply (Submodule.mem_orthogonal _ _).mpr
    intro v hv
    have hd := direction_equation l v hv
    simp only [PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply]
    change v 0*(p.1-(p.1+(l.reflect p).1)/2) +
      v 1*(p.2-(p.2+(l.reflect p).2)/2) = 0
    dsimp [reflect]
    linear_combination (l.residual p/l.normalSq)*hd

/-- Coordinate reflection is exactly Mathlib's geometric reflection. -/
theorem reflect_eq_mathlib (l : Line ℝ) (p : Point ℝ) :
    (l.reflect p).toPlane = EuclideanGeometry.reflection l.affine p.toPlane := by
  rw [EuclideanGeometry.reflection_apply', orthogonalProjection_eq_midpoint]
  ext i
  fin_cases i <;> simp [Point.toPlane] <;> ring

end Line
end LeanOrigami
