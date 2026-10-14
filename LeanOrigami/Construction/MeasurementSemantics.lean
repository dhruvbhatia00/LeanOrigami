import LeanOrigami.Construction.DistanceRecipe
import LeanOrigami.Geometry.Euclidean

/-!
# Euclidean meaning of measurement recipes

The executable distance specification uses only polynomial arithmetic and a
sign. These theorems identify it with Mathlib's Euclidean distance, and identify
the square-root specification with Mathlib's nonnegative square root.
-/

namespace LeanOrigami

/-- The polynomial used by the distance recipe is the squared Euclidean distance. -/
theorem DistanceRecipe.squared_eq_dist_sq (p q : Point ℝ) :
    squared p q = dist p.toPlane q.toPlane ^ 2 := by
  simp [EuclideanSpace.dist_sq_eq, Point.toPlane, Fin.sum_univ_two,
    Real.dist_eq, sq_abs, squared]

/-- A nonnegative root of the recipe's distance polynomial is exactly the
Euclidean distance. This includes coincident points. -/
theorem DistanceRecipe.eq_distance_iff (p q : Point ℝ) (d : ℝ) :
    d = dist p.toPlane q.toPlane ↔ 0 ≤ d ∧ d^2 = squared p q := by
  rw [squared_eq_dist_sq]
  constructor
  · rintro rfl
    exact ⟨dist_nonneg, rfl⟩
  · rintro ⟨hn, hs⟩
    exact (sq_eq_sq₀ hn dist_nonneg).mp hs

/-- The signed square-root specification denotes Mathlib's square root exactly
on its advertised input domain. -/
theorem RootOperation.square_iff_sqrt (x t : ℝ) (hx : 0 ≤ x) :
    RootOperation.square.Relation x t ↔ t = Real.sqrt x := by
  constructor
  · intro h
    exact h.unique ⟨Real.sqrt_nonneg x, Real.sq_sqrt hx⟩
  · rintro rfl
    exact ⟨Real.sqrt_nonneg x, Real.sq_sqrt hx⟩

end LeanOrigami
