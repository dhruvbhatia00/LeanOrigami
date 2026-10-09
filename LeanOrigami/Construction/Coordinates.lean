import LeanOrigami.Construction.Geometry
import LeanOrigami.Construction.Basis

/-!
# Constructed points and their coordinates

The initial seeds determine both axes and an off-axis unit point. Perpendiculars,
intersections, and the diagonal then place any constructed coordinate on either
axis. These constructions work unchanged for zero and negative coordinates.
-/

namespace LeanOrigami
namespace Constructible

/-- Draw the vertical through a constructed point. -/
theorem vertical {p : Point ℝ} (hp : Constructible (.point p)) :
    Constructible (.line (Line.chart 0 p.1)) := by
  apply perpendicular hp xAxis
  · simp [Line.Contains, Line.chart]
  · simp [Line.Perpendicular, Line.chart]

/-- Draw the horizontal through a constructed point. -/
theorem horizontal {p : Point ℝ} (hp : Constructible (.point p)) :
    Constructible (.line (Line.horizontal p.2)) := by
  apply perpendicular hp yAxis
  · simp [Line.Contains, Line.horizontal]
  · simp [Line.Perpendicular, Line.horizontal]

/-- Place the first coordinate on the original axis. -/
theorem project_x {p : Point ℝ} (hp : Constructible (.point p)) :
    Constructible (.point (p.1, 0)) := by
  apply of_intersection (vertical hp) xAxis
  · simp [Line.determinant, Line.chart]
  · simp [Line.Contains, Line.chart]
  · simp [Line.Contains]

/-- Place the second coordinate on the vertical axis. -/
theorem project_y {p : Point ℝ} (hp : Constructible (.point p)) :
    Constructible (.point (0, p.2)) := by
  apply of_intersection yAxis (horizontal hp)
  · simp [Line.determinant, Line.horizontal]
  · simp [Line.Contains]
  · simp [Line.Contains, Line.horizontal]

/-- Intersect the vertical and horizontal through two axis points. -/
theorem grid {x y : ℝ} (hx : Constructible (.point (x, 0)))
    (hy : Constructible (.point (0, y))) : Constructible (.point (x, y)) := by
  apply of_intersection (vertical hx) (horizontal hy)
  · simp [Line.determinant, Line.chart, Line.horizontal]
  · simp [Line.Contains, Line.chart]
  · simp [Line.Contains, Line.horizontal]

/-- The line `y = x` is itself constructed, not assumed as an initial object. -/
theorem diagonal : Constructible (.line (Line.chart (-1) 0)) := by
  have hunit : Constructible (.point (1, 1)) := grid unit (Basis.point_constructible true)
  apply through origin hunit
  · norm_num
  · norm_num [Line.Contains, Line.chart]
  · norm_num [Line.Contains, Line.chart]

/-- Transfer a horizontal-axis coordinate to the vertical axis. -/
theorem x_to_y {x : ℝ} (hx : Constructible (.point (x, 0))) :
    Constructible (.point (0, x)) := by
  have h : Constructible (.point (x, x)) := by
    apply of_intersection (vertical hx) diagonal
    · norm_num [Line.determinant, Line.chart]
    · simp [Line.Contains, Line.chart]
    · simp [Line.Contains, Line.chart]
  exact project_y h

/-- Transfer a vertical-axis coordinate to the horizontal axis. -/
theorem y_to_x {y : ℝ} (hy : Constructible (.point (0, y))) :
    Constructible (.point (y, 0)) := by
  have h : Constructible (.point (y, y)) := by
    apply of_intersection diagonal (horizontal hy)
    · norm_num [Line.determinant, Line.chart, Line.horizontal]
    · simp [Line.Contains, Line.chart]
    · simp [Line.Contains, Line.horizontal]
  exact project_x h

end Constructible
namespace ConstructibleNumber

/-- A constructed point supplies its first coordinate. -/
theorem of_x {p : Point ℝ} (hp : Constructible (.point p)) : ConstructibleNumber p.1 :=
  ⟨p, hp, Or.inl rfl⟩

/-- A constructed point supplies its second coordinate. -/
theorem of_y {p : Point ℝ} (hp : Constructible (.point p)) : ConstructibleNumber p.2 :=
  ⟨p, hp, Or.inr rfl⟩

/-- Any constructed number can be placed on the original axis, whichever
coordinate originally named it. -/
theorem axis_point {x : ℝ} (hx : ConstructibleNumber x) : Constructible (.point (x, 0)) := by
  obtain ⟨p, hp, hx | hx⟩ := hx
  · exact hx ▸ Constructible.project_x hp
  · exact hx ▸ Constructible.y_to_x (Constructible.project_y hp)

/-- Two independently constructed coordinates give a constructed point. -/
theorem point {x y : ℝ} (hx : ConstructibleNumber x) (hy : ConstructibleNumber y) :
    Constructible (.point (x, y)) :=
  Constructible.grid hx.axis_point (Constructible.x_to_y hy.axis_point)

/-- Zero is supplied by the origin seed. -/
theorem zero : ConstructibleNumber 0 := of_x Constructible.origin

/-- One is supplied by the unit seed. -/
theorem one : ConstructibleNumber 1 := of_x Constructible.unit

end ConstructibleNumber

/-- A point is constructible exactly when both of its coordinates are. -/
theorem constructible_point_iff (p : Point ℝ) :
    Constructible (.point p) ↔ ConstructibleNumber p.1 ∧ ConstructibleNumber p.2 := by
  constructor
  · exact fun hp => ⟨ConstructibleNumber.of_x hp, ConstructibleNumber.of_y hp⟩
  · rintro ⟨hx, hy⟩
    exact ConstructibleNumber.point hx hy

end LeanOrigami
