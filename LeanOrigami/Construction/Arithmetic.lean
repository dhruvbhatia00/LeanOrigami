import LeanOrigami.Construction.Coordinates

/-!
# Elementary arithmetic by explicit geometric constructions

Each theorem starts with construction evidence for its operands and records
only lines through known points, perpendiculars, and unique intersections.
The formulas work for signed and zero operands. Division alone requires a
nonzero divisor. Executable versions are expanded into primitive programs
by the recipe module.
-/

namespace LeanOrigami.ConstructibleNumber

/-- Addition translates the line through `(0,1)` and `(y,0)` to pass through
`(x,1)`; its intersection with the original axis is `(x+y,0)`. -/
theorem add {x y : ℝ} (hx : ConstructibleNumber x) (hy : ConstructibleNumber y) :
    ConstructibleNumber (x+y) := by
  have hbase : Constructible (.line (Line.chart y y)) := by
    apply Constructible.through (Basis.point_constructible true) hy.axis_point
    · intro he; have h := congrArg Prod.snd he; norm_num [Basis.height] at h
    · simp [Line.Contains, Line.chart, Basis.height]
    · simp [Line.Contains, Line.chart]
  have hshift : Constructible (.line (Line.chart y (x+y))) := by
    apply Constructible.parallel (m := Line.chart y (x+y)) (point hx one) hbase rfl rfl
    simp [Line.Contains, Line.chart]
  apply of_x (p := (x+y, 0))
  apply Constructible.of_intersection hshift Constructible.xAxis
  · simp [Line.determinant, Line.chart]
  · simp [Line.Contains, Line.chart]
  · simp [Line.Contains]

/-- Subtraction translates the line through the origin and `(y,1)` to pass
through `(x,1)`. Its horizontal-axis intercept is `x-y`. -/
theorem sub {x y : ℝ} (hx : ConstructibleNumber x) (hy : ConstructibleNumber y) :
    ConstructibleNumber (x-y) := by
  have hbase : Constructible (.line (Line.chart (-y) 0)) := by
    apply Constructible.through Constructible.origin (point hy one)
    · intro he; have h := congrArg Prod.snd he; norm_num at h
    · simp [Line.Contains, Line.chart]
    · simp [Line.Contains, Line.chart]
  have hshift : Constructible (.line (Line.chart (-y) (x-y))) := by
    apply Constructible.parallel (m := Line.chart (-y) (x-y)) (point hx one) hbase rfl rfl
    simp [Line.Contains, Line.chart, sub_eq_add_neg]
  apply of_x (p := (x-y, 0))
  apply Constructible.of_intersection hshift Constructible.xAxis
  · simp [Line.determinant, Line.chart]
  · simp [Line.Contains, Line.chart]
  · simp [Line.Contains]

/-- Reflection of a signed coordinate is already a subtraction construction. -/
theorem neg {x : ℝ} (hx : ConstructibleNumber x) : ConstructibleNumber (-x) := by
  simpa using sub zero hx

/-- The line through the origin and `(x,1)` meets height `y` at `(x*y,y)`. -/
theorem mul {x y : ℝ} (hx : ConstructibleNumber x) (hy : ConstructibleNumber y) :
    ConstructibleNumber (x*y) := by
  have hbase : Constructible (.line (Line.chart (-x) 0)) := by
    apply Constructible.through Constructible.origin (point hx one)
    · intro he; have h := congrArg Prod.snd he; norm_num at h
    · simp [Line.Contains, Line.chart]
    · simp [Line.Contains, Line.chart]
  apply of_x (p := (x*y, y))
  apply Constructible.of_intersection hbase (Constructible.horizontal (point zero hy))
  · simp [Line.determinant, Line.chart, Line.horizontal]
  · simp [Line.Contains, Line.chart]
  · simp [Line.Contains, Line.horizontal]

/-- The line through the origin and `(1,y)` meets height `x` at `(x/y,x)`.
The nonzero guard is the geometric condition needed for this intersection. -/
theorem div {x y : ℝ} (hx : ConstructibleNumber x) (hy : ConstructibleNumber y) (hne : y ≠ 0) :
    ConstructibleNumber (x/y) := by
  have hbase : Constructible (.line (Line.chart (-1/y) 0)) := by
    apply Constructible.through Constructible.origin (point one hy)
    · intro he; have h := congrArg Prod.fst he; norm_num at h
    · simp [Line.Contains, Line.chart]
    · simp [Line.Contains, Line.chart, hne]
  apply of_x (p := (x/y, x))
  apply Constructible.of_intersection hbase (Constructible.horizontal (point zero hx))
  · simp [Line.determinant, Line.chart, Line.horizontal]
  · simp [Line.Contains, Line.chart]
    ring
  · simp [Line.Contains, Line.horizontal]

end LeanOrigami.ConstructibleNumber
