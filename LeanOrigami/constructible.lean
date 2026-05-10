import LeanOrigami.Axioms

/-!
# Origami constructibility

The mutual inductive predicates `cons_point` and `cons_line` describe points
and lines obtainable from the Huzita-Hatori axioms, starting from `0` and `1`
on the real axis.  A real number is constructible when it appears as one
coordinate of a constructible point.
-/

mutual

inductive cons_point : Point → Prop where
  | hOrigin (P : Point) : P = ![0, 0] → cons_point P
  | hOne (P : Point) : P = ![1, 0] → cons_point P
  | hIntersect {L₁ L₂ : Line}
      (hL₁ : cons_line L₁) (hL₂ : cons_line L₂) (P : Point) :
      intersects_at L₁ L₂ P → cons_point P

inductive cons_line : Line → Prop where
  | axiom1 {P₁ P₂ : Point} (hP₁ : cons_point P₁) (hP₂ : cons_point P₂) {L : Line} :
      valid L → Axiom1 P₁ P₂ L → cons_line L
  | axiom2 {P₁ P₂ : Point} (hP₁ : cons_point P₁) (hP₂ : cons_point P₂) {L : Line} :
      valid L → Axiom2 P₁ P₂ L → cons_line L
  | axiom3 {L₁ L₂ : Line} (hL₁ : cons_line L₁) (hL₂ : cons_line L₂) {L : Line} :
      valid L → Axiom3 L₁ L₂ L → cons_line L
  | axiom4 {L₁ : Line} {P₁ : Point}
      (hL₁ : cons_line L₁) (hP₁ : cons_point P₁) {L : Line} :
      valid L → Axiom4 L₁ P₁ L → cons_line L
  | axiom5 {P₁ P₂ : Point} {L₁ : Line}
      (hP₁ : cons_point P₁) (hP₂ : cons_point P₂) (hL₁ : cons_line L₁) {L : Line} :
      valid L → Axiom5 P₁ P₂ L₁ L → cons_line L
  | axiom6 {P₁ P₂ : Point} {L₁ L₂ : Line}
      (hP₁ : cons_point P₁) (hP₂ : cons_point P₂)
      (hL₁ : cons_line L₁) (hL₂ : cons_line L₂) {L : Line} :
      valid L → Axiom6 P₁ P₂ L₁ L₂ L → cons_line L
  | axiom7 {L₁ : Line} {P : Point}
      (hL₁ : cons_line L₁) (hP : cons_point P) (L : Line) :
      valid L → Axiom7 L₁ P L → cons_line L

end

/-! ## Constructible real numbers -/

def constructible_real_proj (x : ℝ) : Prop :=
  ∃ P : Point, cons_point P ∧ (P 0 = x ∨ P 1 = x)

def constructible_real_dist (x : ℝ) : Prop :=
  ∃ P : Point, cons_point P ∧ ((P 0) ^ 2 + (P 1) ^ 2 = x ^ 2)

--0 and 1 are constructible points.
lemma cons_point_origin : cons_point ![0, 0] :=
  cons_point.hOrigin _ rfl

lemma cons_point_one : cons_point ![1, 0] :=
  cons_point.hOne _ rfl
-- 1. FOUNDATIONAL LINES
-- We need the axes to project onto and intersect with.

def x_axis : Line := ![0, 1, 0] -- The line y = 0
def y_axis : Line := ![1, 0, 0] -- The line x = 0

/-- The X-axis passes through (0,0) and (1,0). -/
lemma axiom1_x_axis : Axiom1 ![0, 0] ![1, 0] x_axis := by
  -- Unfold the definitions; both evaluate to 0 + 0 = 0
  simp [Axiom1, is_contained, x_axis]

/-- The X-axis is constructible via Axiom 1. -/
lemma cons_x_axis : cons_line x_axis := by
  apply cons_line.axiom1 cons_point_origin cons_point_one
  exact axiom1_x_axis

/-- The Y-axis is constructible (perpendicular to X-axis through origin). -/
lemma cons_y_axis : cons_line y_axis := by
  sorry


-- "A point (a, b) is origami-constructible if and only if its
-- coordinates a and b are origami-constructible elements of R."

lemma cons_point_iff_coords_cons (a b : ℝ) :
  cons_point ![a, b] ↔ constructible_real_proj a ∧ constructible_real_proj b := by
  constructor
  · -- Forward direction (Point → Coordinates)
    -- Proof text: "...we can project the constructed point to the x-axis
    -- and y-axis (apply O4)..."
    intro h
    constructor
    · -- Project onto X-axis to show `a` is constructible
      -- 1. Apply Axiom 4 to get a line through (a,b) perpendicular to X-axis.
      -- 2. Intersect this line with the X-axis to get (a, 0).
      sorry
    · -- Project onto Y-axis to show `b` is constructible
      -- 1. Apply Axiom 4 to get a line through (a,b) perpendicular to Y-axis.
      -- 2. Intersect this line with the Y-axis to get (0, b).
      sorry

  · -- Backward direction (Coordinates → Point)
    -- Proof text: "...the point (a, b) can be origami-constructed as the
    -- intersection of such perpendicular lines."
    intro ⟨ha, hb⟩
    -- ha gives us a point with an 'a' coordinate, hb gives a point with a 'b' coordinate.
    -- 1. Project `ha` to get (a, 0) and `hb` to get (0, b).
    -- 2. Drop a perpendicular to X-axis at (a, 0).
    -- 3. Drop a perpendicular to Y-axis at (0, b).
    -- 4. Intersect these two lines to get (a, b).
    sorry

-- 3. HELPER FOR DISTANCE SYMMETRY
-- Folding distances might give us `-x` instead of `x`. We need to know that if
-- a coordinate is constructible, its negative is too (by reflecting across an axis).

lemma constructible_real_proj_neg (x : ℝ) :
  constructible_real_proj x ↔ constructible_real_proj (-x) := by
  sorry

-- 4. EQUIVALENCE OF DEFINITIONS
-- We can now use the coordinate projection logic to prove your equivalence theorem.

lemma constructible_real_defs_equiv (x : ℝ) :
  constructible_real_proj x ↔ constructible_real_dist x := by
  constructor
  · -- Proj → Dist
    -- If x is a coordinate of some constructible point, we can project it to
    -- an axis to get exactly (x, 0) or (0, x).
    -- The distance squared to the origin for either point is x^2 + 0^2 = x^2.
    intro h
    rcases h with ⟨P, hP, h_coord⟩
    sorry

  · -- Dist → Proj
    -- If x^2 = P_0^2 + P_1^2 for some constructible point P, we want to show x is a coordinate.
    -- We can use Axiom 5 to fold point P onto the X-axis such that the fold line
    -- passes through the Origin (0,0).
    -- Because the fold line passes through the origin, reflection preserves distance to the origin.
    -- Thus, the reflected point P' lies on the X-axis with the same distance, so P' = (±x, 0).
    -- This makes ±x a constructible coordinate, and by `constructible_real_proj_neg`, x is constructible.
    intro h
    rcases h with ⟨P, hP, h_dist⟩
    sorry





lemma constructible_real_of_point_x {P : Point} (hP : cons_point P) :
    constructible_real_proj (P 0) :=
  ⟨P, hP, Or.inl rfl⟩

lemma constructible_real_of_point_y {P : Point} (hP : cons_point P) :
    constructible_real_proj (P 1) :=
  ⟨P, hP, Or.inr rfl⟩

lemma constructible_real_zero : constructible_real_proj 0 :=
  constructible_real_of_point_x cons_point_origin

lemma constructible_real_one : constructible_real_proj 1 :=
  constructible_real_of_point_x cons_point_one
