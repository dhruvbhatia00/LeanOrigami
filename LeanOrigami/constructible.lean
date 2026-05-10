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
  · -- Goal 1: Prove the x_axis is a valid line (0^2 + 1^2 ≠ 0)
    simp [valid, x_axis]
  · -- Goal 2: Prove it satisfies Axiom 1
    exact axiom1_x_axis

/-- The Y-axis passes through (0,0) and is perpendicular to the X-axis. -/
lemma axiom4_y_axis : Axiom4 x_axis ![0, 0] y_axis := by
  -- Unfold the definitions to evaluate containment and the perpendicular dot product
  simp [Axiom4, is_contained, perpendicular, x_axis, y_axis]

/-- The Y-axis is constructible via Axiom 4. -/
lemma cons_y_axis : cons_line y_axis := by
  apply cons_line.axiom4 cons_x_axis cons_point_origin
  · -- Goal 1: Prove the y_axis is a valid line (1^2 + 0^2 ≠ 0)
    simp [valid, y_axis]
  · -- Goal 2: Prove it satisfies Axiom 4
    exact axiom4_y_axis

-- HELPER 1: Constructing the vertical line x = a
lemma cons_line_x_eq (a : ℝ) (ha : constructible_real_proj a) : cons_line ![1, 0, a] := by
  rcases ha with ⟨P, hP, h_coord⟩
  rcases h_coord with hx | hy
  · -- Case 1: P 0 = a. We drop a perpendicular from P to the X-axis.
    have h_axiom4 : Axiom4 x_axis P ![1, 0, a] := by
      simp [Axiom4, is_contained, perpendicular, x_axis, ← hx]
    apply cons_line.axiom4 cons_x_axis hP
    · simp [valid, x_axis]
    · exact h_axiom4
  · -- Case 2: P 1 = a. Requires constructing y=x and reflecting P.
    sorry

-- HELPER 2: Constructing the horizontal line y = b
lemma cons_line_y_eq (b : ℝ) (hb : constructible_real_proj b) : cons_line ![0, 1, b] := by
  rcases hb with ⟨P, hP, h_coord⟩
  rcases h_coord with hx | hy
  · -- Case 1: P 0 = b. Requires constructing y=x and reflecting P.
    sorry
  · -- Case 2: P 1 = b. We drop a perpendicular from P to the Y-axis.
    have h_axiom4 : Axiom4 y_axis P ![0, 1, b] := by
      simp [Axiom4, is_contained, perpendicular, y_axis, ← hy]
    apply cons_line.axiom4 cons_y_axis hP
    · simp [valid, y_axis]
    · exact h_axiom4

-- "A point (a, b) is origami-constructible if and only if its
-- coordinates a and b are origami-constructible elements of R."

lemma cons_point_iff_coords_cons (a b : ℝ) :
  cons_point ![a, b] ↔ constructible_real_proj a ∧ constructible_real_proj b := by
  constructor
  · -- Forward direction (Point → Coordinates)
    intro h
    constructor
    · -- Show `a` is constructible.
      -- We already have `![a, b]`, and Lean knows `![a, b] 0 = a`.
      exact constructible_real_of_point_x h
    · -- Show `b` is constructible.
      -- We already have `![a, b]`, and Lean knows `![a, b] 1 = b`.
      exact constructible_real_of_point_y h

  · -- Backward direction (Coordinates → Point)
    intro ⟨ha, hb⟩
    -- 1. Construct the perpendicular line x = a
    have hLx := cons_line_x_eq a ha
    -- 2. Construct the perpendicular line y = b
    have hLy := cons_line_y_eq b hb

    -- 3. Prove that these two lines intersect exactly at ![a, b]
    have h_int : intersects_at ![1, 0, a] ![0, 1, b] ![a, b] := by
      simp [intersects_at, is_contained]

    -- 4. Apply the intersection construction axiom
    exact cons_point.hIntersect hLx hLy ![a, b] h_int

-- HELPER FOR DISTANCE SYMMETRY
-- Folding distances might give us `-x` instead of `x`. We need to know that if
-- a coordinate is constructible, its negative is too (by reflecting across an axis).

lemma constructible_real_proj_neg (x : ℝ) :
  constructible_real_proj x ↔ constructible_real_proj (-x) := by
  sorry

-- HELPER: Folding a point onto the X-axis through the origin
-- This encapsulates Axiom 5, Axiom 4, the Intersection, and the distance proof.
lemma cons_point_fold_x_axis (P : Point) (hP : cons_point P) :
  ∃ P' : Point, cons_point P' ∧ P' 1 = 0 ∧ (P' 0)^2 + (P' 1)^2 = (P 0)^2 + (P 1)^2 := by
  sorry

-- EQUIVALENCE OF DEFINITIONS
-- We can now use the coordinate projection logic to prove your equivalence theorem.

lemma constructible_real_defs_equiv (x : ℝ) :
  constructible_real_proj x ↔ constructible_real_dist x := by
  constructor
  · -- Proj → Dist
    intro h
    -- Because `x` is a constructible coordinate (h) and `0` is a constructible
    -- coordinate, the point (x, 0) is constructible by our previous lemma.
    have h_pt : cons_point ![x, 0] := by
      apply (cons_point_iff_coords_cons x 0).mpr
      exact ⟨h, constructible_real_zero⟩

    -- We use ![x, 0] as our witness for the distance definition.
    use ![x, 0]
    constructor
    · exact h_pt
    · -- Prove that (![x, 0] 0)^2 + (![x, 0] 1)^2 = x^2
      simp

  · -- Dist → Proj
    intro h
    rcases h with ⟨P, hP, h_dist⟩

    -- 1. Use our geometric helper to fold P onto the X-axis
    have h_fold := cons_point_fold_x_axis P hP
    rcases h_fold with ⟨P', hP'_cons, hP'_y, hP'_dist⟩

    -- 2. Since P' is on the X-axis, its Y-coordinate squared is 0
    have h_y_sq : (P' 1)^2 = 0 := by
      rw [hP'_y]
      ring

    -- 3. Substitute this 0 into the distance preservation equation
    rw [h_y_sq, add_zero] at hP'_dist
    rw [h_dist] at hP'_dist

    -- 4. We now have (P' 0)^2 = x^2. Mathematically, this means P'_0 = x OR P'_0 = -x.
    -- Lean's `sq_eq_sq_iff_eq_or_eq_neg` handles this exact algebraic step!
    have h_eq_or : P' 0 = x ∨ P' 0 = -x := by
      exact sq_eq_sq_iff_eq_or_eq_neg.mp hP'_dist

    -- 5. Branch on whether P' landed on the positive or negative side of the origin
    rcases h_eq_or with hx | hnegx
    · -- Case 1: P' 0 = x
      -- Since P' is constructible, and its x-coordinate is x, x is constructible!
      exact ⟨P', hP'_cons, Or.inl hx⟩

    · -- Case 2: P' 0 = -x
      -- Since P' is constructible, -x is a constructible coordinate.
      have h_neg_cons : constructible_real_proj (-x) := ⟨P', hP'_cons, Or.inl hnegx⟩
      -- By our symmetry helper, if -x is constructible, x must also be constructible!
      exact (constructible_real_proj_neg x).mpr h_neg_cons
