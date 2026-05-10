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

-- The X-axis is constructible via Axiom 1.
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
-- HELPER: Constructing the line y = x (The Diagonal)
def y_eq_x : Line := ![-1, 1, 0] -- The line -x + y = 0

/-- Folding (1,0) onto the Y-axis through the origin creates the line y = x. -/
lemma axiom5_y_eq_x : Axiom5 ![1, 0] ![0, 0] y_axis y_eq_x := by
  -- Axiom 5: is_contained L P₂ ∧ is_contained L₁ (reflect L P₁)
  -- By folding (1,0) onto the y-axis, the crease through the origin is y=x.
  simp [Axiom5, is_contained, reflect, y_axis, y_eq_x]
  norm_num

/-- The diagonal y = x is constructible via Axiom 5. -/
lemma cons_y_eq_x : cons_line y_eq_x := by
  apply cons_line.axiom5 cons_point_one cons_point_origin cons_y_axis
  · -- Goal 1: Prove y_eq_x is a valid line ((-1)^2 + 1^2 ≠ 0)
    simp [valid, y_eq_x]
  · -- Goal 2: Prove it satisfies Axiom 5
    exact axiom5_y_eq_x

-- HELPER: Constructing the line y = -x
def y_eq_neg_x : Line := ![1, 1, 0]

/-- The line y = -x is constructible by dropping a perpendicular to y = x through the origin. -/
lemma cons_y_eq_neg_x : cons_line y_eq_neg_x := by
  have h_ax4 : Axiom4 y_eq_x ![0, 0] y_eq_neg_x := by
    simp [Axiom4, is_contained, perpendicular, y_eq_x, y_eq_neg_x]
  apply cons_line.axiom4 cons_y_eq_x cons_point_origin
  · simp [valid, y_eq_neg_x]
  · exact h_ax4

-- HELPER : Constructing the vertical line x = a
lemma cons_line_x_eq (a : ℝ) (ha : constructible_real_proj a) : cons_line ![1, 0, a] := by
  rcases ha with ⟨P, hP, h_coord⟩
  rcases h_coord with hx | hy
  · -- Case 1: P 0 = a. We drop a perpendicular from P to the X-axis.
    have h_axiom4 : Axiom4 x_axis P ![1, 0, a] := by
      simp [Axiom4, is_contained, perpendicular, x_axis, ← hx]
    apply cons_line.axiom4 cons_x_axis hP
    · simp [valid]
    · exact h_axiom4
  · -- Case 2: P 1 = a. We intersect y=a with y=x to get (a,a), then drop a perpendicular to the X-axis.
    -- Step 1: Construct the line y=a using Axiom 4 from point P to the Y-axis.
    have h_axiom4_ya : Axiom4 y_axis P ![0, 1, a] := by
      simp [Axiom4, is_contained, perpendicular, y_axis, ← hy]
    have h_ya : cons_line ![0, 1, a] := by
      apply cons_line.axiom4 cons_y_axis hP
      · simp [valid]
      · exact h_axiom4_ya

    -- Step 2: Intersect y=a with y=x to construct the point (a, a).
    have h_int : intersects_at ![0, 1, a] y_eq_x ![a, a] := by
      simp [intersects_at, is_contained, y_eq_x]
    have h_paa : cons_point ![a, a] := cons_point.hIntersect h_ya cons_y_eq_x ![a, a] h_int

    -- Step 3: Construct the line x=a by dropping a perpendicular from (a, a) to the X-axis.
    have h_axiom4_xa : Axiom4 x_axis ![a, a] ![1, 0, a] := by
      simp [Axiom4, is_contained, perpendicular, x_axis]
    apply cons_line.axiom4 cons_x_axis h_paa
    · simp [valid]
    · exact h_axiom4_xa

-- HELPER : Constructing the horizontal line y = b
lemma cons_line_y_eq (b : ℝ) (hb : constructible_real_proj b) : cons_line ![0, 1, b] := by
  rcases hb with ⟨P, hP, h_coord⟩
  rcases h_coord with hx | hy
  · -- Case 1: P 0 = b. We intersect x=b with y=x to get (b,b), then drop a perpendicular to the Y-axis.
    -- Step 1: Construct the line x=b using Axiom 4 from point P to the X-axis.
    have h_axiom4_xb : Axiom4 x_axis P ![1, 0, b] := by
      simp [Axiom4, is_contained, perpendicular, x_axis, ← hx]
    have h_xb : cons_line ![1, 0, b] := by
      apply cons_line.axiom4 cons_x_axis hP
      · simp [valid]
      · exact h_axiom4_xb

    -- Step 2: Intersect x=b with y=x to construct the point (b, b).
    have h_int : intersects_at ![1, 0, b] y_eq_x ![b, b] := by
      simp [intersects_at, is_contained, y_eq_x]
    have h_pbb : cons_point ![b, b] := cons_point.hIntersect h_xb cons_y_eq_x ![b, b] h_int

    -- Step 3: Construct the line y=b by dropping a perpendicular from (b, b) to the Y-axis.
    have h_axiom4_yb : Axiom4 y_axis ![b, b] ![0, 1, b] := by
      simp [Axiom4, is_contained, perpendicular, y_axis]
    apply cons_line.axiom4 cons_y_axis h_pbb
    · simp [valid]
    · exact h_axiom4_yb

  · -- Case 2: P 1 = b. We drop a perpendicular from P to the Y-axis.
    have h_axiom4 : Axiom4 y_axis P ![0, 1, b] := by
      simp [Axiom4, is_contained, perpendicular, y_axis, ← hy]
    apply cons_line.axiom4 cons_y_axis hP
    · simp [valid]
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

-- Symmetry lemma
-- HELPER: Forward direction of symmetry
lemma constructible_real_proj_neg_forward (x : ℝ) :
  constructible_real_proj x → constructible_real_proj (-x) := by
  intro hx
  -- 1. Construct the vertical line x = x using our earlier helper
  have hLx := cons_line_x_eq x hx

  -- 2. Intersect x = x with y = -x to get the point (x, -x)
  have h_int : intersects_at ![1, 0, x] y_eq_neg_x ![x, -x] := by
    simp [intersects_at, is_contained, y_eq_neg_x]

  have hP : cons_point ![x, -x] :=
    cons_point.hIntersect hLx cons_y_eq_neg_x ![x, -x] h_int

  -- 3. Extract the y-coordinate (-x) using your foundational lemma
  exact constructible_real_of_point_y hP

-- MAIN SYMMETRY LEMMA
lemma constructible_real_proj_neg (x : ℝ) :
  constructible_real_proj x ↔ constructible_real_proj (-x) := by
  constructor
  · -- Forward: x → -x
    exact constructible_real_proj_neg_forward x
  · -- Backward: -x → x
    intro h
    -- Apply the forward proof to (-x) to get (-(-x))
    have h2 := constructible_real_proj_neg_forward (-x) h
    -- Lean knows that -(-x) is definitionally equal to x
    rw [neg_neg] at h2
    exact h2

open Real

-- HELPER 3: Folding a point onto the X-axis through the origin
set_option linter.flexible false in
lemma cons_point_fold_x_axis (P : Point) (hP : cons_point P) :
  ∃ P' : Point, cons_point P' ∧ P' 1 = 0 ∧ (P' 0)^2 + (P' 1)^2 = (P 0)^2 + (P 1)^2 := by

  -- STEP 1: Case Split
  -- What if P is already sitting on the X-axis?
  by_cases h_y : P 1 = 0
  · -- If P is already on the X-axis, we don't need to fold! P' is just P.
    use P

  · -- STEP 2: The Non-Trivial Fold
    -- If P is not on the X-axis, we must fold it.
    -- Let r be the distance to the origin.
    let r := Real.sqrt ((P 0)^2 + (P 1)^2)

    -- The fold line L bisects the angle between P and the target point (r, 0).
    -- Its normal vector is P - (r, 0) = (P 0 - r, P 1). It passes through origin, so L 2 = 0.
    let L : Line := ![P 0 - r, P 1, 0]

    -- Prove L is a valid line (since P 1 ≠ 0, the normal vector cannot be 0)
    have hL_valid : valid L := by
      simp [valid, L]
      intro h
      -- Since P 1 ≠ 0 (from h_y), its square is strictly positive.
      have h_pos : (P 1)^2 > 0 := sq_pos_of_ne_zero h_y
      -- The square of the x-component is at least non-negative.
      have h_sq : (P 0 - r)^2 ≥ 0 := sq_nonneg (P 0 - r)
      -- A positive + a non-negative cannot equal 0. nlinarith sees the contradiction!
      nlinarith [h_pos, h_sq, h]

    -- Prove L satisfies Axiom 5 for folding P onto the X-axis, passing through Origin
    have h_ax5 : Axiom5 P ![0, 0] x_axis L := by
      simp [Axiom5, is_contained, reflect, x_axis, L]

      -- Step 1: Extract the geometric distance fact r^2 = P_0^2 + P_1^2
      have hr : r^2 - ((P 0)^2 + (P 1)^2) = 0 := by
        have h_pos : 0 ≤ (P 0)^2 + (P 1)^2 := add_nonneg (sq_nonneg (P 0)) (sq_nonneg (P 1))
        have h_sq : r^2 = (P 0)^2 + (P 1)^2 := Real.sq_sqrt h_pos
        exact sub_eq_zero.mpr h_sq

      -- Step 2: Clear the fraction by putting everything over the non-zero denominator
      have hL_val : (P 0 - r)^2 + (P 1)^2 ≠ 0 := hL_valid
      field_simp [hL_val]

      -- Step 3: field_simp already turned this into Numerator = Denominator * 0.
      -- linear_combination can solve this directly!
      linear_combination P 1 * hr

    have hL_cons : cons_line L :=
      cons_line.axiom5 hP cons_point_origin cons_x_axis hL_valid h_ax5

    -- STEP 3: Construct the Perpendicular
    -- We construct L_perp, the line through P perpendicular to our crease line L.
    -- The intersection of L_perp and the X-axis will be our final point!
    let L_perp : Line := ![-L 1, L 0, -(L 1) * P 0 + L 0 * P 1]

    have h_ax4 : Axiom4 L P L_perp := by
      simp [Axiom4, is_contained, perpendicular, L, L_perp]
      ring

    have hL_perp_valid : valid L_perp := by
      simp [valid, L_perp]
      -- simp automatically simplifies (-L 1)^2 into L 1^2
      intro h

      apply hL_valid

      -- Now we just swap the order of addition to match h perfectly!
      calc L 0 ^ 2 + L 1 ^ 2
        _ = L 1 ^ 2 + L 0 ^ 2 := by ring
        _ = 0 := h

    have hL_perp_cons : cons_line L_perp :=
      cons_line.axiom4 hL_cons hP hL_perp_valid h_ax4

    -- STEP 4: Intersect to find P'
    -- Intersect L_perp with the X-axis to geometrically construct P' = (r, 0)
    let P' : Point := ![r, 0]

    have h_int : intersects_at L_perp x_axis P' := by
      -- Expand all definitions down to their coordinates
      simp [intersects_at, is_contained, x_axis, L_perp, P', L]
      -- It turns out this is a pure algebraic identity! We don't even need r^2 here.
      -- (If your definition of intersects_at requires proving the lines aren't parallel,
      -- the fact that P 1 ≠ 0 from our by_cases `h_y` handles it).
      try ring

    have hP'_cons : cons_point P' :=
      cons_point.hIntersect hL_perp_cons cons_x_axis P' h_int

    -- STEP 5: Final Verification
    use P'
    refine ⟨hP'_cons, rfl, ?_⟩
    -- Simplify the goal to evaluate P' 0 and P' 1
    simp [P']
    -- The goal is now r^2 = (P 0)^2 + (P 1)^2.
    -- We just apply the exact same Real.sq_sqrt logic we used in Axiom 5!
    have h_pos : 0 ≤ (P 0)^2 + (P 1)^2 := add_nonneg (sq_nonneg (P 0)) (sq_nonneg (P 1))
    exact Real.sq_sqrt h_pos

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
