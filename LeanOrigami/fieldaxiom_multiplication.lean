import LeanOrigami.Basic
import LeanOrigami.constructible
import LeanOrigami.Axioms

set_option linter.style.emptyLine false

/-- The product of two constructible numbers is constructible. -/
lemma constructible_real_proj_mul (a b : ℝ)
  (ha : constructible_real_proj a) (hb : constructible_real_proj b) :
  constructible_real_proj (a * b) := by

  -- STEP 1: Construct the foundational points (a, 0) and (0, b)
  have hP_a : cons_point ![a, 0] := by
    apply (cons_point_iff_coords_cons a 0).mpr
    exact ⟨ha, constructible_real_zero⟩

  have hP_b : cons_point ![0, b] := by
    apply (cons_point_iff_coords_cons 0 b).mpr
    exact ⟨constructible_real_zero, hb⟩
  -- STEP 2: The Guide Line
  -- The line passing through the unit point (1, 0) and the point (0, b).
  -- Equation: bX + Y = b

  let L_guide : Line := ![b, 1, b]
  have hL_guide_cons : cons_line L_guide := by
    have h_ax1 : Axiom1 ![1, 0] ![0, b] L_guide := by
      -- Evaluates b(1) + 1(0) = b and b(0) + 1(b) = b
      simp [Axiom1, is_contained, L_guide]

    apply cons_line.axiom1 cons_point_one hP_b
    · -- Goal 1: Prove L_guide is valid (b^2 + 1^2 ≠ 0)
      simp [valid, L_guide]
      intro h
      -- b^2 + 1 = 0 is impossible because 1 > 0 and b^2 ≥ 0
      have h_one : (1 : ℝ)^2 > 0 := by norm_num
      have h_b_sq : b^2 ≥ 0 := sq_nonneg b
      nlinarith [h_one, h_b_sq, h]
    · -- Goal 2: Prove it passes through both points
      exact h_ax1

  -- STEP 3: First fold for Parallel (The Perpendicular)
  -- Drop a perpendicular to L_guide through (a, 0).
  -- Normal vector is (-1, b). Equation: -X + bY = -a
  let L_perp : Line := ![-1, b, -a]
  have hL_perp_cons : cons_line L_perp := by
    -- First, prove the geometric relations for Axiom 4 hold true
    have h_ax4_1 : Axiom4 L_guide ![a, 0] L_perp := by
      -- Evaluates containment: -a + 0 = -a, and perpendicularity: -b + b = 0
      simp [Axiom4, is_contained, perpendicular, L_guide, L_perp]


    apply cons_line.axiom4 hL_guide_cons hP_a
    · -- Goal 1: Prove L_perp is valid ((-1)^2 + b^2 ≠ 0)
      simp [valid, L_perp]
      intro h
      -- 1 + b^2 = 0 is impossible because 1 > 0 and b^2 ≥ 0
      have h_one : (1 : ℝ) > 0 := by norm_num
      have h_b_sq : b^2 ≥ 0 := sq_nonneg b
      nlinarith [h_one, h_b_sq, h]
    · -- Goal 2: Prove it satisfies Axiom 4
      exact h_ax4_1

  -- STEP 4: Second fold for Parallel (The Actual Parallel Line)
  -- Drop a perpendicular to L_perp through (a, 0).
  -- Normal vector is (b, 1). Equation: bX + Y = ab
  let L_parallel : Line := ![b, 1, a * b]
  have hL_parallel_cons : cons_line L_parallel := by
    have h_ax4_2 : Axiom4 L_perp ![a, 0] L_parallel := by
      -- Evaluates containment: b*a + 0 = a*b, and perpendicularity: -1*b + b*1 = 0
      simp [Axiom4, is_contained, perpendicular, L_perp, L_parallel]
      ring

    apply cons_line.axiom4 hL_perp_cons hP_a
    · -- Goal 1: Prove L_parallel is valid (b^2 + 1^2 ≠ 0)
      simp [valid, L_parallel]
      intro h
      -- 1 + b^2 = 0 is impossible because 1 > 0 and b^2 ≥ 0
      have h_one : (1 : ℝ) > 0 := by norm_num
      have h_b_sq : b^2 ≥ 0 := sq_nonneg b
      nlinarith [h_one, h_b_sq, h]
    · -- Goal 2: Prove it satisfies Axiom 4
      exact h_ax4_2

  -- STEP 5: The Intersection
  -- Intersect the parallel line with the Y-axis (x = 0).
  let P_ab : Point := ![0, a * b]
  have hP_ab_cons : cons_point P_ab := by
    have h_int : intersects_at L_parallel y_axis P_ab := by
      -- Unfold the definitions. Lean evaluates the matrix multiplication
      -- and sees 0 = 0 and ab = ab.
      simp [intersects_at, is_contained, L_parallel, y_axis, P_ab]


    -- Apply the intersection axiom!
    exact cons_point.hIntersect hL_parallel_cons cons_y_axis P_ab h_int

  -- STEP 6: Final Extraction
  -- Since P_ab is constructible, its y-coordinate (a * b) is constructible.
  exact constructible_real_of_point_y hP_ab_cons

-- We now move on to the inverse.
/-- The inverse of a non-zero constructible number is constructible. -/
 lemma constructible_real_proj_inv (a : ℝ)
  (ha : constructible_real_proj a) (ha_nz : a ≠ 0) :
  constructible_real_proj (a⁻¹) := by

  -- STEP 1: Construct the foundational points
  -- We need (a, 0) and the unit points (1, 0) and (0, 1)
  have hP_a : cons_point ![a, 0] := by
    apply (cons_point_iff_coords_cons a 0).mpr
    exact ⟨ha, constructible_real_zero⟩

  have hP_one_x : cons_point ![1, 0] := cons_point_one

  have hP_one_y : cons_point ![0, 1] := by
    apply (cons_point_iff_coords_cons 0 1).mpr
    exact ⟨constructible_real_zero, constructible_real_one⟩

 -- STEP 2: The Guide Line
  -- The line passing through (a, 0) and (0, 1).
  -- Equation: X + aY = a
  let L_guide : Line := ![1, a, a]
  have hL_guide_cons : cons_line L_guide := by
    have h_ax1 : Axiom1 ![a, 0] ![0, 1] L_guide := by
      -- Evaluates 1(a) + a(0) = a and 1(0) + a(1) = a
      simp [Axiom1, is_contained, L_guide]

    apply cons_line.axiom1 hP_a hP_one_y
    · -- Goal 1: Prove L_guide is valid (1^2 + a^2 ≠ 0)
      simp [valid, L_guide]
      intro h
      have h_one : (1 : ℝ) > 0 := by norm_num
      have h_a_sq : a^2 ≥ 0 := sq_nonneg a
      nlinarith [h_one, h_a_sq, h]
    · exact h_ax1

  -- STEP 3: First fold for Parallel (The Perpendicular)
  -- Drop a perpendicular to L_guide through (1, 0).
  -- Normal vector is (-a, 1). Equation: -aX + Y = -a
  let L_perp : Line := ![-a, 1, -a]
  have hL_perp_cons : cons_line L_perp := by
    have h_ax4_1 : Axiom4 L_guide ![1, 0] L_perp := by
      -- Evaluates containment: -a(1) + 0 = -a, and perpendicularity: 1(-a) + a(1) = 0
      simp [Axiom4, is_contained, perpendicular, L_guide, L_perp]


    apply cons_line.axiom4 hL_guide_cons hP_one_x
    · -- Goal 1: Prove L_perp is valid ((-a)^2 + 1^2 ≠ 0)
      simp [valid, L_perp]
      intro h
      have h_one : (1 : ℝ) > 0 := by norm_num
      have h_a_sq : a^2 ≥ 0 := sq_nonneg a
      nlinarith [h_one, h_a_sq, h]
    · exact h_ax4_1

  -- STEP 4: Second fold for Parallel (The Actual Parallel Line)
  -- Drop a perpendicular to L_perp through (1, 0).
  -- Normal vector is (1, a). Equation: X + aY = 1
  let L_parallel : Line := ![1, a, 1]
  have hL_parallel_cons : cons_line L_parallel := by
    have h_ax4_2 : Axiom4 L_perp ![1, 0] L_parallel := by
      -- Evaluates containment: 1(1) + a(0) = 1, and perpendicularity: -a(1) + 1(a) = 0
      simp [Axiom4, is_contained, perpendicular, L_perp, L_parallel]


    apply cons_line.axiom4 hL_perp_cons hP_one_x
    · -- Goal 1: Prove L_parallel is valid (1^2 + a^2 ≠ 0)
      simp [valid, L_parallel]
      intro h
      have h_one : (1 : ℝ) > 0 := by norm_num
      have h_a_sq : a^2 ≥ 0 := sq_nonneg a
      nlinarith [h_one, h_a_sq, h]
    · exact h_ax4_2

  -- STEP 5: The Intersection
  -- Intersect the parallel line with the Y-axis (x = 0).
  let P_inv : Point := ![0, a⁻¹]
  have hP_inv_cons : cons_point P_inv := by
    have h_int : intersects_at L_parallel y_axis P_inv := by
      -- Unfold the definitions. Lean evaluates the matrix multiplication
      -- and reduces it to a * a⁻¹ = 1.
      simp [intersects_at, is_contained, L_parallel, y_axis, P_inv]
      -- Use the "Group With Zero" version of the theorem!
      exact mul_inv_cancel₀ ha_nz

    -- Apply the intersection axiom!
    exact cons_point.hIntersect hL_parallel_cons cons_y_axis P_inv h_int

  -- STEP 6: Final Extraction
  exact constructible_real_of_point_y hP_inv_cons
