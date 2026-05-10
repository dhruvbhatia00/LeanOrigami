import LeanOrigami.Basic

--proof of axiom2
theorem fold_is_perpendicular_bisector (L : Line) (P₁ P₂ : Point) (hL : valid L)
  (h_fold : folds_onto L P₁ P₂) :
  is_contained L ![(P₁ 0 + P₂ 0) / 2, (P₁ 1 + P₂ 1) / 2] ∧
  L 0 * (P₂ 1 - P₁ 1) = L 1 * (P₂ 0 - P₁ 0) := by
  rw [folds_onto] at h_fold
  subst h_fold
  constructor
  · -- Prove the midpoint is contained in L
    simp [is_contained, reflect]
    have hd : L 0 ^ 2 + L 1 ^ 2 ≠ 0 := hL
    -- Clear the denominators and solve the polynomial identity
    field_simp [hd]
    ring
  · -- Prove the vectors are orthogonal
    simp [reflect]
    have hd : L 0 ^ 2 + L 1 ^ 2 ≠ 0 := hL
    -- Clear the denominators and solve the polynomial identity
    field_simp [hd]

noncomputable def perpendicular_bisector (P₁ P₂ : Point) : Line :=
  ![(P₁ 0 - P₂ 0),
    (P₁ 1 - P₂ 1),
    ((P₁ 0)^2 - (P₂ 0)^2 + (P₁ 1)^2 - (P₂ 1)^2) / 2]
--iff statement of axiom2
theorem axiom2_characterization (L : Line) (P₁ P₂ : Point) (hL : valid L) :
  Axiom2 L P₁ P₂ ↔ ∃ a : ℝ, a ≠ 0 ∧ L = scaled a (perpendicular_bisector P₁ P₂) := by
constructor
· sorry
· sorry

-- The explicit coordinates of the base perpendicular line through P. -/
def perp_line (L₁ : Line) (P : Point) : Line :=
  ![- L₁ 1, L₁ 0, -(L₁ 1) * P 0 + (L₁ 0) * P 1]

/-- Any line L satisfying Axiom 4 is a scaled version of the perpendicular line. -/
theorem axiom4_is_perp_line (L : Line) (L₁ : Line) (P : Point) :
  Axiom4 L L₁ P ↔
  ∃ a : ℝ, a ≠ 0 ∧ L = scaled a (perp_line L₁ P) := by
  sorry

/-- Geometrically, a line L is tangent to a parabola with a given focus and directrix
    if the reflection of the focus across L is contained on the directrix. -/
def is_tangent_to_parabola (L : Line) (focus : Point) (directrix : Line) : Prop :=
  is_contained directrix (reflect L focus)

/-- Theorem: The fold line L from Axiom 6 is exactly the simultaneous common
    tangent to two distinct parabolas: one defined by (P₁, L₁) and the other by (P₂, L₂). -/


-- 1. GEOMETRIC FOUNDATION OF A PARABOLA

-- Distance squared between two points. -/
def dist_sq (P Q : Point) : ℝ :=
  (P 0 - Q 0)^2 + (P 1 - Q 1)^2

/-- Perpendicular distance squared from a point P to a line L. -/
noncomputable def point_line_dist_sq (P : Point) (L : Line) : ℝ :=
  (L 0 * P 0 + L 1 * P 1 - L 2)^2 / (L 0^2 + L 1^2)

/-- The standard locus definition of a parabola:
    A point Q is on the parabola if it is equidistant from the focus and the directrix. -/
def is_on_parabola (Q : Point) (focus : Point) (directrix : Line) : Prop :=
  dist_sq Q focus = point_line_dist_sq Q directrix


-- 2. ALGEBRAIC EQUATIONS FOR TANGENCY

/-- The algebraic polynomial equation that holds when L places P onto L_target.
    This is derived by unfolding `is_contained L_target (reflect L P)` and
    multiplying both sides by `(L 0^2 + L 1^2)` to clear the denominator. -/
def places_onto_eq (L L_target : Line) (P : Point) : Prop :=
  L_target 0 * (P 0 * (L 0^2 + L 1^2) - 2 * L 0 * (L 0 * P 0 + L 1 * P 1 - L 2)) +
  L_target 1 * (P 1 * (L 0^2 + L 1^2) - 2 * L 1 * (L 0 * P 0 + L 1 * P 1 - L 2)) =
  L_target 2 * (L 0^2 + L 1^2)

/-- A line L is tangent to the parabola (places the focus onto the directrix)
    if and only if its coefficients satisfy the cleared-denominator polynomial equation. -/
theorem tangent_characterization (L L_target : Line) (P : Point) (hL : valid L) :
  is_tangent_to_parabola L P L_target ↔ places_onto_eq L L_target P := by
  simp only [is_tangent_to_parabola, is_contained, reflect, places_onto_eq]
  have hd : L 0 ^ 2 + L 1 ^ 2 ≠ 0 := hL

  constructor
  · intro h
    -- Forward direction: Multiply both sides of the fractional equation by the denominator
    have h1 := congrArg (· * (L 0 ^ 2 + L 1 ^ 2)) h

    -- Use a calc block to bridge the algebraic gap using field_simp and ring
    calc
      L_target 0 * (P 0 * (L 0 ^ 2 + L 1 ^ 2) - 2 * L 0 * (L 0 * P 0 + L 1 * P 1 - L 2)) +
      L_target 1 * (P 1 * (L 0 ^ 2 + L 1 ^ 2) - 2 * L 1 * (L 0 * P 0 + L 1 * P 1 - L 2))
        = (L_target 0 * (P 0 - 2 * L 0 * (L 0 * P 0 + L 1 * P 1 - L 2) / (L 0 ^ 2 + L 1 ^ 2)) +
           L_target 1 * (P 1 - 2 * L 1 * (L 0 * P 0 + L 1 * P 1 - L 2) / (L 0 ^ 2 + L 1 ^ 2))) * (L 0 ^ 2 + L 1 ^ 2) :=
            by { field_simp [hd] }
      _ = L_target 2 * (L 0 ^ 2 + L 1 ^ 2) := h1

  · intro h
    -- Reverse direction: Divide both sides of the polynomial equation by the denominator
    have h1 := congrArg (· / (L 0 ^ 2 + L 1 ^ 2)) h

    -- Use a calc block to bridge back to the fractional equation
    calc
      L_target 0 * (P 0 - 2 * L 0 * (L 0 * P 0 + L 1 * P 1 - L 2) / (L 0 ^ 2 + L 1 ^ 2)) +
      L_target 1 * (P 1 - 2 * L 1 * (L 0 * P 0 + L 1 * P 1 - L 2) / (L 0 ^ 2 + L 1 ^ 2))
        = (L_target 0 * (P 0 * (L 0 ^ 2 + L 1 ^ 2) - 2 * L 0 * (L 0 * P 0 + L 1 * P 1 - L 2)) +
           L_target 1 * (P 1 * (L 0 ^ 2 + L 1 ^ 2) - 2 * L 1 * (L 0 * P 0 + L 1 * P 1 - L 2))) / (L 0 ^ 2 + L 1 ^ 2) :=
           by { field_simp [hd] }
      _ = L_target 2 * (L 0 ^ 2 + L 1 ^ 2) / (L 0 ^ 2 + L 1 ^ 2) := h1
      _ = L_target 2 := by rw [mul_div_cancel_right₀ _ hd]

-- 3. AXIOM 6 CHARACTERIZATION

/-- Axiom 6 trivially expands to the reflection tangency condition for two pairs. -/
theorem axiom6_is_simultaneous_tangent (L L₁ L₂ : Line) (P₁ P₂ : Point) :
  Axiom6 L L₁ L₂ P₁ P₂ ↔ is_tangent_to_parabola L P₁ L₁ ∧ is_tangent_to_parabola L P₂ L₂ := by
  -- Because both sides are definitionally identical, we just unfold them.
  simp only [Axiom6, is_tangent_to_parabola]

/-- The Algebraic Characterization of Axiom 6:
    Line L satisfies Axiom 6 if and only if its coefficients satisfy the system of
    two non-linear polynomial equations representing the two folding constraints. -/
theorem axiom6_characterization (L L₁ L₂ : Line) (P₁ P₂ : Point) (hL : valid L) :
  Axiom6 L L₁ L₂ P₁ P₂ ↔ places_onto_eq L L₁ P₁ ∧ places_onto_eq L L₂ P₂ := by
  -- Rewrite Axiom 6 into the two geometric tangency conditions,
  -- then rewrite both of those into their algebraic polynomial equivalents.
  rw [axiom6_is_simultaneous_tangent, tangent_characterization L L₁ P₁ hL, tangent_characterization L L₂ P₂ hL]
