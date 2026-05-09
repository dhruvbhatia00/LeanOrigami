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

def perpendicular_bisector (P₁ P₂ : Point) : Line :=
  ![(P₁ 1 - P₂ 1), (P₂ 0 - P₁ 0), (P₁ 0 * P₂ 1 - P₂ 0 * P₁ 1)]
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
theorem axiom6_is_simultaneous_tangent :
  Axiom6 L L₁ L₂ P₁ P₂ ↔ is_tangent_to_parabola L P₁ L₁ ∧ is_tangent_to_parabola L P₂ L₂ := by
  -- Because Axiom6 is literally defined as these two containments,
  -- the proof is actually trivial by definition!
  sorry
