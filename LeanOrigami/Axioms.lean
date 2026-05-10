import LeanOrigami.Basic

/-!
# Huzita-Hatori axioms and algebraic specifications

This file owns the axiom predicates and the algebraic forms used by later
constructibility arguments.  `Basic.lean` intentionally remains only analytic
geometry: points, lines, incidence, reflection, and elementary line relations.
-/

/-! ## Axiom predicates -/

def Axiom1 (P₁ P₂ : Point) (L : Line) : Prop :=
  is_contained L P₁ ∧ is_contained L P₂

def Axiom2 (P₁ P₂ : Point) (L : Line) : Prop :=
  folds_onto L P₁ P₂

def Axiom3 (L₁ L₂ : Line) (L : Line) : Prop :=
  reflect_line L L₁ = L₂

def Axiom4 (L₁ : Line) (P₁ : Point) (L : Line) : Prop :=
  is_contained L P₁ ∧ perpendicular L₁ L

def Axiom5 (P₁ P₂ : Point) (L₁ : Line) (L : Line) : Prop :=
  is_contained L P₂ ∧ is_contained L₁ (reflect L P₁)

def Axiom6 (P₁ P₂ : Point) (L₁ L₂ : Line) (L : Line) : Prop :=
  is_contained L₁ (reflect L P₁) ∧ is_contained L₂ (reflect L P₂)

def Axiom7 (L₁ : Line) (P : Point) (L : Line) : Prop :=
  is_contained L₁ (reflect L P) ∧ perpendicular L₁ L

/-! ## Shared algebraic reflection condition -/

/--
The cleared-denominator equation for saying that reflection across `L` places
point `P` onto target line `Ltarget`.

This is the algebraic core used by Axioms 5, 6, and 7.
-/
def places_onto_eq (L Ltarget : Line) (P : Point) : Prop :=
  Ltarget 0 *
      (P 0 * (L 0^2 + L 1^2) -
        2 * L 0 * (L 0 * P 0 + L 1 * P 1 - L 2)) +
    Ltarget 1 *
      (P 1 * (L 0^2 + L 1^2) -
        2 * L 1 * (L 0 * P 0 + L 1 * P 1 - L 2)) =
    Ltarget 2 * (L 0^2 + L 1^2)

def is_tangent_to_parabola (L : Line) (focus : Point) (directrix : Line) : Prop :=
  is_contained directrix (reflect L focus)

theorem tangent_characterization (L Ltarget : Line) (P : Point) (hL : valid L) :
    is_tangent_to_parabola L P Ltarget ↔ places_onto_eq L Ltarget P := by
  simp only [is_tangent_to_parabola, is_contained, reflect, places_onto_eq]
  have hd : L 0 ^ 2 + L 1 ^ 2 ≠ 0 := hL
  constructor
  · intro h
    have h1 := congrArg (· * (L 0 ^ 2 + L 1 ^ 2)) h
    calc
      Ltarget 0 *
          (P 0 * (L 0 ^ 2 + L 1 ^ 2) -
            2 * L 0 * (L 0 * P 0 + L 1 * P 1 - L 2)) +
        Ltarget 1 *
          (P 1 * (L 0 ^ 2 + L 1 ^ 2) -
            2 * L 1 * (L 0 * P 0 + L 1 * P 1 - L 2))
          =
        (Ltarget 0 *
            (P 0 -
              2 * L 0 * (L 0 * P 0 + L 1 * P 1 - L 2) /
                (L 0 ^ 2 + L 1 ^ 2)) +
          Ltarget 1 *
            (P 1 -
              2 * L 1 * (L 0 * P 0 + L 1 * P 1 - L 2) /
                (L 0 ^ 2 + L 1 ^ 2))) *
          (L 0 ^ 2 + L 1 ^ 2) := by
            field_simp [hd]
      _ = Ltarget 2 * (L 0 ^ 2 + L 1 ^ 2) := h1
  · intro h
    have h1 := congrArg (· / (L 0 ^ 2 + L 1 ^ 2)) h
    calc
      Ltarget 0 *
          (P 0 -
            2 * L 0 * (L 0 * P 0 + L 1 * P 1 - L 2) /
              (L 0 ^ 2 + L 1 ^ 2)) +
        Ltarget 1 *
          (P 1 -
            2 * L 1 * (L 0 * P 0 + L 1 * P 1 - L 2) /
              (L 0 ^ 2 + L 1 ^ 2))
          =
        (Ltarget 0 *
            (P 0 * (L 0 ^ 2 + L 1 ^ 2) -
              2 * L 0 * (L 0 * P 0 + L 1 * P 1 - L 2)) +
          Ltarget 1 *
            (P 1 * (L 0 ^ 2 + L 1 ^ 2) -
              2 * L 1 * (L 0 * P 0 + L 1 * P 1 - L 2))) /
          (L 0 ^ 2 + L 1 ^ 2) := by
            field_simp [hd]
      _ = Ltarget 2 * (L 0 ^ 2 + L 1 ^ 2) / (L 0 ^ 2 + L 1 ^ 2) := h1
      _ = Ltarget 2 := by rw [mul_div_cancel_right₀ _ hd]

/-! ## Axiom 1 -/

namespace Axiom1Spec

def lineThrough (P₁ P₂ : Point) : Line :=
  ![P₂ 1 - P₁ 1, P₁ 0 - P₂ 0,
    (P₂ 1 - P₁ 1) * P₁ 0 + (P₁ 0 - P₂ 0) * P₁ 1]

/--
Homogeneous coefficient condition for a line through two points.

The first conjunct anchors the line at `P₁`; the second says that the line's
normal vector is orthogonal to the displacement from `P₁` to `P₂`.
-/
def lineThroughCondition (P₁ P₂ : Point) (L : Line) : Prop :=
  is_contained L P₁ ∧
    L 0 * (P₂ 0 - P₁ 0) + L 1 * (P₂ 1 - P₁ 1) = 0

theorem axiom1_lineThroughCondition (P₁ P₂ : Point) (L : Line) :
    Axiom1 P₁ P₂ L ↔ lineThroughCondition P₁ P₂ L := by
  constructor
  · intro h
    rcases h with ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    simp [is_contained] at h1 h2
    linear_combination h2 - h1
  · intro h
    rcases h with ⟨h1, hdir⟩
    refine ⟨h1, ?_⟩
    simp [is_contained] at h1 hdir ⊢
    linear_combination h1 + hdir

theorem axiom1_scaled_iff {P₁ P₂ : Point} {L : Line}
    (hsep : P₁ 0 ≠ P₂ 0 ∨ P₁ 1 ≠ P₂ 1) :
    Axiom1 P₁ P₂ L ↔ ∃ a : ℝ, L = scaled a (lineThrough P₁ P₂) := by
  rw [axiom1_lineThroughCondition]
  constructor
  · intro h
    rcases h with ⟨hP, hdir⟩
    simp [is_contained] at hP hdir
    rcases hsep with hx | hy
    · use -(L 1) / (P₂ 0 - P₁ 0)
      ext i
      fin_cases i
      · simp [scaled, lineThrough]
        field_simp [sub_ne_zero.mpr (Ne.symm hx)]
        ring_nf
        nlinarith [hdir]
      · simp [scaled, lineThrough]
        field_simp [sub_ne_zero.mpr (Ne.symm hx)]
        ring
      · simp [scaled, lineThrough]
        field_simp [sub_ne_zero.mpr (Ne.symm hx)]
        ring_nf
        linear_combination P₁ 0 * hdir - (P₂ 0 - P₁ 0) * hP
    · use (L 0) / (P₂ 1 - P₁ 1)
      ext i
      fin_cases i
      · simp [scaled, lineThrough]
        field_simp [sub_ne_zero.mpr (Ne.symm hy)]
        try ring
      · simp [scaled, lineThrough]
        field_simp [sub_ne_zero.mpr (Ne.symm hy)]
        ring_nf
        nlinarith [hdir]
      · simp [scaled, lineThrough]
        field_simp [sub_ne_zero.mpr (Ne.symm hy)]
        ring_nf
        linear_combination P₁ 1 * hdir - (P₂ 1 - P₁ 1) * hP
  · intro h
    rcases h with ⟨a, rfl⟩
    constructor <;> simp [is_contained, scaled, lineThrough] <;> ring

end Axiom1Spec

/-! ## Axiom 2 -/

namespace Axiom2Spec

noncomputable def midpoint (P₁ P₂ : Point) : Point :=
  ![(P₁ 0 + P₂ 0) / 2, (P₁ 1 + P₂ 1) / 2]

noncomputable def perpendicularBisector (P₁ P₂ : Point) : Line :=
  ![P₂ 0 - P₁ 0, P₂ 1 - P₁ 1,
    ((P₂ 0 - P₁ 0) * (P₁ 0 + P₂ 0) +
      (P₂ 1 - P₁ 1) * (P₁ 1 + P₂ 1)) / 2]

/--
Homogeneous coefficient condition for the perpendicular bisector fold.

The line contains the midpoint and has normal vector parallel to the segment
from `P₁` to `P₂`.  This avoids splitting into vertical/non-vertical cases.
-/
def perpendicularBisectorCondition (P₁ P₂ : Point) (L : Line) : Prop :=
  is_contained L (midpoint P₁ P₂) ∧
    L 0 * (P₂ 1 - P₁ 1) = L 1 * (P₂ 0 - P₁ 0)

theorem axiom2_perpendicularBisector_forward (P₁ P₂ : Point) (L : Line) (hL : valid L) :
    Axiom2 P₁ P₂ L → perpendicularBisectorCondition P₁ P₂ L := by
  intro h
  rw [Axiom2, folds_onto] at h
  subst h
  constructor
  · simp [midpoint, is_contained, reflect]
    have hd : L 0 ^ 2 + L 1 ^ 2 ≠ 0 := hL
    field_simp [hd]
    ring
  · simp [reflect]
    have hd : L 0 ^ 2 + L 1 ^ 2 ≠ 0 := hL
    field_simp [hd]

set_option linter.flexible false in
theorem axiom2_perpendicularBisector_reverse (P₁ P₂ : Point) (L : Line) (hL : valid L) :
    perpendicularBisectorCondition P₁ P₂ L → Axiom2 P₁ P₂ L := by
  intro h
  rcases h with ⟨hm, hp⟩
  rw [Axiom2, folds_onto]
  simp [midpoint, is_contained] at hm hp
  have hm2 : L 0 * (P₁ 0 + P₂ 0) + L 1 * (P₁ 1 + P₂ 1) = 2 * L 2 := by
    nlinarith [hm]
  simp [reflect]
  ext i
  fin_cases i
  · simp
    have hd : L 0 ^ 2 + L 1 ^ 2 ≠ 0 := hL
    field_simp [hd]
    ring_nf
    linear_combination -L 0 * hm2 + L 1 * hp
  · simp
    have hd : L 0 ^ 2 + L 1 ^ 2 ≠ 0 := hL
    field_simp [hd]
    ring_nf
    linear_combination -L 1 * hm2 - L 0 * hp

theorem axiom2_perpendicularBisector_iff (P₁ P₂ : Point) (L : Line) (hL : valid L) :
    Axiom2 P₁ P₂ L ↔ perpendicularBisectorCondition P₁ P₂ L := by
  constructor
  · exact axiom2_perpendicularBisector_forward P₁ P₂ L hL
  · exact axiom2_perpendicularBisector_reverse P₁ P₂ L hL

set_option linter.flexible false in
theorem axiom2_scaled_iff {P₁ P₂ : Point} {L : Line}
    (hL : valid L) (hsep : P₁ 0 ≠ P₂ 0 ∨ P₁ 1 ≠ P₂ 1) :
    Axiom2 P₁ P₂ L ↔ ∃ a : ℝ, a ≠ 0 ∧ L = scaled a (perpendicularBisector P₁ P₂) := by
  rw [axiom2_perpendicularBisector_iff P₁ P₂ L hL]
  constructor
  · intro h
    rcases h with ⟨hm, hp⟩
    simp [midpoint, is_contained] at hm hp
    rcases hsep with hx | hy
    · use L 0 / (P₂ 0 - P₁ 0)
      constructor
      · intro ha
        apply hL
        have h0 : L 0 = 0 := by
          have := congrArg (fun t => t * (P₂ 0 - P₁ 0)) ha
          field_simp [sub_ne_zero.mpr (Ne.symm hx)] at this
          simpa using this
        have h1 : L 1 = 0 := by
          rw [h0] at hp
          have hdx : P₂ 0 - P₁ 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
          have hmul : L 1 * (P₂ 0 - P₁ 0) = 0 := by simpa using hp.symm
          exact (mul_eq_zero.mp hmul).resolve_right hdx
        simp [h0, h1]
      · ext i
        fin_cases i
        · simp [scaled, perpendicularBisector]
          field_simp [sub_ne_zero.mpr (Ne.symm hx)]
          try ring
        · simp [scaled, perpendicularBisector]
          field_simp [sub_ne_zero.mpr (Ne.symm hx)]
          nlinarith [hp]
        · simp [scaled, perpendicularBisector]
          field_simp [sub_ne_zero.mpr (Ne.symm hx)]
          ring_nf
          linear_combination -((P₁ 1 + P₂ 1) * hp + 2 * (P₂ 0 - P₁ 0) * hm)
    · use L 1 / (P₂ 1 - P₁ 1)
      constructor
      · intro ha
        apply hL
        have h1 : L 1 = 0 := by
          have := congrArg (fun t => t * (P₂ 1 - P₁ 1)) ha
          field_simp [sub_ne_zero.mpr (Ne.symm hy)] at this
          simpa using this
        have h0 : L 0 = 0 := by
          rw [h1] at hp
          have hdy : P₂ 1 - P₁ 1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
          have hmul : L 0 * (P₂ 1 - P₁ 1) = 0 := by simpa using hp
          exact (mul_eq_zero.mp hmul).resolve_right hdy
        simp [h0, h1]
      · ext i
        fin_cases i
        · simp [scaled, perpendicularBisector]
          field_simp [sub_ne_zero.mpr (Ne.symm hy)]
          nlinarith [hp]
        · simp [scaled, perpendicularBisector]
          field_simp [sub_ne_zero.mpr (Ne.symm hy)]
          try ring
        · simp [scaled, perpendicularBisector]
          field_simp [sub_ne_zero.mpr (Ne.symm hy)]
          ring_nf
          linear_combination -(-(P₁ 0 + P₂ 0) * hp + 2 * (P₂ 1 - P₁ 1) * hm)
  · intro h
    rcases h with ⟨a, _ha, rfl⟩
    constructor
    · simp [midpoint, is_contained, scaled, perpendicularBisector]
      ring
    · simp [scaled, perpendicularBisector]
      ring

end Axiom2Spec

/-! ## Axiom 3 -/

namespace Axiom3Spec

def directionQuadratic (L₁ L₂ F : Line) : Prop :=
  let S := L₁ 0 * L₂ 1 + L₂ 0 * L₁ 1
  let T := L₁ 1 * L₂ 1 - L₁ 0 * L₂ 0
  S * (F 1)^2 - 2 * T * (F 0) * (F 1) - S * (F 0)^2 = 0

def slopeQuadratic (L₁ L₂ : Line) (m : ℝ) : Prop :=
  let S := L₁ 0 * L₂ 1 + L₂ 0 * L₁ 1
  let T := L₁ 1 * L₂ 1 - L₁ 0 * L₂ 0
  S * m^2 - 2 * T * m - S = 0

theorem axiom3_directionQuadratic (L₁ L₂ F : Line) :
    Axiom3 L₁ L₂ F → directionQuadratic L₁ L₂ F := by
  intro h
  rw [← h]
  simp [reflect_line, directionQuadratic]
  ring

theorem axiom3_slopeQuadratic {L₁ L₂ F : Line} {m : ℝ}
    (h : Axiom3 L₁ L₂ F) (hB : F 1 ≠ 0) (hm : F 0 = -m * F 1) :
    slopeQuadratic L₁ L₂ m := by
  have hq := axiom3_directionQuadratic L₁ L₂ F h
  simp [directionQuadratic, slopeQuadratic, hm] at hq ⊢
  nlinarith [show (F 1)^2 > 0 from sq_pos_of_ne_zero hB]

end Axiom3Spec

/-! ## Axiom 4 -/

namespace Axiom4Spec

def perpendicularLine (L₁ : Line) (P : Point) : Line :=
  ![-L₁ 1, L₁ 0, -L₁ 1 * P 0 + L₁ 0 * P 1]

theorem axiom4_scaled_iff {L L₁ : Line} {P : Point} (hL : valid L) (hL₁ : valid L₁) :
    Axiom4 L₁ P L ↔ ∃ a : ℝ, a ≠ 0 ∧ L = scaled a (perpendicularLine L₁ P) := by
  constructor
  · intro h
    rcases h with ⟨h_cont, h_perp⟩
    simp only [is_contained, perpendicular] at h_cont h_perp
    let a := (L 1 * L₁ 0 - L 0 * L₁ 1) / (L₁ 0 ^ 2 + L₁ 1 ^ 2)
    use a
    have hd : L₁ 0 ^ 2 + L₁ 1 ^ 2 ≠ 0 := hL₁
    constructor
    · intro ha
      have h_num : L 1 * L₁ 0 - L 0 * L₁ 1 = 0 := by
        calc
          L 1 * L₁ 0 - L 0 * L₁ 1
              = (L 1 * L₁ 0 - L 0 * L₁ 1) / (L₁ 0 ^ 2 + L₁ 1 ^ 2) *
                  (L₁ 0 ^ 2 + L₁ 1 ^ 2) := by rw [div_mul_cancel₀ _ hd]
          _ = a * (L₁ 0 ^ 2 + L₁ 1 ^ 2) := rfl
          _ = 0 * (L₁ 0 ^ 2 + L₁ 1 ^ 2) := by rw [ha]
          _ = 0 := zero_mul _
      have h_id :
          (L 0 ^ 2 + L 1 ^ 2) * (L₁ 0 ^ 2 + L₁ 1 ^ 2) =
            (L 0 * L₁ 0 + L 1 * L₁ 1) ^ 2 +
              (L 1 * L₁ 0 - L 0 * L₁ 1) ^ 2 := by
        ring
      have h_dot : L 0 * L₁ 0 + L 1 * L₁ 1 = 0 := by
        calc
          L 0 * L₁ 0 + L 1 * L₁ 1
              = L 0 * L₁ 0 + L₁ 1 * L 1 := by ring
          _ = L 0 * L₁ 0 + -(L₁ 0 * L 0) := by rw [h_perp]
          _ = 0 := by ring
      rw [h_num, h_dot] at h_id
      simp only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, add_zero] at h_id
      cases mul_eq_zero.mp h_id with
      | inl hl => exact hL hl
      | inr hr => exact hL₁ hr
    · have h_sub : L 0 * L₁ 0 = -(L 1 * L₁ 1) := by
        calc
          L 0 * L₁ 0
              = L₁ 0 * L 0 := by ring
          _ = - -(L₁ 0 * L 0) := by ring
          _ = -(L₁ 1 * L 1) := by rw [← h_perp]
          _ = -(L 1 * L₁ 1) := by ring
      have h0 : L 0 = a * (-L₁ 1) := by
        have step :
            L 0 * (L₁ 0 ^ 2 + L₁ 1 ^ 2) =
              (L 1 * L₁ 0 - L 0 * L₁ 1) * (-L₁ 1) := by
          calc
            L 0 * (L₁ 0 ^ 2 + L₁ 1 ^ 2)
                = (L 0 * L₁ 0) * L₁ 0 + L 0 * L₁ 1 ^ 2 := by ring
            _ = (-(L 1 * L₁ 1)) * L₁ 0 + L 0 * L₁ 1 ^ 2 := by rw [h_sub]
            _ = (L 1 * L₁ 0 - L 0 * L₁ 1) * (-L₁ 1) := by ring
        calc
          L 0
              = L 0 * (L₁ 0 ^ 2 + L₁ 1 ^ 2) / (L₁ 0 ^ 2 + L₁ 1 ^ 2) := by
                rw [mul_div_cancel_right₀ _ hd]
          _ = (L 1 * L₁ 0 - L 0 * L₁ 1) * (-L₁ 1) /
                (L₁ 0 ^ 2 + L₁ 1 ^ 2) := by rw [step]
          _ = (L 1 * L₁ 0 - L 0 * L₁ 1) / (L₁ 0 ^ 2 + L₁ 1 ^ 2) *
                (-L₁ 1) := by ring
          _ = a * (-L₁ 1) := rfl
      have h_sub2 : L 1 * L₁ 1 = -(L 0 * L₁ 0) := by
        calc
          L 1 * L₁ 1
              = L₁ 1 * L 1 := by ring
          _ = -(L₁ 0 * L 0) := h_perp
          _ = -(L 0 * L₁ 0) := by ring
      have h1 : L 1 = a * L₁ 0 := by
        have step :
            L 1 * (L₁ 0 ^ 2 + L₁ 1 ^ 2) =
              (L 1 * L₁ 0 - L 0 * L₁ 1) * L₁ 0 := by
          calc
            L 1 * (L₁ 0 ^ 2 + L₁ 1 ^ 2)
                = L 1 * L₁ 0 ^ 2 + (L 1 * L₁ 1) * L₁ 1 := by ring
            _ = L 1 * L₁ 0 ^ 2 + (-(L 0 * L₁ 0)) * L₁ 1 := by rw [h_sub2]
            _ = (L 1 * L₁ 0 - L 0 * L₁ 1) * L₁ 0 := by ring
        calc
          L 1
              = L 1 * (L₁ 0 ^ 2 + L₁ 1 ^ 2) / (L₁ 0 ^ 2 + L₁ 1 ^ 2) := by
                rw [mul_div_cancel_right₀ _ hd]
          _ = (L 1 * L₁ 0 - L 0 * L₁ 1) * L₁ 0 /
                (L₁ 0 ^ 2 + L₁ 1 ^ 2) := by rw [step]
          _ = (L 1 * L₁ 0 - L 0 * L₁ 1) / (L₁ 0 ^ 2 + L₁ 1 ^ 2) *
                L₁ 0 := by ring
          _ = a * L₁ 0 := rfl
      have h2 : L 2 = a * (-L₁ 1 * P 0 + L₁ 0 * P 1) := by
        calc
          L 2
              = L 0 * P 0 + L 1 * P 1 := h_cont.symm
          _ = (a * (-L₁ 1)) * P 0 + (a * L₁ 0) * P 1 := by rw [h0, h1]
          _ = a * (-L₁ 1 * P 0 + L₁ 0 * P 1) := by ring
      funext i
      fin_cases i
      · change L 0 = scaled a (perpendicularLine L₁ P) 0
        exact h0
      · change L 1 = scaled a (perpendicularLine L₁ P) 1
        exact h1
      · change L 2 = scaled a (perpendicularLine L₁ P) 2
        exact h2
  · intro h
    rcases h with ⟨a, _ha, hL_eq⟩
    constructor
    · simp only [is_contained]
      rw [hL_eq]
      simp [scaled, perpendicularLine]
      ring
    · simp only [perpendicular]
      rw [hL_eq]
      simp [scaled, perpendicularLine]
      ring

end Axiom4Spec

/-! ## Axiom 5 -/

namespace Axiom5Spec

def axiom5Algebraic (P₁ P₂ : Point) (L₁ F : Line) : Prop :=
  is_contained F P₂ ∧ places_onto_eq F L₁ P₁

def slopeQuadratic (P₁ P₂ : Point) (L₁ : Line) (m : ℝ) : Prop :=
  let a := L₁ 0; let b := L₁ 1; let c := L₁ 2
  let x := P₁ 0; let y := P₁ 1
  let u := P₂ 0; let v := P₂ 1
  let e := -m * x + y - (v - u * m)
  a * (x * (m^2 + 1) + 2 * m * e) +
    b * (y * (m^2 + 1) - 2 * e) =
    c * (m^2 + 1)

theorem axiom5_algebraic (P₁ P₂ : Point) (L₁ F : Line) (hF : valid F) :
    Axiom5 P₁ P₂ L₁ F → axiom5Algebraic P₁ P₂ L₁ F := by
  intro h
  exact ⟨h.1, (tangent_characterization F L₁ P₁ hF).1 h.2⟩

theorem axiom5_of_algebraic {P₁ P₂ : Point} {L₁ F : Line}
    (hF : valid F) (h : axiom5Algebraic P₁ P₂ L₁ F) :
    Axiom5 P₁ P₂ L₁ F := by
  rw [axiom5Algebraic] at h
  rw [Axiom5]
  exact ⟨h.1, (tangent_characterization F L₁ P₁ hF).2 h.2⟩

theorem axiom5_algebraic_iff {P₁ P₂ : Point} {L₁ F : Line} (hF : valid F) :
    Axiom5 P₁ P₂ L₁ F ↔ axiom5Algebraic P₁ P₂ L₁ F := by
  constructor
  · exact axiom5_algebraic P₁ P₂ L₁ F hF
  · exact axiom5_of_algebraic hF

theorem axiom5_slopeQuadratic {P₁ P₂ : Point} {L₁ : Line} {m : ℝ}
    (h : Axiom5 P₁ P₂ L₁ (point_slope_form (some m) P₂)) :
    slopeQuadratic P₁ P₂ L₁ m := by
  have hF := valid_point_slope_form (some m) P₂
  have hAlg := (axiom5_algebraic P₁ P₂ L₁ (point_slope_form (some m) P₂) hF) h
  simpa [slopeQuadratic, axiom5Algebraic, places_onto_eq, point_slope_form] using hAlg.2

theorem axiom5_of_slopeQuadratic {P₁ P₂ : Point} {L₁ : Line} {m : ℝ}
    (h : slopeQuadratic P₁ P₂ L₁ m) :
    Axiom5 P₁ P₂ L₁ (point_slope_form (some m) P₂) := by
  apply axiom5_of_algebraic (valid_point_slope_form (some m) P₂)
  refine ⟨?_, ?_⟩
  · exact point_slope_form_contains (some m) P₂
  · simpa [slopeQuadratic, axiom5Algebraic, places_onto_eq, point_slope_form] using h

theorem axiom5_slopeQuadratic_iff {P₁ P₂ : Point} {L₁ : Line} {m : ℝ} :
    Axiom5 P₁ P₂ L₁ (point_slope_form (some m) P₂) ↔
      slopeQuadratic P₁ P₂ L₁ m := by
  constructor
  · exact axiom5_slopeQuadratic
  · exact axiom5_of_slopeQuadratic

end Axiom5Spec

/-! ## Axiom 6 -/

namespace Axiom6Spec

def slopeInterceptForm (m k : ℝ) : Line :=
  ![-m, 1, k]

def simultaneousTangency (P₁ P₂ : Point) (L₁ L₂ : Line) (F : Line) : Prop :=
  is_tangent_to_parabola F P₁ L₁ ∧ is_tangent_to_parabola F P₂ L₂

def algebraicSystem (P₁ P₂ : Point) (L₁ L₂ : Line) (F : Line) : Prop :=
  places_onto_eq F L₁ P₁ ∧ places_onto_eq F L₂ P₂

def cubicSlopeRelation (P₁ P₂ : Point) (L₁ L₂ : Line) (m : ℝ) : Prop :=
  let q₁ := L₁ 0 * P₁ 0 + L₁ 1 * P₁ 1 - L₁ 2
  let q₂ := L₂ 0 * P₂ 0 + L₂ 1 * P₂ 1 - L₂ 2
  let d₁ := L₁ 1 - L₁ 0 * m
  let d₂ := L₂ 1 - L₂ 0 * m
  let deltaY := P₁ 1 - P₂ 1
  let deltaX := P₁ 0 - P₂ 0
  (m^2 + 1) * (d₂ * q₁ - d₁ * q₂) -
    2 * d₁ * d₂ * (deltaY - m * deltaX) = 0

theorem axiom6_is_simultaneous_tangent (P₁ P₂ : Point) (L₁ L₂ F : Line) :
    Axiom6 P₁ P₂ L₁ L₂ F ↔ simultaneousTangency P₁ P₂ L₁ L₂ F := by
  simp [Axiom6, simultaneousTangency, is_tangent_to_parabola]

theorem axiom6_characterization (P₁ P₂ : Point) (L₁ L₂ F : Line) (hF : valid F) :
    Axiom6 P₁ P₂ L₁ L₂ F ↔ algebraicSystem P₁ P₂ L₁ L₂ F := by
  rw [axiom6_is_simultaneous_tangent]
  constructor
  · intro h
    exact ⟨(tangent_characterization F L₁ P₁ hF).1 h.1,
      (tangent_characterization F L₂ P₂ hF).1 h.2⟩
  · intro h
    exact ⟨(tangent_characterization F L₁ P₁ hF).2 h.1,
      (tangent_characterization F L₂ P₂ hF).2 h.2⟩

theorem axiom6_cubicSlope {P₁ P₂ : Point} {L₁ L₂ : Line} {m k : ℝ}
    (h : Axiom6 P₁ P₂ L₁ L₂ (slopeInterceptForm m k)) :
    cubicSlopeRelation P₁ P₂ L₁ L₂ m := by
  have hF : valid (slopeInterceptForm m k) := by
    simp [valid, slopeInterceptForm]
    nlinarith [sq_nonneg m]
  have hAlg := (axiom6_characterization P₁ P₂ L₁ L₂ (slopeInterceptForm m k) hF).1 h
  rcases hAlg with ⟨h1, h2⟩
  simp [places_onto_eq, slopeInterceptForm] at h1 h2 ⊢
  dsimp [cubicSlopeRelation]
  linear_combination
    (L₂ 1 - L₂ 0 * m) * h1 - (L₁ 1 - L₁ 0 * m) * h2

end Axiom6Spec

/-! ## Axiom 7 -/

namespace Axiom7Spec

def axiom7Algebraic (L₁ : Line) (P : Point) (F : Line) : Prop :=
  places_onto_eq F L₁ P ∧ perpendicular L₁ F

def slopePerpendicular (L₁ : Line) (m : ℝ) : Prop :=
  L₁ 1 = L₁ 0 * m

def slopeInterceptAlgebraic (L₁ : Line) (P : Point) (m k : ℝ) : Prop :=
  places_onto_eq (Axiom6Spec.slopeInterceptForm m k) L₁ P ∧ slopePerpendicular L₁ m

theorem perpendicular_slopeIntercept (L₁ : Line) (m k : ℝ) :
    perpendicular L₁ (Axiom6Spec.slopeInterceptForm m k) ↔ slopePerpendicular L₁ m := by
  simp [perpendicular, slopePerpendicular, Axiom6Spec.slopeInterceptForm]

theorem axiom7_algebraic (L₁ : Line) (P : Point) (F : Line) (hF : valid F) :
    Axiom7 L₁ P F → axiom7Algebraic L₁ P F := by
  intro h
  exact ⟨(tangent_characterization F L₁ P hF).1 h.1, h.2⟩

theorem axiom7_of_algebraic {L₁ : Line} {P : Point} {F : Line}
    (hF : valid F) (h : axiom7Algebraic L₁ P F) :
    Axiom7 L₁ P F := by
  rw [axiom7Algebraic] at h
  rw [Axiom7]
  exact ⟨(tangent_characterization F L₁ P hF).2 h.1, h.2⟩

theorem axiom7_algebraic_iff {L₁ : Line} {P : Point} {F : Line} (hF : valid F) :
    Axiom7 L₁ P F ↔ axiom7Algebraic L₁ P F := by
  constructor
  · exact axiom7_algebraic L₁ P F hF
  · exact axiom7_of_algebraic hF

theorem axiom7_slopeIntercept_iff {L₁ : Line} {P : Point} {m k : ℝ} :
    Axiom7 L₁ P (Axiom6Spec.slopeInterceptForm m k) ↔
      slopeInterceptAlgebraic L₁ P m k := by
  have hF : valid (Axiom6Spec.slopeInterceptForm m k) := by
    simp [valid, Axiom6Spec.slopeInterceptForm]
    nlinarith [sq_nonneg m]
  constructor
  · intro h
    exact ⟨(axiom7_algebraic L₁ P (Axiom6Spec.slopeInterceptForm m k) hF h).1,
      (perpendicular_slopeIntercept L₁ m k).1 h.2⟩
  · intro h
    apply axiom7_of_algebraic hF
    exact ⟨h.1, (perpendicular_slopeIntercept L₁ m k).2 h.2⟩

end Axiom7Spec
