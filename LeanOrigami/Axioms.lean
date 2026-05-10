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
