import LeanOrigami.constructible

/-!
# Tactic-facing constructibility lemmas

This file contains small wrapper lemmas around the core constructibility
definitions.  The tactic should use these canonical constructions instead of
rebuilding axiom proofs directly.
-/

set_option linter.flexible false in
lemma valid_lineThrough {P Q : Point}
    (hsep : P 0 ≠ Q 0 ∨ P 1 ≠ Q 1) :
    valid (Axiom1Spec.lineThrough P Q) := by
  simp [valid, Axiom1Spec.lineThrough]
  intro h
  rcases hsep with hx | hy
  · apply hx
    nlinarith [h]
  · apply hy
    nlinarith [h]

set_option linter.flexible false in
lemma valid_perpendicularBisector {P Q : Point}
    (hsep : P 0 ≠ Q 0 ∨ P 1 ≠ Q 1) :
    valid (Axiom2Spec.perpendicularBisector P Q) := by
  simp [valid, Axiom2Spec.perpendicularBisector]
  intro h
  rcases hsep with hx | hy
  · apply hx
    nlinarith [h]
  · apply hy
    nlinarith [h]

theorem cons_line_axiom1_lineThrough {P Q : Point}
    (hP : cons_point P) (hQ : cons_point Q)
    (hsep : P 0 ≠ Q 0 ∨ P 1 ≠ Q 1) :
    cons_line (Axiom1Spec.lineThrough P Q) := by
  apply cons_line.axiom1 hP hQ
  · exact valid_lineThrough hsep
  · exact (Axiom1Spec.axiom1_scaled_iff (L := Axiom1Spec.lineThrough P Q) hsep).2
      ⟨1, by ext i; fin_cases i <;> simp [scaled]⟩

theorem cons_line_axiom2_perpendicularBisector {P Q : Point}
    (hP : cons_point P) (hQ : cons_point Q)
    (hsep : P 0 ≠ Q 0 ∨ P 1 ≠ Q 1) :
    cons_line (Axiom2Spec.perpendicularBisector P Q) := by
  apply cons_line.axiom2 hP hQ
  · exact valid_perpendicularBisector hsep
  · exact (Axiom2Spec.axiom2_scaled_iff
      (L := Axiom2Spec.perpendicularBisector P Q)
      (valid_perpendicularBisector hsep) hsep).2
      ⟨1, by norm_num, by ext i; fin_cases i <;> simp [scaled]⟩

set_option linter.flexible false in
lemma valid_perpendicularLine {L : Line} {P : Point} (hL : valid L) :
    valid (Axiom4Spec.perpendicularLine L P) := by
  simp [valid, Axiom4Spec.perpendicularLine]
  intro h
  apply hL
  nlinarith

theorem cons_line_axiom4_perpendicularLine {L : Line} {P : Point}
    (hL : cons_line L) (hP : cons_point P) (hvalid : valid L) :
    cons_line (Axiom4Spec.perpendicularLine L P) := by
  apply cons_line.axiom4 hL hP
  · exact valid_perpendicularLine hvalid
  · exact (Axiom4Spec.axiom4_scaled_iff
      (L := Axiom4Spec.perpendicularLine L P)
      (valid_perpendicularLine hvalid) hvalid).2
      ⟨1, by norm_num, by ext i; fin_cases i <;> simp [scaled]⟩

noncomputable def intersectionPoint (L M : Line) : Point :=
  ![(M 1 * L 2 - L 1 * M 2) / (L 0 * M 1 - M 0 * L 1),
    (L 0 * M 2 - M 0 * L 2) / (L 0 * M 1 - M 0 * L 1)]

lemma intersects_at_intersectionPoint {L M : Line}
    (hdet : L 0 * M 1 - M 0 * L 1 ≠ 0) :
    intersects_at L M (intersectionPoint L M) := by
  have hdet' : L 0 * M 1 - L 1 * M 0 ≠ 0 := by
    convert hdet using 1
    ring
  have hdet'' : M 1 * L 0 - M 0 * L 1 ≠ 0 := by
    convert hdet using 1
    ring
  constructor
  · simp [is_contained, intersectionPoint]
    field_simp [hdet']
    ring
  · simp [is_contained, intersectionPoint]
    field_simp [hdet, hdet', hdet'']
    ring

theorem cons_point_intersectionPoint {L M : Line}
    (hL : cons_line L) (hM : cons_line M)
    (hdet : L 0 * M 1 - M 0 * L 1 ≠ 0) :
    cons_point (intersectionPoint L M) :=
  cons_point.hIntersect hL hM _ (intersects_at_intersectionPoint hdet)

lemma det_ne_zero_of_is_transverse {L M : Line} (h : is_transverse L M) :
    L 0 * M 1 - M 0 * L 1 ≠ 0 := by
  intro hdet
  apply h
  simp [is_parallel]
  nlinarith

theorem cons_point_intersectionPoint_of_transverse {L M : Line}
    (hL : cons_line L) (hM : cons_line M)
    (htrans : is_transverse L M) :
    cons_point (intersectionPoint L M) :=
  cons_point_intersectionPoint hL hM (det_ne_zero_of_is_transverse htrans)

/-! ## Polynomial tools for fold side conditions -/

def quadraticEval (A B C x : ℝ) : ℝ :=
  A * x ^ 2 + B * x + C

def quadraticDiscriminant (A B C : ℝ) : ℝ :=
  B ^ 2 - 4 * A * C

noncomputable def quadraticRoot (A B C : ℝ) (sign : Bool) : ℝ :=
  if sign then
    (-B + Real.sqrt (quadraticDiscriminant A B C)) / (2 * A)
  else
    (-B - Real.sqrt (quadraticDiscriminant A B C)) / (2 * A)

lemma quadraticRoot_is_root {A B C : ℝ} (hA : A ≠ 0)
    (hdisc : 0 ≤ quadraticDiscriminant A B C) (sign : Bool) :
    quadraticEval A B C (quadraticRoot A B C sign) = 0 := by
  have hdisc' : 0 ≤ B ^ 2 - A * C * 4 := by
    rw [quadraticDiscriminant] at hdisc
    nlinarith
  have hsqrt :
      (Real.sqrt (B ^ 2 - A * C * 4)) ^ 2 = B ^ 2 - A * C * 4 :=
    Real.sq_sqrt hdisc'
  unfold quadraticEval quadraticRoot quadraticDiscriminant
  by_cases hs : sign
  · simp [hs]
    field_simp [hA]
    ring_nf
    nlinarith [hsqrt]
  · simp [hs]
    field_simp [hA]
    ring_nf
    nlinarith [hsqrt]

theorem exists_quadratic_root_of_discriminant_nonneg {A B C : ℝ}
    (hA : A ≠ 0) (hdisc : 0 ≤ quadraticDiscriminant A B C) :
    ∃ x : ℝ, quadraticEval A B C x = 0 :=
  ⟨quadraticRoot A B C true, quadraticRoot_is_root hA hdisc true⟩

lemma linearRoot_is_root {B C : ℝ} (hB : B ≠ 0) :
    quadraticEval 0 B C (-C / B) = 0 := by
  simp [quadraticEval]
  field_simp [hB]
  ring

theorem exists_root_of_quadratic_or_linear {A B C : ℝ}
    (h :
      (A ≠ 0 ∧ 0 ≤ quadraticDiscriminant A B C) ∨
        (A = 0 ∧ B ≠ 0)) :
    ∃ x : ℝ, quadraticEval A B C x = 0 := by
  rcases h with ⟨hA, hdisc⟩ | ⟨rfl, hB⟩
  · exact exists_quadratic_root_of_discriminant_nonneg hA hdisc
  · exact ⟨-C / B, linearRoot_is_root hB⟩

namespace Axiom5Spec

def slopeQuadraticCoeffA (P₁ P₂ : Point) (L₁ : Line) : ℝ :=
  L₁ 0 * (2 * P₂ 0 - P₁ 0) + L₁ 1 * P₁ 1 - L₁ 2

def slopeQuadraticCoeffB (P₁ P₂ : Point) (L₁ : Line) : ℝ :=
  2 * L₁ 0 * (P₁ 1 - P₂ 1) - 2 * L₁ 1 * (P₂ 0 - P₁ 0)

def slopeQuadraticCoeffC (P₁ P₂ : Point) (L₁ : Line) : ℝ :=
  L₁ 0 * P₁ 0 + L₁ 1 * (2 * P₂ 1 - P₁ 1) - L₁ 2

def slopeQuadraticDiscriminant (P₁ P₂ : Point) (L₁ : Line) : ℝ :=
  quadraticDiscriminant
    (slopeQuadraticCoeffA P₁ P₂ L₁)
    (slopeQuadraticCoeffB P₁ P₂ L₁)
    (slopeQuadraticCoeffC P₁ P₂ L₁)

def slopeQuadraticCase (P₁ P₂ : Point) (L₁ : Line) : Prop :=
  slopeQuadraticCoeffA P₁ P₂ L₁ ≠ 0 ∧
    0 ≤ slopeQuadraticDiscriminant P₁ P₂ L₁

def slopeLinearCase (P₁ P₂ : Point) (L₁ : Line) : Prop :=
  slopeQuadraticCoeffA P₁ P₂ L₁ = 0 ∧
    slopeQuadraticCoeffB P₁ P₂ L₁ ≠ 0

set_option linter.flexible false in
lemma slopeQuadratic_iff_eval (P₁ P₂ : Point) (L₁ : Line) (m : ℝ) :
    slopeQuadratic P₁ P₂ L₁ m ↔
      quadraticEval
        (slopeQuadraticCoeffA P₁ P₂ L₁)
        (slopeQuadraticCoeffB P₁ P₂ L₁)
        (slopeQuadraticCoeffC P₁ P₂ L₁) m = 0 := by
  simp [slopeQuadratic, quadraticEval, slopeQuadraticCoeffA,
    slopeQuadraticCoeffB, slopeQuadraticCoeffC]
  constructor <;> intro h <;> nlinarith

theorem exists_slopeQuadratic_of_quadratic_or_linear {P₁ P₂ : Point} {L₁ : Line}
    (h :
      (slopeQuadraticCoeffA P₁ P₂ L₁ ≠ 0 ∧
          0 ≤ slopeQuadraticDiscriminant P₁ P₂ L₁) ∨
        (slopeQuadraticCoeffA P₁ P₂ L₁ = 0 ∧
          slopeQuadraticCoeffB P₁ P₂ L₁ ≠ 0)) :
    ∃ m : ℝ, slopeQuadratic P₁ P₂ L₁ m := by
  rcases h with hquad | hlin
  · rcases hquad with ⟨hA, hdisc⟩
    rcases exists_quadratic_root_of_discriminant_nonneg
        (A := slopeQuadraticCoeffA P₁ P₂ L₁)
        (B := slopeQuadraticCoeffB P₁ P₂ L₁)
        (C := slopeQuadraticCoeffC P₁ P₂ L₁)
        hA (by simpa [slopeQuadraticDiscriminant] using hdisc) with ⟨m, hm⟩
    exact ⟨m, (slopeQuadratic_iff_eval P₁ P₂ L₁ m).2 hm⟩
  · rcases hlin with ⟨hA, hB⟩
    rcases exists_root_of_quadratic_or_linear
        (A := slopeQuadraticCoeffA P₁ P₂ L₁)
        (B := slopeQuadraticCoeffB P₁ P₂ L₁)
        (C := slopeQuadraticCoeffC P₁ P₂ L₁)
        (Or.inr ⟨hA, hB⟩) with ⟨m, hm⟩
    exact ⟨m, (slopeQuadratic_iff_eval P₁ P₂ L₁ m).2 hm⟩

theorem exists_axiom5_point_slope_fold_of_quadratic_or_linear
    {P₁ P₂ : Point} {L₁ : Line}
    (h :
      (slopeQuadraticCoeffA P₁ P₂ L₁ ≠ 0 ∧
          0 ≤ slopeQuadraticDiscriminant P₁ P₂ L₁) ∨
        (slopeQuadraticCoeffA P₁ P₂ L₁ = 0 ∧
          slopeQuadraticCoeffB P₁ P₂ L₁ ≠ 0)) :
    ∃ m : ℝ, Axiom5 P₁ P₂ L₁ (point_slope_form (some m) P₂) := by
  rcases exists_slopeQuadratic_of_quadratic_or_linear h with ⟨m, hm⟩
  exact ⟨m, axiom5_of_slopeQuadratic hm⟩

theorem cons_line_axiom5_quadraticRoot {P₁ P₂ : Point} {L₁ : Line}
    (hP₁ : cons_point P₁) (hP₂ : cons_point P₂) (hL₁ : cons_line L₁)
    (hA : slopeQuadraticCoeffA P₁ P₂ L₁ ≠ 0)
    (hdisc : 0 ≤ slopeQuadraticDiscriminant P₁ P₂ L₁)
    (sign : Bool) :
    cons_line
      (point_slope_form
        (some
          (quadraticRoot
            (slopeQuadraticCoeffA P₁ P₂ L₁)
            (slopeQuadraticCoeffB P₁ P₂ L₁)
            (slopeQuadraticCoeffC P₁ P₂ L₁)
            sign))
        P₂) := by
  apply cons_line.axiom5 hP₁ hP₂ hL₁
  · exact valid_point_slope_form _ _
  · apply axiom5_of_slopeQuadratic
    apply (slopeQuadratic_iff_eval P₁ P₂ L₁ _).2
    apply quadraticRoot_is_root hA
    simpa [slopeQuadraticDiscriminant] using hdisc

theorem cons_line_axiom5_linearRoot {P₁ P₂ : Point} {L₁ : Line}
    (hP₁ : cons_point P₁) (hP₂ : cons_point P₂) (hL₁ : cons_line L₁)
    (hA : slopeQuadraticCoeffA P₁ P₂ L₁ = 0)
    (hB : slopeQuadraticCoeffB P₁ P₂ L₁ ≠ 0) :
    cons_line
      (point_slope_form
        (some
          (-slopeQuadraticCoeffC P₁ P₂ L₁ /
            slopeQuadraticCoeffB P₁ P₂ L₁))
        P₂) := by
  apply cons_line.axiom5 hP₁ hP₂ hL₁
  · exact valid_point_slope_form _ _
  · apply axiom5_of_slopeQuadratic
    apply (slopeQuadratic_iff_eval P₁ P₂ L₁ _).2
    rw [hA]
    exact linearRoot_is_root hB

theorem cons_line_axiom5_quadraticRoot_case {P₁ P₂ : Point} {L₁ : Line}
    (hP₁ : cons_point P₁) (hP₂ : cons_point P₂) (hL₁ : cons_line L₁)
    (hcase : slopeQuadraticCase P₁ P₂ L₁) (sign : Bool) :
    cons_line
      (point_slope_form
        (some
          (quadraticRoot
            (slopeQuadraticCoeffA P₁ P₂ L₁)
            (slopeQuadraticCoeffB P₁ P₂ L₁)
            (slopeQuadraticCoeffC P₁ P₂ L₁)
            sign))
        P₂) :=
  cons_line_axiom5_quadraticRoot hP₁ hP₂ hL₁ hcase.1 hcase.2 sign

theorem cons_line_axiom5_linearRoot_case {P₁ P₂ : Point} {L₁ : Line}
    (hP₁ : cons_point P₁) (hP₂ : cons_point P₂) (hL₁ : cons_line L₁)
    (hcase : slopeLinearCase P₁ P₂ L₁) :
    cons_line
      (point_slope_form
        (some
          (-slopeQuadraticCoeffC P₁ P₂ L₁ /
            slopeQuadraticCoeffB P₁ P₂ L₁))
        P₂) :=
  cons_line_axiom5_linearRoot hP₁ hP₂ hL₁ hcase.1 hcase.2

end Axiom5Spec
