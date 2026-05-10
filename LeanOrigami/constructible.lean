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
      Axiom1 P₁ P₂ L → cons_line L
  | axiom2 {P₁ P₂ : Point} (hP₁ : cons_point P₁) (hP₂ : cons_point P₂) {L : Line} :
      Axiom2 P₁ P₂ L → cons_line L
  | axiom3 {L₁ L₂ : Line} (hL₁ : cons_line L₁) (hL₂ : cons_line L₂) {L : Line} :
      Axiom3 L₁ L₂ L → cons_line L
  | axiom4 {L₁ : Line} {P₁ : Point}
      (hL₁ : cons_line L₁) (hP₁ : cons_point P₁) {L : Line} :
      Axiom4 L₁ P₁ L → cons_line L
  | axiom5 {P₁ P₂ : Point} {L₁ : Line}
      (hP₁ : cons_point P₁) (hP₂ : cons_point P₂) (hL₁ : cons_line L₁) {L : Line} :
      Axiom5 P₁ P₂ L₁ L → cons_line L
  | axiom6 {P₁ P₂ : Point} {L₁ L₂ : Line}
      (hP₁ : cons_point P₁) (hP₂ : cons_point P₂)
      (hL₁ : cons_line L₁) (hL₂ : cons_line L₂) {L : Line} :
      Axiom6 P₁ P₂ L₁ L₂ L → cons_line L
  | axiom7 {L₁ : Line} {P : Point}
      (hL₁ : cons_line L₁) (hP : cons_point P) (L : Line) :
      Axiom7 L₁ P L → cons_line L

end

/-! ## Constructible real numbers -/

def constructible_real_proj (x : ℝ) : Prop :=
  ∃ P : Point, cons_point P ∧ (P 0 = x ∨ P 1 = x)

def constructible_real_dist (x : ℝ) : Prop :=
  ∃ P : Point, cons_point P ∧ ((P 0) ^ 2 + (P 1) ^ 2 = x ^ 2)

lemma constructible_real_defs_equiv (x : ℝ) : constructible_real_proj x ↔
constructible_real_dist x  := by
  sorry

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
