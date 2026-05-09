import LeanOrigami.Basic

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
