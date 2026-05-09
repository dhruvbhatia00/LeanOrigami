import LeanOrigami.Basic

def Axiom1 (P₁ : Point) (P₂ : Point) (L : Line) : Prop :=
  is_contained L P₁ ∧ is_contained L P₂

def Axiom3 (L₁ : Line) (L₂ : Line) (L : Line) : Prop :=
  reflect_line L₁ L =  L₂

def Axiom5 (P₁ : Point) (P₂ : Point) (L₁ : Line) (L : Line) : Prop :=
  is_contained L P₂ ∧ is_contained L₁ (reflect L P₁)
