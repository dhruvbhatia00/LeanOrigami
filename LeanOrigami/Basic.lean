-- import Mathlib
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.RCLike.Basic

abbrev Point : Type := Fin 2 → ℝ

abbrev Line : Type := Fin 3 → ℝ

def valid (L : Line) : Prop := (L 0)^2 + (L 1)^2 ≠ 0

def is_contained (L : Line) (P : Point) : Prop :=
  (L 0) * (P 0) + (L 1) * (P 1) = L 2

def scaled (a : ℝ) (L : Line) := ![a * L 0, a * L 1, a * L 2]


variable (L L₁ L₂ : Line) (P P₁ P₂ : Point) (hL : valid L) (hL₁ : valid L₁) (hL₂ : valid L₂)

lemma contains_iff_scaled_contains (a : ℝ) (ha : a ≠ 0) :
  is_contained L P ↔ is_contained (scaled a L) P := by
  refine ⟨?_, ?_⟩;
  · simp [is_contained, scaled]; grind
  · simp [is_contained, scaled]; grind

noncomputable
def reflect : Point :=
  let a := L 0; let b := L 1; let c := L 2
  let x := P 0; let y := P 1
  ![x - (2 * a * (a * x + b * y - c))/(a^2 + b^2),
    y - (2 * b * (a * x + b * y - c))/(a^2 + b^2)]

lemma reflect_fix_of_contains (hLP : is_contained L P) (h : (L 0) ^ 2 + (L 1) ^ 2 ≠ 0) :
  reflect L P = P := by
    simp [reflect, is_contained] at *;
    ext i; by_cases hi : i = 0;
    · simp [hi, h]; right;
      rw [hLP]; simp
    · sorry;


def reflect_line : Line :=
  let a₁ := L₁ 0; let b₁ := L₁ 1; let c₁ := L₁ 2
  let a₂ := L₂ 0; let b₂ := L₂ 1; let c₂ := L₂ 2
  ![(b₁^2 - a₁^2) * a₂ - 2 * a₁ * b₁ * b₂,
  (a₁^2 - b₁^2) * b₂ - 2 * a₁ * b₁ * a₂,
  - c₂ * (a₁^2 + b₁^2) + 2 * c₁ * (a₁ * a₂ + b₁ * b₂)]


def intersects_at : Prop :=
  is_contained L₁ P ∧ is_contained L₂ P

lemma intersection_coords :
  let a₁ := L₁ 0; let b₁ := L₁ 1; let c₁ := L₁ 2
  let a₂ := L₂ 0; let b₂ := L₂ 1; let c₂ := L₂ 2
intersects_at L₁ L₂ P → P = ![(b₂*c₁ - b₁*c₂)/(a₁*b₂ - a₂*b₁), (c₂* a₁ - c₁ * a₂)/(a₁ * b₂ - b₁ * a₂)] :=
sorry

def perpendicular : Prop :=
  let a₁ := L₁ 0; let b₁ := L₁ 1;
  let a₂ := L₂ 0; let b₂ := L₂ 1;
  b₁ * b₂ = - (a₁ * a₂)

-- A line L folds point P₁ onto P₂ if P₂ is the reflection of P₁ across L. -/
def folds_onto (L : Line) (P₁ P₂ : Point) : Prop :=
  reflect L P₁ = P₂

lemma reflect_reflect (L : Line) (P : Point) : reflect L (reflect L P) = P := by
  by_cases hd : L 0 ^ 2 + L 1 ^ 2 = 0
  · have h0 : L 0 = 0 := by nlinarith [sq_nonneg (L 0), sq_nonneg (L 1)]
    have h1 : L 1 = 0 := by nlinarith [sq_nonneg (L 0), sq_nonneg (L 1)]
    ext i
    fin_cases i <;> simp [reflect, h0, h1]
  · have hdsq : (L 0 ^ 2 + L 1 ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 hd
    simp [reflect]
    ext i
    fin_cases i <;> simp <;> field_simp [hd, hdsq, pow_two] <;> ring_nf

lemma folds_onto_symm : folds_onto L P₁ P₂ ↔ folds_onto L P₂ P₁ := by
  constructor
  · intro h
    rw [folds_onto] at h ⊢
    rw [← h]
    exact reflect_reflect L P₁
  · intro h
    rw [folds_onto] at h ⊢
    rw [← h]
    exact reflect_reflect L P₂

-- Two points are "fold-related" if there exists a valid fold line that maps one onto the other. -/
-- def fold_related (P₁ P₂ : Point) : Prop :=
--   ∃ L : Line, valid L ∧ folds_onto L P₁ P₂


section Axioms
variable (L L₁ L₂ : Line) (P P₁ P₂ : Point) (hL : valid L) (hL₁ : valid L₁) (hL₂ : valid L₂)

def Axiom1 (P₁ : Point) (P₂ : Point) (L : Line) : Prop :=
  is_contained L P₁ ∧ is_contained L P₂

def Axiom2 : Prop :=
    folds_onto L P₁ P₂

def Axiom3 (L₁ : Line) (L₂ : Line) (L : Line) : Prop :=
  reflect_line L₁ L =  L₂

def Axiom4 : Prop :=
    is_contained L P ∧ perpendicular L₁ L

def Axiom5 (P₁ : Point) (P₂ : Point) (L₁ : Line) (L : Line) : Prop :=
  is_contained L P₂ ∧ is_contained L₁ (reflect L P₁)

def Axiom6 : Prop :=
    is_contained L₁ (reflect L P₁) ∧ is_contained L₂ (reflect L P₂)

def Axiom7 : Prop :=
    is_contained L₁ (reflect L P) ∧ perpendicular L₁ L





end Axioms


#min_imports
