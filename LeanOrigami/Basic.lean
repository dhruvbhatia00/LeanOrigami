import Mathlib

-- import Mathlib.AlgebraicTopology.SimplexCategory.Basic
--  import Mathlib.Analysis.RCLike.Basic

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

def intersects_at : Prop :=
  is_contained L₁ P ∧ is_contained L₂ P

lemma intersection_coords :
  let a₁ := L₁ 0; let b₁ := L₁ 1; let c₁ := L₁ 2
  let a₂ := L₂ 0; let b₂ := L₂ 1; let c₂ := L₂ 2
intersects_at L₁ L₂ P → P = ![(b₂*c₁ - b₁*c₂)/(a₁*b₂ - a₂*b₁), (c₂* a₁ - c₁ * a₂)/(a₁ * b₂ - b₁ * a₂)] :=
sorry



#min_imports
