import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

def Point : Type := Fin 2 → ℝ

def Line : Type := Fin 3 → ℝ

def valid (L : Line) : Prop := L 0 ≠ 0 ∨ L 1 ≠ 0

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

lemma reflect_fix_of_contains (hLP : is_contained L P) :
  reflect L P = P := by
    simp [reflect, is_contained] at *;



#min_imports
