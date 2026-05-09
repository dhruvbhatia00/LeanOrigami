import Mathlib

def Point : Type := Fin 2 → ℝ

def Line : Type := Fin 3 → ℝ

def is_contained (L : Line) (P : Point) : Prop :=
  (L 0) * (P 0) + (L 1) * (P 1) = L 2

def scaled (a : ℝ) (L : Line) := ![a * L 0, a * L 1, a * L 2]

lemma contains_iff_scaled_contains (a : ℝ) (ha : a ≠ 0) (P : Point) (L : Line) :
  is_contained L P ↔ is_contained (scaled a L) P := by
  refine ⟨?_, ?_⟩;
  · simp [is_contained, scaled]; grind
  · sorry
