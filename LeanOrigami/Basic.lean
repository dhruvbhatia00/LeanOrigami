import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.RCLike.Basic

/-!
# Basic analytic geometry for origami constructions

The paper is modeled as the real affine plane.  A point is represented by its
two coordinates, and a line is represented by coefficients `A B C` for the
equation

```text
A * x + B * y = C.
```

Line coefficients are homogeneous: scaling all three coefficients by a nonzero
scalar gives the same geometric line.  Most definitions below are deliberately
coordinate-explicit because later tactics/widgets will need predictable
algebraic normal forms.
-/

abbrev Point : Type := Fin 2 → ℝ

abbrev Line : Type := Fin 3 → ℝ

/-! ## Lines and incidence -/

def valid (L : Line) : Prop :=
  (L 0)^2 + (L 1)^2 ≠ 0

def is_contained (L : Line) (P : Point) : Prop :=
  L 0 * P 0 + L 1 * P 1 = L 2

def scaled (a : ℝ) (L : Line) : Line :=
  ![a * L 0, a * L 1, a * L 2]

lemma contains_iff_scaled_contains (L : Line) (P : Point) (a : ℝ) (ha : a ≠ 0) :
    is_contained L P ↔ is_contained (scaled a L) P := by
  constructor
  · intro h
    simp [is_contained, scaled]
    calc
      a * L 0 * P 0 + a * L 1 * P 1 = a * (L 0 * P 0 + L 1 * P 1) := by ring
      _ = a * L 2 := by rw [h]
  · intro h
    simp [is_contained, scaled] at h
    have hscaled : a * (L 0 * P 0 + L 1 * P 1) = a * L 2 := by
      calc
        a * (L 0 * P 0 + L 1 * P 1) = a * L 0 * P 0 + a * L 1 * P 1 := by ring
        _ = a * L 2 := h
    exact mul_left_cancel₀ ha hscaled

lemma valid_scaled (a : ℝ) (ha : a ≠ 0) (L : Line) :
    valid (scaled a L) ↔ valid L := by
  simp [valid, scaled]
  constructor
  · intro h hv
    apply h
    calc
      (a * L 0) ^ 2 + (a * L 1) ^ 2 = a ^ 2 * (L 0 ^ 2 + L 1 ^ 2) := by ring
      _ = 0 := by rw [hv, mul_zero]
  · intro h hv
    apply h
    have hv' : a ^ 2 * (L 0 ^ 2 + L 1 ^ 2) = 0 := by
      calc
        a ^ 2 * (L 0 ^ 2 + L 1 ^ 2)
            = (a * L 0) ^ 2 + (a * L 1) ^ 2 := by ring
        _ = 0 := hv
    exact (mul_eq_zero.mp hv').resolve_left (pow_ne_zero 2 ha)

/-! ## Standard line relations -/

def perpendicular (L₁ L₂ : Line) : Prop :=
  let a₁ := L₁ 0; let b₁ := L₁ 1
  let a₂ := L₂ 0; let b₂ := L₂ 1
  b₁ * b₂ = -(a₁ * a₂)

def is_horizontal (L : Line) : Prop :=
  L 0 = 0

def is_vertical (L : Line) : Prop :=
  L 1 = 0

def is_parallel (L₁ L₂ : Line) : Prop :=
  let a := L₁ 0; let b := L₁ 1
  let d := L₂ 0; let e := L₂ 1
  b * d = a * e

def is_transverse (L₁ L₂ : Line) : Prop :=
  ¬ is_parallel L₁ L₂

-- Backwards-compatible spelling for existing files.
abbrev is_tranverse : Line → Line → Prop :=
  is_transverse

lemma is_parallel_symm (L₁ L₂ : Line) :
    is_parallel L₁ L₂ ↔ is_parallel L₂ L₁ := by
  simp [is_parallel]
  constructor <;> intro h <;> nlinarith

/-! ## Point-slope lines -/

def point_slope_form (m : Option ℝ) (P : Point) : Line :=
  match m with
  | some a => ![-a, 1, (P 1) - (P 0) * a]
  | none => ![1, 0, P 0]

lemma point_slope_form_contains (m : Option ℝ) (P : Point) :
    is_contained (point_slope_form m P) P := by
  cases m with
  | none => simp [point_slope_form, is_contained]
  | some m =>
      simp [point_slope_form, is_contained]
      ring

lemma valid_point_slope_form (m : Option ℝ) (P : Point) :
    valid (point_slope_form m P) := by
  cases m with
  | none => simp [valid, point_slope_form]
  | some m =>
      simp [valid, point_slope_form]
      nlinarith [sq_nonneg m]

/-! ## Reflection -/

noncomputable def reflect (L : Line) (P : Point) : Point :=
  let a := L 0; let b := L 1; let c := L 2
  let x := P 0; let y := P 1
  ![x - (2 * a * (a * x + b * y - c)) / (a^2 + b^2),
    y - (2 * b * (a * x + b * y - c)) / (a^2 + b^2)]

lemma reflect_fix_of_contains (L : Line) (P : Point)
    (hLP : is_contained L P) (h : (L 0) ^ 2 + (L 1) ^ 2 ≠ 0) :
    reflect L P = P := by
  simp [reflect, is_contained] at *
  ext i
  fin_cases i <;> simp [h]
  · rw [hLP]
    simp
  · rw [hLP]
    simp

lemma reflect_fix_of_contains_valid (L : Line) (P : Point)
    (hLP : is_contained L P) (hL : valid L) :
    reflect L P = P :=
  reflect_fix_of_contains L P hLP hL

lemma reflect_reflect (L : Line) (P : Point) :
    reflect L (reflect L P) = P := by
  by_cases hd : L 0 ^ 2 + L 1 ^ 2 = 0
  · have h0 : L 0 = 0 := by nlinarith [sq_nonneg (L 0), sq_nonneg (L 1)]
    have h1 : L 1 = 0 := by nlinarith [sq_nonneg (L 0), sq_nonneg (L 1)]
    ext i
    fin_cases i <;> simp [reflect, h0, h1]
  · have hdsq : (L 0 ^ 2 + L 1 ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 hd
    simp [reflect]
    ext i
    fin_cases i <;> simp <;> field_simp [hd, hdsq, pow_two] <;> ring_nf

-- `reflect_line M L` is the image of line `L` after reflecting across mirror `M`.
def reflect_line (M L : Line) : Line :=
  let a₁ := M 0; let b₁ := M 1; let c₁ := M 2
  let a₂ := L 0; let b₂ := L 1; let c₂ := L 2
  ![(b₁^2 - a₁^2) * a₂ - 2 * a₁ * b₁ * b₂,
    (a₁^2 - b₁^2) * b₂ - 2 * a₁ * b₁ * a₂,
    -c₂ * (a₁^2 + b₁^2) + 2 * c₁ * (a₁ * a₂ + b₁ * b₂)]

/-! ## Intersections -/

def intersects_at (L₁ L₂ : Line) (P : Point) : Prop :=
  is_contained L₁ P ∧ is_contained L₂ P

lemma intersects_at_comm (L₁ L₂ : Line) (P : Point) :
    intersects_at L₁ L₂ P ↔ intersects_at L₂ L₁ P := by
  simp [intersects_at, and_comm]

lemma intersection_coords (L₁ L₂ : Line) (P : Point)
    (hdet : L₁ 0 * L₂ 1 - L₂ 0 * L₁ 1 ≠ 0) :
    let a₁ := L₁ 0; let b₁ := L₁ 1; let c₁ := L₁ 2
    let a₂ := L₂ 0; let b₂ := L₂ 1; let c₂ := L₂ 2
    intersects_at L₁ L₂ P →
      P =
        ![(b₂ * c₁ - b₁ * c₂) / (a₁ * b₂ - a₂ * b₁),
          (c₂ * a₁ - c₁ * a₂) / (a₁ * b₂ - b₁ * a₂)] := by
  dsimp only
  intro h
  rcases h with ⟨h1, h2⟩
  simp [is_contained] at h1 h2 ⊢
  ext i
  fin_cases i
  · simp
    have hx :
        (L₁ 0 * L₂ 1 - L₂ 0 * L₁ 1) * P 0 =
          L₂ 1 * L₁ 2 - L₁ 1 * L₂ 2 := by
      linear_combination L₂ 1 * h1 - L₁ 1 * h2
    rw [← hx]
    field_simp [hdet]
  · simp
    have hdet' : L₁ 0 * L₂ 1 - L₁ 1 * L₂ 0 ≠ 0 := by
      convert hdet using 1
      ring
    have hy :
        (L₁ 0 * L₂ 1 - L₁ 1 * L₂ 0) * P 1 =
          L₁ 0 * L₂ 2 - L₂ 0 * L₁ 2 := by
      linear_combination L₁ 0 * h2 - L₂ 0 * h1
    rw [show L₂ 2 * L₁ 0 - L₁ 2 * L₂ 0 =
        L₁ 0 * L₂ 2 - L₂ 0 * L₁ 2 by ring]
    rw [← hy]
    field_simp [hdet']

/-! ## Fold relations and Huzita-Hatori axioms -/

-- A line `L` folds point `P₁` onto point `P₂` when reflection across `L` maps
-- `P₁` to `P₂`.
def folds_onto (L : Line) (P₁ P₂ : Point) : Prop :=
  reflect L P₁ = P₂

lemma folds_onto_symm (L : Line) (P₁ P₂ : Point) :
    folds_onto L P₁ P₂ ↔ folds_onto L P₂ P₁ := by
  constructor
  · intro h
    rw [folds_onto] at h ⊢
    rw [← h]
    exact reflect_reflect L P₁
  · intro h
    rw [folds_onto] at h ⊢
    rw [← h]
    exact reflect_reflect L P₂
