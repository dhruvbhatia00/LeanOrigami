import LeanOrigami.Basic

def is_scaled (L₁ : Line) (L₂ : Line) : Prop :=
 (∃ a : ℝ, a ≠ 0 ∧ L₁ 0 = a * (L₂ 0) ∧ L₁ 1 = a * (L₂ 1) ∧ L₁ 2 = a * (L₂ 2))

-- lemma which says isscaled in symmetric

-- add a function which returns the fold L for algAxiom1

def line_through_points (P₁ P₂ : Point) : Line :=
  let a₁ := P₁ 0; let b₁ := P₁ 1;
  let a₂ := P₂ 0; let b₂ := P₂ 1;
  ![(a₂ - a₁), (b₁ - b₂), ((a₂ - a₁) * a₁ + (b₁ - b₂) * b₁)]

lemma AlgAxiom1 (P₁ : Point) (P₂ : Point) (L : Line) :
  let L₁ := line_through_points P₁ P₂;
  (Axiom1 P₁ P₂ L) ↔ (is_scaled L₁ L) := by
  refine⟨?_, ?_⟩;
  · simp[Axiom1, is_contained]
    sorry
  · sorry

def line_between_two_parallels_not_horizontal (L₁ L₂ : Line) : Line :=
  let A₁ := L₁ 0; let B₁ := L₁ 1; let C₁ := L₁ 2
  let A₂ := L₂ 0; let C₂ := L₂ 2
  ![2 * A₁ * A₂, 2 * A₂ * B₁, A₂ * C₁ + A₁ * C₂]

def line_between_two_parallels_horizontal (L₁ L₂ : Line) : Line :=
  let B₁ := L₁ 1; let C₁ := L₁ 2
  let C₂ := L₂ 2
  ![0, 2 * B₁, C₁ + C₂]



lemma AlgAxiom3_parallels_not_horizontal (L₁ : Line) (L₂ : Line) (L : Line) (hL : ¬ is_horizontal L₁) (h12 : is_parallel L₁ L₂) :
  let A₁ := L₁ 0; let B₁ := L₁ 1; let C₁ := L₁ 2;
  let A₂ := L₂ 0; let B₂ := L₂ 1; let C₂ := L₂ 2;
  let A := L 0; let B := L 1; let C := L 2;
  let L₃ := line_between_two_parallels_not_horizontal L₁ L₂;
  ()→
  (Axiom3 L₁ L₂ L) ↔ (is_scaled L₃ L) := by
  sorry

lemma AlgAxiom3_parallels_horizontal (L₁ : Line) (L₂ : Line) (L : Line) (hL : is_horizontal L₁) (h12 : is_parallel L₁ L₂) :
  let A₁ := L₁ 0; let B₁ := L₁ 1; let C₁ := L₁ 2;
  let A₂ := L₂ 0; let B₂ := L₂ 1; let C₂ := L₂ 2;
  let A := L 0; let B := L 1; let C := L 2;
  let L₃ := line_between_two_parallels_horizontal L₁ L₂;
  (Axiom3 L₁ L₂ L) ↔ (is_scaled L₃ L) := by
  sorry

/-
--this will be 4 functions later on

def angle_bisection (L₁ L₂ : Line) : Line :=
  let a₁ := L₁ 0; let b₁ := L₁ 1; let c₁ := L₁ 2
  let a₂ := L₂ 0; let b₂ := L₂ 1; let c₂ := L₂ 2
  ![]

-- lemma AlgAxiom3_one_intersection (L₁ : Line) (L₂ : Line) (L : Line)

lemma AlgAxiom5_not_horizontal (P₁ : Point) (P₂ : Point) (L₁ : Line) (L : Line) :
  let a₁ := P₁ 0; let b₁ := P₁ 1;
  let a₂ := P₂ 0; let b₂ := P₂ 1;
  let A₁ := L₁ 0; let B₁ := L₁ 1; let C₁ := L₁ 2;
  (Axiom5 P₁ P₂ L₁ L) ↔ () := by
  sorry
-/
