import LeanOrigami.Basic
import LeanOrigami.constructible
import LeanOrigami.Axioms
import LeanOrigami.ConstructibleLemmas

lemma x_axis_cons : cons_line ![0, 1, 0] := by
  have h0: cons_point ![0 , 0] := by
    exact cons_point_origin
  have h1: cons_point ![1 , 0] := by
    exact cons_point_one
  have h2: Axiom1 (![0 , 0]) (![1 , 0]) (![0, 1, 0]) := by
    simp [Axiom1, is_contained]
  have h3: valid (![0, 1, 0]) := by
    simp [valid]
  apply cons_line.axiom1 (h0) (h1) (h3) (h2)

lemma y_axis_cons : cons_line ![1, 0, 0] := by
  have h0: cons_point ![0 , 0] := by
    exact cons_point_origin
  have h1: cons_line ![0,1,0] := by
    exact x_axis_cons
  have h2: Axiom4 (![0,1,0]) (![0 , 0]) (![1, 0, 0]) := by
    simp [Axiom4, is_contained, perpendicular]
  have h3: valid (![1, 0, 0]) := by
    simp [valid]
  apply cons_line.axiom4 (h1) (h0) (h3) (h2)

lemma add_cons (a b : ℝ) : constructible_real_dist a ∧ constructible_real_dist b
→ constructible_real_dist (a + b) := by
  simp only [constructible_real_dist]
  rintro ⟨⟨P, hP⟩, ⟨Q, hQ⟩⟩
  sorry

lemma negative_cons (P : Point) : cons_point P
 → cons_point ![-(P 0), -(P 1)] := by
 sorry

lemma dist_of_cons_points_is_cons (P Q : Point) (x : ℝ) (h0 : cons_point P ∧ cons_point Q) (h1 : ((P 0) - (Q 0)) ^ 2 + ((P 1) - (Q 1)) ^ 2 = x^2) :
(constructible_real_dist x) := by
  let l := ![(P 1) - (Q 1), (Q 0) - (P 0), ((P 1) - (Q 1))*(P 0) + ((Q 0) - (P 0))*(P 1)]
  have h2 : Axiom1 (P) (Q) (l) := by
    simp [Axiom1, is_contained, l]
    ring
  let m := ![((Q 0) - (P 0)), (Q 1) - (P 1), ((Q 0) - (P 0)) * (P 0) + ((Q 1)-(P 1)) * (P 1)]
  have h3 : Axiom4 (l) (P) (m) := by
    simp [Axiom4, is_contained, l ,m, perpendicular]
    ring
  let n := ![(P 1) - (Q 1), (Q 0) - (P 0), 0]
  have h4 : Axiom4 (m) (![0, 0]) (n) := by
    simp [Axiom4, is_contained, m, n, perpendicular]
    ring
  let k := ![ -(P 1), (P 0), (-(P 1)*(Q 0) + (P 0) * (Q 1))]
  let R := intersectionPoint n k
  have h5 : ((P 1 - Q 1) * P 0 + P 1 * (Q 0 - P 0)) = -((P 0) * (Q 1) - (P 1) * (Q 0)) :=
    sorry
  have h6 : (P 0 - Q 0) ^ 2 + (P 1 - Q 1) ^ 2 =
    (-((Q 0 - P 0) * (-(P 1 * Q 0) + P 0 * Q 1)) / ((P 1 - Q 1) * P 0 + P 1 * (Q 0 - P 0))) ^ 2 +
    ((P 1 - Q 1) * (-(P 1 * Q 0) + P 0 * Q 1) / ((P 1 - Q 1) * P 0 + P 1 * (Q 0 - P 0))) ^ 2 := by
    sorry
  have h_length : x^2 = (R 0)^2 + (R 1)^2 := by
    rw[← h1]
    simp [R, intersectionPoint, k, n, h6]
  sorry
