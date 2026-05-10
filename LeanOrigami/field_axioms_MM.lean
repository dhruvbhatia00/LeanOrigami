import LeanOrigami.Basic
import LeanOrigami.constructible
import LeanOrigami.Axioms

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

lemma negative_cons (P : Point) : cons_point P
 → cons_point ![-(P 0), -(P 1)] := by
 sorry
