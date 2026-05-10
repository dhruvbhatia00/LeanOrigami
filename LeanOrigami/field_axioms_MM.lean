import LeanOrigami.Basic
import LeanOrigami.constructible
import LeanOrigami.Axioms

lemma x_axis_cons : cons_line ![0, 1, 0] := by
  have cons_point ![0 , 0] := by
    cons_point_origin


lemma negative_cons (P : Point) : is_constructible_proj P
 → is_constructible ![-(P 0), -(P 1)] := by
 sorry
