import LeanOrigami.Basic

def L : Line := ![1.0, 2.0, 3.0]

def P : Point := ![1.0, 2.0]

lemma one_contained_x_axis : is_contained ![0, 1, 0] ![1, 0] := by
  simp [is_contained]
