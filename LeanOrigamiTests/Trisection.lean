import LeanOrigami.Construction.TrisectionCondition

/-!
# Both interior trisectors, away from a preferred coordinate frame

These examples check the full geometric specification, including strict
interior placement and all three equal angles, rather than just the cubic.
-/

namespace LeanOrigamiTests.Trisection
open LeanOrigami

/-- A translated, rotated input with unequal ray lengths. -/
example : Trisection.IsTrisection (2, -3) (2, -1) (6/25, -192/25)
    (6/5, -12/5) (26/25, -82/25) := by
  let roots : Trisection.Roots ℝ := ⟨2, 5, 44/125, 3/5, 4/5⟩
  have h : roots.Valid (2, -3) (2, -1) (6/25, -192/25) := by
    norm_num [Trisection.Roots.Valid, Trisection.Roots.cosine,
      Trisection.unitVector, Point.dot, Point.sqNorm, roots]
  have he := roots.isTrisection (2, -3) (2, -1) (6/25, -192/25) h
  norm_num [Trisection.Roots.firstPoint, Trisection.Roots.secondPoint,
    Trisection.Roots.perpendicularUnit, Trisection.Roots.cosine,
    Trisection.unitVector, Point.dot, roots] at he
  simpa only [neg_div] using he

/-- Clockwise input puts both outputs on the clockwise side. -/
example : Trisection.IsTrisection (0, 0) (1, 0) (-117/125, -44/125)
    (3/5, -4/5) (-7/25, -24/25) := by
  let roots : Trisection.Roots ℝ := ⟨1, 1, 44/125, 3/5, 4/5⟩
  have h : roots.Valid (0, 0) (1, 0) (-117/125, -44/125) := by
    norm_num [Trisection.Roots.Valid, Trisection.Roots.cosine,
      Trisection.unitVector, Point.dot, Point.sqNorm, roots]
  have he := roots.isTrisection (0, 0) (1, 0) (-117/125, -44/125) h
  norm_num [Trisection.Roots.firstPoint, Trisection.Roots.secondPoint,
    Trisection.Roots.perpendicularUnit, Trisection.Roots.cosine,
    Trisection.unitVector, Point.dot, roots] at he
  simpa only [neg_div] using he

/-- The initial domain excludes straight angles and zero rays. -/
example : ¬ Trisection.Domain ((0 : ℚ), 0) (1, 0) (-1, 0) ∧
    ¬ Trisection.Domain ((0 : ℚ), 0) (0, 0) (1, 1) := by
  norm_num [Trisection.Domain, Point.det]

private def certificateObjects (firstOutput secondOutput : Point ℚ) : List (Object ℚ) :=
  [.point (0, 0), .point (1, 0), .point (-117/125, 44/125),
    .point firstOutput, .point secondOutput, .point (1, 0), .point (1, 0),
    .point (44/125, 0), .point (3/5, 0), .point (4/5, 0), .point (-117/125, 0)]

private def certificate : Condition :=
  TrisectionCondition.condition 0 1 2 3 4 ⟨5, 6, 7, 8, 9⟩ 10

/-- The exact endpoint condition accepts the intended order. -/
example : certificate.checkObjects (certificateObjects (3/5, 4/5) (-7/25, 24/25)) = true := by
  decide +kernel

/-- Correct cubic witnesses alone do not excuse swapped output rays. -/
example : certificate.checkObjects (certificateObjects (-7/25, 24/25) (3/5, 4/5)) = false := by
  decide +kernel

#print axioms TrisectionCondition.sound

#print axioms Trisection.Roots.isTrisection
#print axioms Trisection.Roots.map_valid

end LeanOrigamiTests.Trisection
