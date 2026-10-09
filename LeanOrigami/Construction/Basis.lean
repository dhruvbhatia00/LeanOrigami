import LeanOrigami.Construction.Checker

/-!
# A reusable coordinate basis from the two seeds

Starting with only `(0,0)` and `(1,0)`, rule 5 supplies two diagonal creases.
Selecting the upper or lower branch constructs `(0,1)` or `(0,-1)`. All
coordinates are saved claims; program replay checks every one of them.
-/

namespace LeanOrigami.Basis

/-- The chosen side of the original axis. -/
def height (K : Type*) [Field K] (upper : Bool) : K := if upper then 1 else -1

/-- Object 8 is the off-axis point. The Boolean chooses exact coordinates,
not the position of a crease in an enumerated solver result. -/
def program (K : Type*) [Field K] (upper : Bool) : Program K :=
  let y := height K upper
  [.fold (.axiom1 ⟨0⟩ ⟨1⟩) ⟨0, 1, 0, Or.inr ⟨rfl, rfl⟩⟩,
   .fold (.axiom4 ⟨0⟩ ⟨2⟩) ⟨1, 0, 0, Or.inl rfl⟩,
   .fold (.axiom4 ⟨1⟩ ⟨2⟩) ⟨1, 0, 1, Or.inl rfl⟩,
   .fold (.axiom5 ⟨1⟩ ⟨0⟩ ⟨3⟩) ⟨1, -y, 0, Or.inl rfl⟩,
   .intersect ⟨4⟩ ⟨5⟩ (1, y),
   .fold (.axiom4 ⟨6⟩ ⟨3⟩) ⟨0, 1, y, Or.inr ⟨rfl, rfl⟩⟩,
   .intersect ⟨3⟩ ⟨7⟩ (0, y)]

/-- The complete constructed state makes the construction's references readable. -/
def objects (upper : Bool) : List (Object ℚ) :=
  let y := height ℚ upper
  [.point (0, 0), .point (1, 0),
   .line ⟨0, 1, 0, Or.inr ⟨rfl, rfl⟩⟩,
   .line ⟨1, 0, 0, Or.inl rfl⟩,
   .line ⟨1, 0, 1, Or.inl rfl⟩,
   .line ⟨1, -y, 0, Or.inl rfl⟩,
   .point (1, y), .line ⟨0, 1, y, Or.inr ⟨rfl, rfl⟩⟩,
   .point (0, y)]

/-- Both branch choices replay by kernel computation. -/
theorem replay (upper : Bool) : Program.run (program ℚ upper) = .ok (objects upper) := by
  cases upper <;> decide +kernel

/-- Both exact off-axis points have genuine construction histories. -/
theorem point_constructible (upper : Bool) :
    Constructible (.point (0, height ℝ upper)) := by
  have h := Program.run_sound (Rat.castHom ℝ) (program ℚ upper) (objects upper)
    (replay upper) (.point (0, height ℚ upper)) (by simp [objects])
  cases upper <;> simpa [Object.map, height] using h

/-- The constructed point is not on the original axis. -/
theorem off_axis (upper : Bool) : height ℝ upper ≠ 0 := by
  cases upper <;> norm_num [height]

end LeanOrigami.Basis
