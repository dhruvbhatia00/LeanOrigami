import LeanOrigami.Construction.Checker

/-!
# A replayable subdivision construction

Objects 0 and 1 are the seeds. Each line below appends one exact object.
The same saved recipe works with rational or Hex real algebraic coordinates;
all values below are claimed outputs, checked against the requested operation.
-/

namespace LeanOrigamiDemos.Subdivision
open LeanOrigami

/-- The axes, perpendicular bisectors, and intersections constructing quarters.
Indices 2 and 3 are the axes; 5, 7, and 9 are the three subdivision points. -/
def program (K : Type*) [Field K] : Program K :=
  [.fold (.axiom1 ⟨0⟩ ⟨1⟩) ⟨0, 1, 0, Or.inr ⟨rfl, rfl⟩⟩,
   .fold (.axiom4 ⟨0⟩ ⟨2⟩) ⟨1, 0, 0, Or.inl rfl⟩,
   .fold (.axiom2 ⟨0⟩ ⟨1⟩) ⟨1, 0, 1/2, Or.inl rfl⟩,
   .intersect ⟨2⟩ ⟨4⟩ (1/2, 0),
   .fold (.axiom2 ⟨0⟩ ⟨5⟩) ⟨1, 0, 1/4, Or.inl rfl⟩,
   .intersect ⟨2⟩ ⟨6⟩ (1/4, 0),
   .fold (.axiom2 ⟨5⟩ ⟨1⟩) ⟨1, 0, 3/4, Or.inl rfl⟩,
   .intersect ⟨2⟩ ⟨8⟩ (3/4, 0)]

/-- Exact rational replay is kernel computation. The program is polymorphic;
these examples use the rational subfield to keep certificate reduction small. -/
theorem half_constructible : ConstructibleNumber (1/2 : ℝ) := by
  have h := Program.accepts_sound (Rat.castHom ℝ) (program ℚ) ⟨5⟩ .x (1/2) (by decide +kernel)
  simpa using h

/-- The second bisector constructs the first quarter. -/
theorem quarter_constructible : ConstructibleNumber (1/4 : ℝ) := by
  have h := Program.accepts_sound (Rat.castHom ℝ) (program ℚ) ⟨7⟩ .x (1/4) (by decide +kernel)
  simpa using h

/-- Bisecting between the midpoint and unit point constructs the third quarter. -/
theorem three_quarters_constructible : ConstructibleNumber (3/4 : ℝ) := by
  have h := Program.accepts_sound (Rat.castHom ℝ) (program ℚ) ⟨9⟩ .x (3/4) (by decide +kernel)
  simpa using h

end LeanOrigamiDemos.Subdivision
