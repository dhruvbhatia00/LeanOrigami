import LeanOrigamiDemos.Subdivision

/-!
# Construction certification and rejection examples

The complete saved recipe is replayed by the kernel. Expected objects and
geometric conclusions are checked separately from the rejection examples.
No native computation is used as evidence in these proofs.
-/

namespace LeanOrigamiTests.Construction
open LeanOrigami LeanOrigamiDemos.Subdivision

/-- The real interpretation of rational coordinates used in the small proof examples. -/
noncomputable abbrev real := Rat.castHom ℝ

/-- Axis and subdivision objects in their stable program-index order. -/
def expected : List (Object ℚ) :=
  [.point (0, 0), .point (1, 0),
   .line ⟨0, 1, 0, Or.inr ⟨rfl, rfl⟩⟩,
   .line ⟨1, 0, 0, Or.inl rfl⟩,
   .line ⟨1, 0, 1/2, Or.inl rfl⟩, .point (1/2, 0),
   .line ⟨1, 0, 1/4, Or.inl rfl⟩, .point (1/4, 0),
   .line ⟨1, 0, 3/4, Or.inl rfl⟩, .point (3/4, 0)]

/-- Every output, including both axes and both coordinates of each point, is exact. -/
theorem replay : Program.run (K := ℚ) (program ℚ) = .ok expected := by decide +kernel

/-- All outputs have construction histories, rather than just matching coordinates. -/
theorem all_constructed : ∀ o ∈ expected, Constructible (o.map real) :=
  Program.run_sound real (program ℚ) expected replay

example : Constructible (.point (1/2, 0)) := by
  simpa [Object.map, real] using
    all_constructed (.point (1/2, 0)) (by simp [expected])

example : Constructible (.point (1/4, 0)) := by
  simpa [Object.map, real] using
    all_constructed (.point (1/4, 0)) (by simp [expected])

example : Constructible (.point (3/4, 0)) := by
  simpa [Object.map, real] using
    all_constructed (.point (3/4, 0)) (by simp [expected])

example : Program.accepts (program ℚ) ⟨9⟩ .y 0 = true := by decide +kernel
example : Program.accepts (program ℚ) ⟨9⟩ .x (1/4) = false := by decide +kernel

-- Wrong-kind references are checked even though the reference's declared role is a point.
example : Program.run (K := ℚ)
    ((program ℚ).take 1 ++ [.fold (.axiom1 ⟨2⟩ ⟨1⟩) ⟨1, 0, 0, Or.inl rfl⟩]) =
    .error (.expectedPoint 2) := by decide +kernel

example : Program.run (K := ℚ)
    [.fold (.axiom4 ⟨0⟩ ⟨1⟩) ⟨1, 0, 0, Or.inl rfl⟩] =
    .error (.expectedLine 1) := by decide +kernel

-- Future and missing objects cannot serve as inputs, regardless of claimed output coordinates.
example : Program.run (K := ℚ)
    [.fold (.axiom1 ⟨0⟩ ⟨2⟩) ⟨1, 0, 0, Or.inl rfl⟩] =
    .error (.missingReference 2) := by decide +kernel

example : Program.run (K := ℚ)
    [.fold (.axiom1 ⟨0⟩ ⟨100⟩) ⟨1, 0, 0, Or.inl rfl⟩] =
    .error (.missingReference 100) := by decide +kernel

-- Satisfying an underconstrained fold does not permit introducing a line.
example : Program.run (K := ℚ)
    [.fold (.axiom1 ⟨0⟩ ⟨0⟩) ⟨1, 0, 0, Or.inl rfl⟩] =
    .error .coincidentPoints := by decide +kernel

example : Program.run (K := ℚ)
    [.fold (.axiom2 ⟨0⟩ ⟨0⟩) ⟨1, 0, 0, Or.inl rfl⟩] =
    .error .coincidentPoints := by decide +kernel

-- The selected output is checked, not accepted as an extra input.
example : Program.run (K := ℚ)
    [.fold (.axiom1 ⟨0⟩ ⟨1⟩) ⟨1, 0, 0, Or.inl rfl⟩] =
    .error .incorrectOutput := by decide +kernel

example : Program.run (K := ℚ)
    ((program ℚ).take 3 ++ [.intersect ⟨2⟩ ⟨4⟩ (42, 0)]) =
    .error .incorrectOutput := by decide +kernel

example : Program.run (K := ℚ)
    ((program ℚ).take 2 ++ [.intersect ⟨3⟩ ⟨3⟩ (0, 0)]) =
    .error .coincidentLines := by decide +kernel

example : Program.run (K := ℚ)
    ((program ℚ).take 2 ++
      [.fold (.axiom4 ⟨1⟩ ⟨2⟩) ⟨1, 0, 1, Or.inl rfl⟩,
       .intersect ⟨3⟩ ⟨4⟩ (0, 0)]) = .error .parallelLines := by decide +kernel

-- Underconstrained requests remain errors even when the selected line satisfies them.
example : Program.run (K := ℚ) ((program ℚ).take 1 ++
    [.fold (.axiom3 ⟨2⟩ ⟨2⟩) ⟨1, 0, 0, Or.inl rfl⟩]) =
    .error .underconstrainedFold := by decide +kernel
example : Program.run (K := ℚ) ((program ℚ).take 1 ++
    [.fold (.axiom5 ⟨0⟩ ⟨1⟩ ⟨2⟩) ⟨1, 0, 0, Or.inl rfl⟩]) =
    .error .incorrectOutput := by decide +kernel
example : Program.run (K := ℚ) ((program ℚ).take 1 ++
    [.fold (.axiom6 ⟨0⟩ ⟨1⟩ ⟨2⟩ ⟨2⟩) ⟨1, 0, 0, Or.inl rfl⟩]) =
    .error .underconstrainedFold := by decide +kernel
example : Program.run (K := ℚ) ((program ℚ).take 1 ++
    [.fold (.axiom7 ⟨0⟩ ⟨2⟩ ⟨2⟩) ⟨1, 0, 0, Or.inl rfl⟩]) =
    .error .underconstrainedFold := by decide +kernel

-- Rule 2 works for a horizontal crease and an oblique crease as well as vertical ones.
example : (Line.bisector (0, 0) ((0, 2) : Point ℚ) (by decide)).reflect
    (0, 0) = (0, 2) := Line.bisector_reflect _ _ _
example : (Line.bisector (0, 0) ((2, 2) : Point ℚ) (by decide)) =
    (⟨1, 1, 2, Or.inl rfl⟩ : Line ℚ) := by decide +kernel

-- Rule 4 accepts a point already on an oblique input line.
example : (Line.perpendicularThrough (0, 0) (⟨1, 1, 0, Or.inl rfl⟩ : Line ℚ)) =
    ⟨1, -1, 0, Or.inl rfl⟩ := by decide +kernel

#print axioms Line.bisector_reflect
#print axioms Line.bisector_unique
#print axioms FoldInput.axiom2_admissible_iff
#print axioms FoldInput.axiom4_solutions
#print axioms Program.run_sound
#print axioms Program.accepts_sound
#print axioms all_constructed
#print axioms half_constructible
#print axioms quarter_constructible
#print axioms three_quarters_constructible

end LeanOrigamiTests.Construction
