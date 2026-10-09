import LeanOrigamiDemos.OffAxis
import LeanOrigami.Solvers.Equations

/-!
# Multiple branches and exceptional point-to-line folds

These examples check both geometric statements and saved-program replay.
The elimination examples expose the equations and their guards. Complete
rule-6 replay and discovery are checked in the other fold tests.
-/

namespace LeanOrigamiTests.PointLine
open LeanOrigami

private def xAxis : Line ℚ := ⟨0, 1, 0, Or.inr ⟨rfl, rfl⟩⟩
private def yAxis : Line ℚ := ⟨1, 0, 0, Or.inl rfl⟩

-- Both selected rule-5 branches lead to exact off-axis points.
example : Program.accepts (LeanOrigami.Basis.program ℚ true) ⟨8⟩ .y 1 = true := by
  decide +kernel
example : Program.accepts (LeanOrigami.Basis.program ℚ false) ⟨8⟩ .y (-1) = true := by
  decide +kernel
example : Program.accepts (LeanOrigami.Basis.program ℚ false) ⟨8⟩ .y 1 = false := by
  decide +kernel

-- Coincident source/fixed point on its target leaves infinitely many creases.
example : Program.run (K := ℚ)
    [.fold (.axiom1 ⟨0⟩ ⟨1⟩) xAxis,
     .fold (.axiom5 ⟨0⟩ ⟨0⟩ ⟨2⟩) yAxis] = .error .underconstrainedFold := by
  decide +kernel

-- The same coincidence off the target has no solution, not infinitely many.
example : Program.run (K := ℚ)
    [.fold (.axiom1 ⟨0⟩ ⟨1⟩) xAxis,
     .fold (.axiom4 ⟨0⟩ ⟨2⟩) yAxis,
     .fold (.axiom5 ⟨1⟩ ⟨1⟩ ⟨3⟩) xAxis] = .error .noFoldSolutions := by
  decide +kernel

-- A tangent landing circle leaves the source unmoved. The horizontal
-- crease through source and fixed point is still a valid rule-5 choice.
example : Program.accepts (K := ℚ)
    [.fold (.axiom1 ⟨0⟩ ⟨1⟩) xAxis,
     .fold (.axiom4 ⟨1⟩ ⟨2⟩) ⟨1, 0, 1, Or.inl rfl⟩,
     .fold (.axiom5 ⟨1⟩ ⟨0⟩ ⟨3⟩) xAxis] ⟨1⟩ .x 1 = true := by
  decide +kernel

-- When the source is on its target there may also be a moved branch.
example : (FoldInput.axiom5 (0, 0) (1, 1) yAxis).Satisfies
    (⟨1, -1, 0, Or.inl rfl⟩ : Line ℚ) := by
  norm_num [FoldInput.Satisfies, Line.reflect, Line.residual, Line.normalSq,
    Line.Contains, yAxis]
example : (FoldInput.axiom5 (0, 0) (1, 1) yAxis).Satisfies
    (⟨0, 1, 1, Or.inr ⟨rfl, rfl⟩⟩ : Line ℚ) := by
  norm_num [FoldInput.Satisfies, Line.reflect, Line.residual, Line.normalSq,
    Line.Contains, yAxis]

-- The geometric admissibility test ranges over ALL real creases.
example : ¬(FoldInput.axiom5 (0, 0) (0, 0)
    (Line.horizontal (0 : ℝ))).Admissible := by
  simp [FoldInput.axiom5_admissible_iff, Line.horizontal, Line.Contains]
example : (FoldInput.axiom5 (0, 0) (0, 0)
    (Line.horizontal (1 : ℝ))).Admissible := by
  simp [FoldInput.axiom5_admissible_iff, Line.horizontal, Line.Contains]

-- Three distinct creases satisfy this rule-6 configuration, one horizontal.
private def threeInput : FoldInput ℚ :=
  .axiom6 (0, 1) (0, -1) (Line.horizontal (-1)) yAxis
example : threeInput.Satisfies (Line.chart 1 (-1)) ∧
    threeInput.Satisfies (Line.horizontal 0) ∧
    threeInput.Satisfies (Line.chart (-1) 1) := by
  norm_num [threeInput, FoldInput.Satisfies, Line.chart, Line.horizontal,
    Line.reflect, Line.residual, Line.normalSq, Line.Contains, yAxis]
example : (Line.chart (1 : ℚ) (-1)) ≠ Line.horizontal 0 ∧
    (Line.chart (1 : ℚ) (-1)) ≠ Line.chart (-1) 1 ∧
    (Line.horizontal (0 : ℚ)) ≠ Line.chart (-1) 1 := by decide +kernel

-- A zero eliminant does not certify a crease when both dot products vanish.
example : FoldInput.axiom6Eliminant (0, 1) (0, 2) xAxis xAxis (0 : ℚ) = 0 ∧
    ¬(FoldInput.axiom6 (0, 1) (0, 2) xAxis xAxis).Satisfies (Line.chart 0 0) := by
  norm_num [FoldInput.axiom6Eliminant, FoldInput.Satisfies, Line.chartDot,
    Line.chart, Line.reflect, Line.residual, Line.normalSq, Line.Contains, xAxis]

#print axioms FoldInput.axiom5_admissible_iff
#print axioms FoldInput.axiom5_solutions_subset_pair
#print axioms FoldInput.axiom5_iff_landing
#print axioms FoldInput.axiom6_iff_eliminant
#print axioms FoldInput.axiom6_horizontal_leading_zero
#print axioms LeanOrigami.Basis.point_constructible

end LeanOrigamiTests.PointLine
