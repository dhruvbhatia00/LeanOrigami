import LeanOrigami.Construction.Checker
import LeanOrigami.Solvers.Bisectors

/-!
# Line alignment and cubic-fold checks

Exact selected creases are checked independently of root discovery. These
examples cover the remaining primitive rules and their infinite families.
-/

namespace LeanOrigamiTests.RemainingFolds
open LeanOrigami

private def accepted (input : FoldInput ℚ) (crease : Line ℚ) : Bool :=
  match Solver.fold input crease with
  | .ok _ => true
  | .error _ => false

-- Perpendicular axes have two bisectors; parallel lines have one midline.
example : accepted (.axiom3 (Line.horizontal 0) (Line.chart 0 0))
    (Line.chart 1 0) = true := by decide +kernel
example : accepted (.axiom3 (Line.horizontal 0) (Line.chart 0 0))
    (Line.chart (-1) 0) = true := by decide +kernel
example : accepted (.axiom3 (Line.horizontal 0) (Line.horizontal 2))
    (Line.horizontal 1) = true := by decide +kernel
example : accepted (.axiom3 (Line.horizontal 0) (Line.horizontal 0))
    (Line.chart 0 0) = false := by decide +kernel
example : accepted (.axiom3 (Line.horizontal 0) (Line.chart 0 0))
    (Line.chart 1 1) = false := by decide +kernel

-- Rule 7 has one crease, no crease, or infinitely many, respectively.
example : accepted (.axiom7 (0, 0) (Line.chart 0 2) (Line.horizontal 0))
    (Line.chart 0 1) = true := by decide +kernel
example : accepted (.axiom7 (0, 1) (Line.horizontal 0) (Line.horizontal 0))
    (Line.chart 0 0) = false := by decide +kernel
example : accepted (.axiom7 (0, 0) (Line.horizontal 0) (Line.horizontal 0))
    (Line.chart 0 0) = false := by decide +kernel

-- A lower-degree eliminant can still have a horizontal solution.
example : accepted (.axiom6 (0, 1) (0, 0) (Line.horizontal (-1)) (Line.horizontal 0))
    (Line.horizontal 0) = true := by decide +kernel

-- Two choices: the source points are already on their nonparallel targets.
example : accepted (.axiom6 (0, 1) (0, 0) (Line.horizontal 1) (Line.chart 0 0))
    (Line.chart 0 0) = true ∧
    accepted (.axiom6 (0, 1) (0, 0) (Line.horizontal 1) (Line.chart 0 0))
    (Line.horizontal 1) = true := by decide +kernel

-- Three choices, including the direction omitted by the nonhorizontal chart.
example : let input : FoldInput ℚ :=
      .axiom6 (0, 1) (0, -1) (Line.horizontal (-1)) (Line.chart 0 0)
    accepted input (Line.chart 1 (-1)) = true ∧
    accepted input (Line.chart (-1) 1) = true ∧
    accepted input (Line.horizontal 0) = true ∧
    accepted input (Line.chart 0 0) = false := by decide +kernel

-- These are separate infinite families. Both must be rejected.
example : ¬(FoldInput.axiom6 (0, 0) (0, 1)
    (Line.horizontal 0) (Line.horizontal 1)).Admissible := by
  apply FoldInput.axiom6_free_not_admissible
  norm_num [FoldInput.axiom6FreeDirection, Line.determinant, Line.Contains, Line.horizontal]
example : ¬(FoldInput.axiom6 (0, 1) (0, 1)
    (Line.horizontal 0) (Line.horizontal 0)).Admissible := by
  apply FoldInput.axiom6_zero_polynomial_not_admissible
  norm_num [FoldInput.axiom6Polynomial, Univariate.Cubic.IsZero, Line.horizontal, Line.residual]

#print axioms FoldInput.axiom3_intersecting_exactly_two
#print axioms FoldInput.axiom3_admissible_iff
#print axioms FoldInput.axiom3_solutions_subset_pair
#print axioms FoldInput.axiom6_admissible_iff
#print axioms FoldInput.axiom6_solutions_bound
#print axioms FoldInput.axiom7_admissible_iff
#print axioms FoldInput.axiom7_solutions_subsingleton
#print axioms Solver.fold_succeeds_iff
#print axioms Program.accepts_sound

end LeanOrigamiTests.RemainingFolds
