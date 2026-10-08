import LeanOrigami.Folds
import LeanOrigami.Geometry.Euclidean

/-!
# Geometry and fold-rule examples

These small real-plane proofs illustrate the public geometry and specification
API. Inputs here are geometric objects, not claims of construction history.
-/

namespace LeanOrigamiTests.Geometry
open LeanOrigami

/-- The vertical line at a specified horizontal coordinate. -/
def vertical (x : ℝ) : Line ℝ := ⟨1, 0, x, Or.inl rfl⟩

/-- The horizontal line at a specified vertical coordinate. -/
def horizontal (y : ℝ) : Line ℝ := ⟨0, 1, y, Or.inr ⟨rfl, rfl⟩⟩

-- Equivalent equations, including negative scaling, have identical representations.
example : Line.normalize (2 : ℝ) 2 2 (by norm_num) =
    Line.normalize 1 1 1 (by norm_num) := by
  ext <;> norm_num [Line.normalize]

example : Line.normalize (-3 : ℝ) (-6) (-9) (by norm_num) =
    Line.normalize 1 2 3 (by norm_num) := by
  ext <;> norm_num [Line.normalize]

example (l : Line ℝ) : Line.normalize l.a l.b l.c l.normal_ne_zero = l :=
  l.normalize_self

-- Both inconsistent and vacuous equations are rejected as lines.
example : Line.ofCoefficients? (0 : ℝ) 0 1 = none := Line.ofCoefficients_zero 1
example : Line.ofCoefficients? (0 : ℝ) 0 0 = none := Line.ofCoefficients_zero 0

-- Reflection works for vertical creases without converting them to slopes.
example : (vertical 1).reflect (0, 0) = (2, 0) := by
  norm_num [vertical, Line.reflect, Line.residual, Line.normalSq]

example (y : ℝ) : (vertical 1).reflect (1, y) = (1, y) := by
  apply (Line.reflect_eq_self _ _).mpr
  simp [vertical, Line.Contains]

example (l : Line ℝ) (p : Point ℝ) : l.reflect (l.reflect p) = p :=
  l.reflect_reflect p

-- Axis-aligned and oblique intersections satisfy exact coordinate conclusions.
example : (vertical 2).intersection (horizontal 3) (by norm_num [Line.determinant, vertical, horizontal]) =
    (2, 3) := by
  norm_num [Line.intersection, Line.determinant, vertical, horizontal]

example : (Line.normalize (1 : ℝ) 1 3 (by norm_num)).intersection
    (Line.normalize 1 (-1) 1 (by norm_num)) (by norm_num [Line.determinant, Line.normalize]) =
    (2, 1) := by
  norm_num [Line.intersection, Line.determinant, Line.normalize]

example (p : Point ℝ) : ¬ LegalIntersection (vertical 0) (vertical 0) p :=
  not_legalIntersection_self _ _

example (p : Point ℝ) : ¬ LegalIntersection (vertical 0) (vertical 1) p := by
  rintro ⟨h₀, h₁, _⟩
  simp [vertical, Line.Contains] at h₀ h₁
  linarith

-- Rule 1: the crease passes through two distinct points.
example : (FoldInput.axiom1 (1, 0) (1, 2)).Satisfies (vertical 1) := by
  norm_num [FoldInput.Satisfies, vertical, Line.Contains]

-- Rule 2: the crease reflects one point exactly onto the other.
example : (FoldInput.axiom2 (0, 0) (2, 0)).Satisfies (vertical 1) := by
  norm_num [FoldInput.Satisfies, vertical, Line.reflect, Line.residual, Line.normalSq]

-- Rule 3: the entire line x=0 is reflected onto x=2, not just a chosen point.
example : (FoldInput.axiom3 (vertical 0) (vertical 2)).Satisfies (vertical 1) := by
  intro p
  simp [vertical, Line.Contains, Line.reflect, Line.residual, Line.normalSq]
  constructor <;> intro h <;> linarith

-- Matching one point does not mean that an entire line has been aligned.
example : ¬ (FoldInput.axiom3 (vertical 0) (horizontal 0)).Satisfies (vertical 1) := by
  intro h
  have hp := (h (0, 1)).mp (by norm_num [vertical, Line.Contains])
  norm_num [vertical, horizontal, Line.Contains, Line.reflect, Line.residual, Line.normalSq] at hp

-- Rule 4: pass through the point and fold perpendicular to the given line.
example : (FoldInput.axiom4 (1, 4) (horizontal 0)).Satisfies (vertical 1) := by
  norm_num [FoldInput.Satisfies, vertical, horizontal, Line.Contains, Line.Perpendicular]

-- Rule 5: move the first point onto its target while keeping the second on the crease.
example : (FoldInput.axiom5 (0, 0) (1, 3) (vertical 2)).Satisfies (vertical 1) := by
  norm_num [FoldInput.Satisfies, vertical, Line.Contains, Line.reflect, Line.residual, Line.normalSq]

-- Rule 6: both point-to-line constraints must hold for the same crease.
example : (FoldInput.axiom6 (0, 0) (0, 1) (vertical 2) (horizontal 1)).Satisfies (vertical 1) := by
  norm_num [FoldInput.Satisfies, vertical, horizontal, Line.Contains,
    Line.reflect, Line.residual, Line.normalSq]

-- Rule 7: the target line and the perpendicularity line have different roles.
example : (FoldInput.axiom7 (0, 0) (vertical 2) (horizontal 0)).Satisfies (vertical 1) := by
  norm_num [FoldInput.Satisfies, vertical, horizontal, Line.Contains,
    Line.Perpendicular, Line.reflect, Line.residual, Line.normalSq]

-- The second line in rule 7 is essential: this crease is not perpendicular to x=0.
example : ¬ (FoldInput.axiom7 (0, 0) (vertical 2) (vertical 0)).Satisfies (vertical 1) := by
  norm_num [FoldInput.Satisfies, vertical, Line.Perpendicular]

-- A satisfying crease is not necessarily a legal choice.
example : (FoldInput.axiom1 (1, 0) (1, 0)).Satisfies (vertical 1) := by
  norm_num [FoldInput.Satisfies, vertical, Line.Contains]

example : ¬ (FoldInput.axiom1 (1, 0) (1, 0)).Legal (vertical 1) :=
  FoldInput.not_legal_of_not_admissible (FoldInput.axiom1_same_not_admissible _) _

example : (FoldInput.axiom1 (1, 0) (1, 2)).Legal (vertical 1) := by
  constructor
  · apply (FoldInput.axiom1_admissible_iff _ _).mpr
    norm_num
  · norm_num [FoldInput.Satisfies, vertical, Line.Contains]

-- The Mathlib bridge checks the meaning of the coordinate implementation.
example (l : Line ℝ) (p : Point ℝ) : (l.reflect p).toPlane =
    EuclideanGeometry.reflection l.affine p.toPlane := l.reflect_eq_mathlib p

#print axioms Line.normalize_scale
#print axioms Line.ext_contains
#print axioms Line.intersection_unique
#print axioms Line.reflect_reflect
#print axioms Line.reflect_eq_mathlib
#print axioms Line.perpendicular_iff_isOrtho
#print axioms FoldInput.axiom3_iff_image
#print axioms FoldInput.axiom1_admissible_iff
#print axioms FoldInput.axiom2_same_not_admissible
#print axioms legalIntersection_iff

end LeanOrigamiTests.Geometry
