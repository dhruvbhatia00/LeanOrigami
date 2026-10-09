import LeanOrigami.Text
import LeanOrigamiDemos.Roots

/-!
# Text proofs of the irrational examples

Every root choice is an exact expression with checked branch conditions.
Coefficients are obtained from seeds by named arithmetic constructions. These
proofs do not evaluate Hex or assume that a native replay test succeeded.
-/

namespace LeanOrigamiDemos.Text
open LeanOrigami

/-- A reusable construction written in the same language as its callers. -/
def twice (a : LeanOrigami.Text.Number) : LeanOrigami.Text.Number := by
  origami
    number result := add a a
    finish result

/-- Square root of two, with a checked nonnegative branch. -/
theorem sqrt_two : ConstructibleNumber (Real.sqrt 2) := by
  origami
    point U := unit
    number one := x U
    number two := use (twice one)
    number root := sqrt two choose (Real.sqrt 2) proving (by
      origami_values
      constructor
      · positivity
      · norm_num [twice, LeanOrigami.Text.add])
    submit root

/-- A saved cube-root choice is checked against the constructed coefficients. -/
theorem cube_root_two : ConstructibleNumber Roots.cubeRootTwo := by
  origami
    point O := origin
    point U := unit
    number zero := x O
    number one := x U
    number two := add one one
    number negativeTwo := sub zero two
    number root := cubic one zero zero negativeTwo choose Roots.cubeRootTwo proving (by
      origami_values
      constructor
      · norm_num
      · nlinarith [Roots.cubeRootTwo_cubed])
    submit root

/-- Reuse the first root as the coefficient for a second root construction. -/
theorem fourth_root_two : ConstructibleNumber (Real.sqrt (Real.sqrt 2)) := by
  origami
    point U := unit
    number one := x U
    number two := add one one
    number square := sqrt two choose (Real.sqrt 2) proving (by
      origami_values
      constructor
      · positivity
      · norm_num)
    number fourth := sqrt square choose (Real.sqrt (Real.sqrt 2)) proving (by
      origami_values
      exact ⟨Real.sqrt_nonneg _, Real.sq_sqrt (Real.sqrt_nonneg _)⟩)
    submit fourth

/-- Construct both coordinates of the upper twenty-degree unit-circle point. -/
noncomputable def trisection : LeanOrigami.Text.Point := by
  origami
    point O := origin
    point U := unit
    number zero := x O
    number one := x U
    number two := add one one
    number four := add two two
    number six := add four two
    number eight := add four four
    number negativeSix := sub zero six
    number negativeOne := sub zero one
    number cosine := cubic eight zero negativeSix negativeOne
      choose (Real.cos (Real.pi/9)) proving (by
        origami_values
        constructor
        · norm_num
        · nlinarith [Roots.trisection_polynomial])
    number square := mul cosine cosine
    number radicand := sub one square
    number sine := sqrt radicand choose (Real.sin (Real.pi/9)) proving (by
      origami_values
      exact ⟨le_of_lt Roots.trisection_angle.2.1,
        by nlinarith [Real.sin_sq_add_cos_sq (Real.pi/9)]⟩)
    point trisector := pair cosine sine
    finish trisector

/-- The selected coordinate is the named cosine, with its exact angle identified
by the separately proved unit-circle and branch theorem. -/
theorem trisection_coordinate : ConstructibleNumber (Real.cos (Real.pi/9)) := by
  origami
    point P := use trisection
    number result := x P
    submit result proving (by rfl)

/-- The saved point, not an unspecified root, has angle twenty degrees. -/
theorem trisection_identified : trisection.value =
    (Real.cos (Real.pi/9), Real.sin (Real.pi/9)) := rfl

#print axioms sqrt_two
#print axioms cube_root_two
#print axioms fourth_root_two
#print axioms trisection_coordinate

end LeanOrigamiDemos.Text

-- Capture at file scope so the exported prefix has no unclosed namespace.
origami_artifact LeanOrigamiDemos.Text.trisection_coordinate as LeanOrigamiDemos.textExamples
