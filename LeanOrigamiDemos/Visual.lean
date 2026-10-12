import LeanOrigami.Widget
import LeanOrigamiDemos.Roots

/-!
# Visual construction starting points

Place the cursor on `origami`. The `all_goals` lines keep this demonstration
file checked before a user inserts a GUI proof; they do not certify the GUI's
construction. Submission separately checks the generated expression against
the original goal. See docs/widget.md for the actual construction steps.
-/

namespace LeanOrigamiDemos.Visual
open LeanOrigami

/-- Three visual operations construct one half. -/
theorem half : ConstructibleNumber (1 / 2 : ℝ) := by
  origami
  all_goals exact ConstructibleNumber.one.div Roots.two_constructible (by norm_num)

/-- Select the positive landing when folding (1,1) onto the x-axis. -/
theorem squareRoot : ConstructibleNumber (Real.sqrt 2) := by
  origami
  all_goals exact Roots.sqrt_two

/-- A double alignment constructs the cube root as a crease's slope. -/
theorem cubeRoot : ConstructibleNumber ((2 : ℝ) ^ (1 / (3 : ℝ))) := by
  origami
  all_goals exact Roots.cube_root_two

/-- The three trisection branches can be explored; cosine goal submission is
outside the initial named-target matcher and must report that limitation. -/
theorem trisection : ConstructibleNumber (Real.cos (Real.pi / 9)) := by
  origami
  all_goals exact Roots.trisection_cos

end LeanOrigamiDemos.Visual
