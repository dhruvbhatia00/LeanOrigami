import LeanOrigami.Text
import LeanOrigamiDemos.RootPrograms
import LeanOrigamiDemos.Roots

/-!
# Submission proofs for the saved irrational programs

The generic certificates prove acceptance of the very same programs used by
native Hex replay. Their hypotheses identify the exact selected roots. The
named real conclusions below use `accepts_sound`, not separate construction
histories. Ordinary `do` notation in RootPrograms supplies the text interface.
-/

namespace LeanOrigamiDemos.Text
open LeanOrigami

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- Certificate for the saved cubic program, valid over the executable scalar field too. -/
theorem cubeAcceptance {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (t : K) (ht : t^3 = 2) (hp : 0 < t) :
    Program.accepts (RootPrograms.cubeRootTwo K t).1
      (RootPrograms.cubeRootTwo K t).2 .x t = true := by
  origami_check using
    try simp only [Basis.height, ite_true]
    try origami_geometry
    all_goals
      norm_num [Line.perpendicularThrough, Line.normalize, RootGeometry.crease,
        ht, ne_of_gt hp, ne_of_lt (neg_neg_of_pos hp)]
      all_goals field_simp
      all_goals (try constructor) <;> first | (solve | ring) | nlinarith

#print axioms cubeAcceptance

/-- Certify the square-root guard and every instruction of the saved program. -/
theorem sqrtAcceptance {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (t : K) (ht : t^2 = 2) (hp : 0 < t) :
    let saved := (RootPrograms.squareRootTwo K t).getD ([], ⟨0⟩)
    Program.accepts saved.1 saved.2 .x t = true := by
  have hc : t^3 = 2*t := by nlinarith [congrArg (fun z : K => t*z) ht]
  dsimp only
  simp (config := { zeta := false }) only [RootPrograms.squareRootTwo, RootRecipe.squareRoot, le_of_lt hp, ht,
    and_self, ite_true]
  origami_check using
    try simp only [Basis.height, ite_true]
    all_goals first
    | (apply (RootGeometry.satisfies_iff _ _ _ _).mpr; nlinarith)
    | origami_geometry
    all_goals
      norm_num [Line.perpendicularThrough, Line.normalize, RootGeometry.crease,
        ht, ne_of_gt hp, ne_of_lt (neg_neg_of_pos hp)]
      all_goals field_simp
      all_goals ring

#print axioms sqrtAcceptance

set_option maxHeartbeats 4000000 in
/-- The second root uses the constructed first root as its coefficient. -/
theorem fourthAcceptance {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (s t : K) (hs : s^2 = 2) (ht : t^2 = s) (sp : 0 < s) (tp : 0 < t) :
    let saved := (RootPrograms.fourthRootTwo K s t).getD ([], ⟨0⟩)
    Program.accepts saved.1 saved.2 .x t = true := by
  have sc : s^3 = 2*s := by nlinarith [congrArg (fun z : K => s*z) hs]
  have tc : t^3 = s*t := by nlinarith [congrArg (fun z : K => t*z) ht]
  dsimp only
  simp (config := { zeta := false }) only [RootPrograms.fourthRootTwo, RootRecipe.squareRoot,
    le_of_lt sp, le_of_lt tp, hs, ht, and_self, ite_true]
  origami_check using
    try simp only [Basis.height, ite_true]
    all_goals first
    | (apply (RootGeometry.satisfies_iff _ _ _ _).mpr; nlinarith)
    | origami_geometry
    all_goals
      norm_num [Line.normalize, RootGeometry.crease, hs, ht,
        ne_of_gt sp, ne_of_gt tp, ne_of_lt (neg_neg_of_pos sp), ne_of_lt (neg_neg_of_pos tp)]
      all_goals field_simp
      all_goals ring

#print axioms fourthAcceptance

set_option maxHeartbeats 4000000 in
/-- Certify both coordinates of the complete upper-circle construction. -/
theorem trisectionAcceptance {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (x y : K) (hx : 8*x^3-6*x-1 = 0) (hy : y^2 = 1-x^2)
    (xl : (1/2 : K) < x) (xu : x < 1) (yp : 0 < y) (coordinate : Coordinate) :
    let saved := (RootPrograms.trisectionPoint K x y).getD ([], ⟨0⟩)
    Program.accepts saved.1 saved.2 coordinate (coordinate.get (x, y)) = true := by
  have xp : 0 < x := lt_trans (by norm_num) xl
  have hy' : y^2 = 1-x*x := by nlinarith [hy]
  have yc : y^3 = (1-x^2)*y := by nlinarith [congrArg (fun z : K => y*z) hy]
  dsimp only
  simp (config := { zeta := false }) only [RootPrograms.trisectionPoint, RootRecipe.squareRoot,
    xl, xu, yp, and_self, not_true_eq_false, ite_false, le_of_lt yp, hy', ite_true]
  origami_check using
    try simp only [Basis.height, ite_true]
    all_goals first
    | (apply (RootGeometry.satisfies_iff _ _ _ _).mpr; nlinarith)
    | origami_geometry
    all_goals
      norm_num [Line.normalize, RootGeometry.crease, ← hy', ← hy,
        ne_of_gt xp, ne_of_gt yp, ne_of_lt (neg_neg_of_pos xp), ne_of_lt (neg_neg_of_pos yp)]
      all_goals field_simp
      all_goals norm_num
      all_goals first | (solve | ring) | nlinarith

#print axioms trisectionAcceptance

/-- Submit the exact nonnegative square root of two. -/
theorem sqrt_two : ConstructibleNumber (Real.sqrt 2) :=
  Program.accepts_sound (RingHom.id ℝ) _ _ .x _
    (sqrtAcceptance _ (by norm_num) (by positivity))

/-- Submit the saved cube-doubling program. -/
theorem cube_root_two : ConstructibleNumber Roots.cubeRootTwo :=
  Program.accepts_sound (RingHom.id ℝ) _ _ .x _
    (cubeAcceptance _ Roots.cubeRootTwo_cubed (Real.rpow_pos_of_pos (by norm_num) _))

/-- Submit a root used as the input to another root construction. -/
theorem fourth_root_two : ConstructibleNumber (Real.sqrt (Real.sqrt 2)) :=
  Program.accepts_sound (RingHom.id ℝ) _ _ .x _
    (fourthAcceptance _ _ (by norm_num) (Real.sq_sqrt (Real.sqrt_nonneg _))
      (by positivity) (by positivity))

/-- Both submitted coordinates come from one saved trisection point. -/
theorem trisection_coordinate (coordinate : Coordinate) :
    ConstructibleNumber (coordinate.get (Real.cos (Real.pi/9), Real.sin (Real.pi/9))) :=
  Program.accepts_sound (RingHom.id ℝ) _ _ coordinate _
    (trisectionAcceptance _ _ Roots.trisection_polynomial
      (by nlinarith [Roots.trisection_angle.1])
      Roots.trisection_branch.1 Roots.trisection_branch.2 Roots.trisection_angle.2.1 coordinate)

/-- The full upper unit-circle point is obtained from the submitted coordinates. -/
theorem trisection_point : Constructible
    (.point (Real.cos (Real.pi/9), Real.sin (Real.pi/9))) :=
  ConstructibleNumber.point (trisection_coordinate .x) (trisection_coordinate .y)

/-- Closed output theorem for portable source export. -/
theorem trisection_cosine : ConstructibleNumber (Real.cos (Real.pi/9)) :=
  trisection_coordinate .x

#print axioms sqrt_two
#print axioms cube_root_two
#print axioms fourth_root_two
#print axioms trisection_point

end LeanOrigamiDemos.Text

origami_artifact LeanOrigamiDemos.Text.trisection_cosine as LeanOrigamiDemos.textExamples
