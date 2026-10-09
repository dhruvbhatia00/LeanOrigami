import LeanOrigami.Construction.Roots
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Square roots, cube doubling, and trisection

These are kernel-checked construction histories from the two standard seeds.
The trisection identifies the upper unit-circle point at angle `π/9`, including
its branch, rather than merely exhibiting an unspecified cubic root.
Executable recipe replay is tested separately in RootConstructions.lean.
-/

namespace LeanOrigamiDemos.Roots
open LeanOrigami ConstructibleNumber

/-- The unit sum supplies the coefficient two. -/
theorem two_constructible : ConstructibleNumber (2 : ℝ) := by
  convert one.add one using 1; norm_num

/-- The constructed output is exactly the nonnegative square root of two. -/
theorem sqrt_two : ConstructibleNumber (Real.sqrt 2) :=
  two_constructible.sqrt (by norm_num)

/-- The positive real cube root of two, using Mathlib's real power notation. -/
noncomputable def cubeRootTwo : ℝ := (2 : ℝ) ^ (1 / (3 : ℝ))

/-- The named length doubles the volume of a unit cube. -/
theorem cubeRootTwo_cubed : cubeRootTwo^3 = 2 := by
  simpa [cubeRootTwo] using Real.rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 2) (by decide : (3 : ℕ) ≠ 0)

/-- Cube doubling is a construction, not just an algebraic existence claim. -/
theorem cube_root_two : ConstructibleNumber cubeRootTwo := by
  apply monic_cubic_root zero zero two_constructible.neg
  nlinarith [cubeRootTwo_cubed]

/-- A root can be used as a coefficient of a further root construction. -/
theorem fourth_root_two : ConstructibleNumber (Real.sqrt (Real.sqrt 2)) :=
  sqrt_two.sqrt (Real.sqrt_nonneg 2)

/-- The original sixty-degree ray also has a constructed unit-circle point. -/
theorem sixty_degree_point : Constructible
    (.point (Real.cos (Real.pi/3), Real.sin (Real.pi/3))) := by
  rw [Real.cos_pi_div_three, Real.sin_pi_div_three]
  have hthree : ConstructibleNumber (3 : ℝ) := by
    convert two_constructible.add one using 1; norm_num
  exact point (one.div two_constructible (by norm_num))
    ((hthree.sqrt (by norm_num)).div two_constructible (by norm_num))

/-- Triple-angle identity specialized to the cubic for twenty degrees. -/
theorem trisection_polynomial :
    8 * Real.cos (Real.pi/9)^3 - 6 * Real.cos (Real.pi/9) - 1 = 0 := by
  have h := Real.cos_three_mul (Real.pi/9)
  have he : 3 * (Real.pi/9) = Real.pi/3 := by ring
  rw [he, Real.cos_pi_div_three] at h
  linarith

/-- This is the root between one half and one, not either other real root. -/
theorem trisection_branch : 1/2 < Real.cos (Real.pi/9) ∧ Real.cos (Real.pi/9) < 1 := by
  have hp := Real.pi_pos
  constructor
  · have h := Real.cos_lt_cos_of_nonneg_of_le_pi
      (by positivity : 0 ≤ Real.pi/9) (by linarith : Real.pi/3 ≤ Real.pi)
      (by linarith : Real.pi/9 < Real.pi/3)
    simpa [Real.cos_pi_div_three] using h
  · have h := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ))
      (by linarith : Real.pi/9 ≤ Real.pi) (by positivity : 0 < Real.pi/9)
    simpa using h

/-- The interval identifies a unique root of the trisection polynomial. -/
theorem trisection_root_unique {x : ℝ} (hx : 1/2 < x)
    (he : 8*x^3-6*x-1 = 0) : x = Real.cos (Real.pi/9) := by
  let y := Real.cos (Real.pi/9)
  have hy : 1/2 < y := trisection_branch.1
  have hp : 8*y^3-6*y-1 = 0 := trisection_polynomial
  have hxx : 1/4 < x^2 := by nlinarith
  have hyy : 1/4 < y^2 := by nlinarith
  have hxy : 1/4 < x*y := by nlinarith [mul_pos (by linarith : 0 < x-1/2) (by linarith : 0 < y-1/2)]
  have hf : (x-y)*(8*(x^2+x*y+y^2)-6) = 0 := by nlinarith [he, hp]
  have hn : 8*(x^2+x*y+y^2)-6 ≠ 0 := by linarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right hn)

/-- The cubic construction produces the horizontal coordinate of the trisector. -/
theorem trisection_cos : ConstructibleNumber (Real.cos (Real.pi/9)) := by
  have htwo := two_constructible
  have hfour := htwo.add htwo
  have height := hfour.add hfour
  have hsix := hfour.add htwo
  apply cubic_root (a := 8) (b := 0) (c := -6) (d := -1)
  · convert height using 1; norm_num
  · exact zero
  · convert hsix.neg using 1; norm_num
  · exact one.neg
  · norm_num
  · nlinarith [trisection_polynomial]

/-- Recover the positive vertical coordinate using the square-root construction. -/
theorem trisection_sin : ConstructibleNumber (Real.sin (Real.pi/9)) := by
  have h := one.sub (trisection_cos.mul trisection_cos)
  have hp := Real.pi_pos
  have hs := Real.sin_sq_add_cos_sq (Real.pi/9)
  have hn : 0 ≤ 1 - Real.cos (Real.pi/9)*Real.cos (Real.pi/9) := by
    nlinarith [sq_nonneg (Real.sin (Real.pi/9))]
  have he := Real.sin_eq_sqrt_one_sub_cos_sq
    (by positivity : 0 ≤ Real.pi/9) (by linarith : Real.pi/9 ≤ Real.pi)
  rw [he]
  simpa [pow_two] using h.sqrt hn

/-- The actual upper unit-circle point is constructible. -/
theorem trisection_point : Constructible
    (.point (Real.cos (Real.pi/9), Real.sin (Real.pi/9))) :=
  point trisection_cos trisection_sin

/-- The constructed point lies on the upper unit circle and its angle with
the positive horizontal ray, expressed by arccos, is one third of sixty degrees. -/
theorem trisection_angle :
    Real.cos (Real.pi/9)^2 + Real.sin (Real.pi/9)^2 = 1 ∧
    0 < Real.sin (Real.pi/9) ∧
    3 * Real.arccos (Real.cos (Real.pi/9)) = Real.pi/3 := by
  have hp := Real.pi_pos
  refine ⟨by nlinarith [Real.sin_sq_add_cos_sq (Real.pi/9)], ?_, ?_⟩
  · exact Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  · rw [Real.arccos_cos (by positivity) (by linarith)]
    ring

/-- Exact polynomial, interval, and circle checks identify the complete point.
This is the bridge from a saved algebraic candidate to the named angle. -/
theorem trisection_identification {x y : ℝ} (hx : 1/2 < x) (hy : 0 < y)
    (hp : 8*x^3-6*x-1 = 0) (hcircle : x^2+y^2 = 1) :
    (x, y) = (Real.cos (Real.pi/9), Real.sin (Real.pi/9)) := by
  have he := trisection_root_unique hx hp
  subst x
  congr 1
  have hs := Real.sin_sq_add_cos_sq (Real.pi/9)
  have hpos := trisection_angle.2.1
  nlinarith

#print axioms sqrt_two
#print axioms cube_root_two
#print axioms fourth_root_two
#print axioms trisection_point
#print axioms trisection_angle
#print axioms trisection_identification

end LeanOrigamiDemos.Roots
