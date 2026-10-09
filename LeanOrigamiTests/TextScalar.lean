import LeanOrigami.Scalar
import HexNumberFieldMathlib.Radical
import LeanOrigamiDemos.Text

/-!
# One exact value for execution and proof

Hex computes the candidate. Its interpretation theorem identifies that same
candidate with Mathlib's square root. A generic acceptance certificate is
instantiated at `Scalar`, without kernel evaluation of Hex's root algorithm.
-/

namespace LeanOrigamiTests.TextScalar
open LeanOrigami
open Hex.AlgebraicNumber

private theorem squareRoot_value : (2 : Hex.AlgebraicNumber).sqrt.toComplex =
    (Real.sqrt 2 : ℂ) := by
  rw [sqrt_toComplex]
  simp only [ofNat_toComplex]
  rw [Complex.sqrt_of_nonneg (by norm_num [Complex.nonneg_iff])]
  norm_num

/-- This definition is executable: the proof of realness erases at runtime. -/
def squareRoot : Scalar := ⟨(2 : Hex.AlgebraicNumber).sqrt, by
  change (2 : Hex.AlgebraicNumber).sqrt.isReal = true
  rw [Hex.AlgebraicNumber.isReal_iff, squareRoot_value]
  rfl⟩

/-- The exact saved candidate denotes the specified Mathlib real number. -/
theorem squareRoot_toReal : Scalar.toReal squareRoot = Real.sqrt 2 := by
  change (2 : Hex.AlgebraicNumber).sqrt.toComplex.re = _
  rw [squareRoot_value]
  rfl

private theorem squareRoot_squared : squareRoot^2 = 2 := by
  apply Scalar.toReal_injective
  change Scalar.realHom (squareRoot^2) = Scalar.realHom 2
  rw [map_pow, map_ofNat]
  change (Scalar.toReal squareRoot)^2 = 2
  rw [squareRoot_toReal]
  norm_num

private theorem squareRoot_positive : 0 < squareRoot := by
  rw [← Scalar.toReal_lt, Scalar.toReal_zero, squareRoot_toReal]
  positivity

/-- The certificate is about the actual executable scalar program. -/
theorem saved_accepts :
    let saved := (LeanOrigamiDemos.RootPrograms.squareRootTwo Scalar squareRoot).getD ([], ⟨0⟩)
    Program.accepts saved.1 saved.2 .x squareRoot = true :=
  LeanOrigamiDemos.Text.sqrtAcceptance squareRoot squareRoot_squared squareRoot_positive

/-- Real interpretation happens only in the soundness theorem, after acceptance. -/
theorem submitted : ConstructibleNumber (Real.sqrt 2) := by
  have h := Program.accepts_sound Scalar.realHom _ _ .x _ saved_accepts
  change ConstructibleNumber (Scalar.toReal squareRoot) at h
  rwa [squareRoot_toReal] at h

#print axioms saved_accepts
#print axioms submitted

end LeanOrigamiTests.TextScalar
