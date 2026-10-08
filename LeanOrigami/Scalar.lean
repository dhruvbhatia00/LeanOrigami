import HexNumberFieldMathlib.Order
import Mathlib.Algebra.Field.Subfield.Defs

/-!
# Exact real scalars

Coordinates use the real subfield of Hex's executable algebraic numbers.
The map to `ℝ` is for proofs only; arithmetic and comparisons use Hex.
Being a scalar does not assert origami constructibility.
-/

namespace LeanOrigami
open Hex

/-- The real values in Hex's algebraic field, recognized by its exact test. -/
def realSubfield : Subfield AlgebraicNumber where
  carrier := {a | a.isReal = true}
  zero_mem' := by simp only [Set.mem_ofPred_eq, AlgebraicNumber.isReal_iff]; simp
  one_mem' := by simp only [Set.mem_ofPred_eq, AlgebraicNumber.isReal_iff]; simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, AlgebraicNumber.isReal_iff] at *
    simp [AlgebraicNumber.add_toComplex, ha, hb]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, AlgebraicNumber.isReal_iff] at *
    simp [AlgebraicNumber.neg_toComplex, ha]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, AlgebraicNumber.isReal_iff] at *
    simp [AlgebraicNumber.mul_toComplex, ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, AlgebraicNumber.isReal_iff] at *
    simp [AlgebraicNumber.inv_toComplex, Complex.inv_im, ha]

/-- Exact real algebraic coordinates, with executable field operations. -/
abbrev Scalar := ↥realSubfield

namespace Scalar

/-- Every scalar's complex interpretation has zero imaginary part. -/
@[simp] theorem im_eq_zero (a : Scalar) : a.val.toComplex.im = 0 :=
  (AlgebraicNumber.isReal_iff _).mp a.property

/-- Interpretation in Mathlib's real numbers; not used for computation. -/
noncomputable def toReal (a : Scalar) : ℝ := a.val.toComplex.re

/-- Real interpretation loses no information. -/
theorem toReal_injective : Function.Injective toReal := by
  intro a b h
  apply Subtype.ext
  apply AlgebraicNumber.toComplex_injective
  exact Complex.ext h (by simp)

@[simp] theorem toReal_zero : toReal 0 = 0 := by
  change (0 : AlgebraicNumber).toComplex.re = 0
  simp

@[simp] theorem toReal_one : toReal 1 = 1 := by
  change (1 : AlgebraicNumber).toComplex.re = 1
  simp

@[simp] theorem toReal_add (a b : Scalar) : toReal (a + b) = toReal a + toReal b := by
  change (a.val + b.val).toComplex.re = _
  simp [AlgebraicNumber.add_toComplex, toReal]

@[simp] theorem toReal_mul (a b : Scalar) : toReal (a * b) = toReal a * toReal b := by
  change (a.val * b.val).toComplex.re = _
  simp [AlgebraicNumber.mul_toComplex, toReal]

/-- The field embedding supplies preservation of subtraction, division and casts. -/
noncomputable def realHom : Scalar →+* ℝ where
  toFun := toReal
  map_zero' := toReal_zero
  map_one' := toReal_one
  map_add' := toReal_add
  map_mul' := toReal_mul

/-- Hex's executable comparison agrees with real comparison. -/
@[simp] theorem toReal_le (a b : Scalar) : toReal a ≤ toReal b ↔ a ≤ b := by
  change _ ↔ a.val ≤ b.val
  rw [AlgebraicNumber.le_iff]
  simp [toReal]

@[simp] theorem toReal_lt (a b : Scalar) : toReal a < toReal b ↔ a < b := by
  change _ ↔ a.val < b.val
  rw [AlgebraicNumber.lt_iff]
  simp [toReal]

instance : LinearOrder Scalar where
  toPartialOrder := inferInstanceAs (PartialOrder ↥realSubfield)
  le_total a b := by
    simpa only [← toReal_le] using le_total (toReal a) (toReal b)
  toDecidableLE := fun a b => inferInstanceAs (Decidable (a.val ≤ b.val))
  toDecidableLT := fun a b => inferInstanceAs (Decidable (a.val < b.val))
  toDecidableEq := inferInstanceAs (DecidableEq realSubfield)

instance : IsStrictOrderedRing Scalar :=
  Function.Injective.isStrictOrderedRing toReal toReal_zero toReal_one
    toReal_add toReal_mul (fun {_ _} => toReal_le _ _) (fun {_ _} => toReal_lt _ _)

end Scalar
end LeanOrigami
