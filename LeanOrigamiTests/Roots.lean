import LeanOrigami.Scalar.Roots

/-!
# Real-root interface examples

These proofs use the solver's general correctness theorem, not evaluation of
Hex's root search inside the kernel. Executable coverage is in Interpreter.
-/

namespace LeanOrigamiTests.Roots
open LeanOrigami LeanOrigami.Scalar

-- Zero polynomials retain their special meaning, including trailing zeros.
example : realRoots (polynomial [0, 0, 0]) = .all := by
  rw [realRoots_all_iff]
  simp [polynomial_toPolynomial]

-- A nonzero constant and a positive quadratic have no real roots.
example (x : ℝ) : ¬(realRoots (polynomial [1])).Contains x := by
  simp [contains_realRoots_polynomial]
example (x : ℝ) : ¬(realRoots (polynomial [1, 0, 1])).Contains x := by
  simp only [contains_realRoots_polynomial, List.foldr_cons, List.foldr_nil,
    toReal_zero, toReal_one, mul_zero, add_zero, zero_add]
  nlinarith [sq_nonneg x]

-- Trailing zero coefficients do not turn a linear equation into a quadratic.
example (a : Scalar) :
    (realRoots (polynomial [a, 1, 0])).Contains (-toReal a) := by
  simp [contains_realRoots_polynomial]

-- Arbitrary real algebraic coefficients are supported, including irrationals.
example (a : Scalar) (ha : 0 ≤ toReal a) :
    (realRoots (polynomial [-a, 0, 1])).Contains (Real.sqrt (toReal a)) := by
  have hneg : toReal (-a) = -toReal a := map_neg realHom a
  simp only [contains_realRoots_polynomial, List.foldr_cons, List.foldr_nil,
    toReal_zero, toReal_one, hneg, mul_zero, add_zero, zero_add]
  nlinarith [Real.sq_sqrt ha]

-- A double root has one value, and finite results contain no duplicate values.
example (a : Scalar) (x : ℝ) :
    (realRoots (polynomial [a*a, -(a+a), 1])).Contains x ↔ x = toReal a := by
  have hneg : toReal (-(a+a)) = -(toReal a + toReal a) := by
    rw [show toReal (-(a+a)) = -toReal (a+a) from map_neg realHom (a+a), toReal_add]
  simp only [contains_realRoots_polynomial, List.foldr_cons, List.foldr_nil,
    toReal_mul, toReal_one, hneg, mul_zero, add_zero]
  constructor
  · intro h; nlinarith [sq_nonneg (x-toReal a)]
  · intro h; rw [h]; ring

example (p : Hex.AlgebraicPoly) (values : List Scalar)
    (h : realRoots p = .finite values) : values.Nodup := realRoots_nodup p values h

#print axioms contains_realRoots
#print axioms contains_realRoots_polynomial
#print axioms realRoots_all_iff
#print axioms realRoots_nodup

end LeanOrigamiTests.Roots
