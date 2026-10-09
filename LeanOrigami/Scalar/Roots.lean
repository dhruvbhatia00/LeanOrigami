import LeanOrigami.Scalar
import HexNumberFieldMathlib.AlgebraicRoots
import HexNumberFieldMathlib.Polynomial

/-!
# Exact real roots

Hex isolates all complex roots. This module retains precisely its real roots
as executable `Scalar` values. The zero polynomial has a separate result;
an empty finite list means that there are no real roots. Interpretation in
Mathlib occurs only in specifications and proofs.
-/

namespace LeanOrigami.Scalar

/-- Build a polynomial from real coefficients in increasing degree order.
Hex removes trailing zeros, so the array's size does not promise a degree. -/
def polynomial (coefficients : List Scalar) : Hex.AlgebraicPoly :=
  Hex.AlgebraicPoly.ofArray (coefficients.map Subtype.val).toArray

/-- The coefficient-array interface has the usual Horner interpretation. -/
theorem polynomial_toPolynomial (coefficients : List Scalar) :
    (polynomial coefficients).toPolynomial =
      coefficients.foldr (fun a p => Polynomial.C (a.val.toComplex) + Polynomial.X * p) 0 := by
  simp only [polynomial, Hex.AlgebraicPoly.toPolynomial_ofArray,
    ← Array.foldr_toList, List.foldr_map]

/-- Evaluating real coefficient arrays agrees with real Horner evaluation. -/
theorem eval_polynomial (coefficients : List Scalar) (x : ℝ) :
    (polynomial coefficients).toPolynomial.eval (x : ℂ) =
      (coefficients.foldr (fun a value => toReal a + x * value) 0 : ℝ) := by
  induction coefficients with
  | nil => simp [polynomial_toPolynomial]
  | cons a coefficients ih =>
    have ha : a.val.toComplex = (toReal a : ℂ) := Complex.ext rfl (by simp)
    simp only [polynomial_toPolynomial, List.foldr_cons, Polynomial.eval_add,
      Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X,
      ha, Complex.ofReal_add, Complex.ofReal_mul] at ih ⊢
    rw [ih]

/-- Convert an algebraic number exactly when its imaginary part is zero. -/
def ofAlgebraic? (a : Hex.AlgebraicNumber) : Option Scalar :=
  if h : a.isReal = true then some ⟨a, h⟩ else none

/-- Exact conversion preserves the represented algebraic number. -/
@[simp] theorem ofAlgebraic?_eq_some (a : Hex.AlgebraicNumber) (r : Scalar) :
    ofAlgebraic? a = some r ↔ a = r.val := by
  unfold ofAlgebraic?
  split
  · simp only [Option.some.injEq, Subtype.ext_iff]
  · rename_i h
    constructor
    · intro hn; cases hn
    · intro ha
      exact False.elim (h (ha ▸ r.property))

/-- Real roots, with the identically zero equation kept distinct. -/
inductive RealRoots where
  | all
  | finite (values : List Scalar)

/-- Membership describes real numbers, including numbers not supplied as scalars. -/
def RealRoots.Contains : RealRoots → ℝ → Prop
  | .all, _ => True
  | .finite values, x => ∃ r ∈ values, toReal r = x

/-- Filter a complete complex root set, forgetting multiplicities. -/
def RealRoots.ofComplex : Hex.RootSet → RealRoots
  | .all => .all
  | .finite entries => .finite
      ((entries.toList.filterMap fun entry => ofAlgebraic? entry.root.exact).dedup)

/-- Filtering loses exactly the nonreal roots and no real roots. -/
theorem RealRoots.contains_ofComplex (roots : Hex.RootSet) (x : ℝ) :
    (ofComplex roots).Contains x ↔ roots.Contains (x : ℂ) := by
  cases roots with
  | all => rfl
  | finite entries =>
    simp only [ofComplex, Contains, Hex.RootSet.Contains, List.mem_dedup,
      List.mem_filterMap]
    constructor
    · rintro ⟨r, ⟨entry, he, hr⟩, hx⟩
      refine ⟨entry, he, ?_⟩
      have hv := (ofAlgebraic?_eq_some _ _).mp hr
      rw [← Hex.AlgebraicRoot.exact_toComplex, hv]
      exact Complex.ext hx (by simp)
    · rintro ⟨entry, he, hx⟩
      have hreal : entry.root.exact.isReal = true := by
        rw [Hex.AlgebraicNumber.isReal_iff, Hex.AlgebraicRoot.exact_toComplex, hx]
        rfl
      let r : Scalar := ⟨entry.root.exact, hreal⟩
      refine ⟨r, ⟨entry, he, ?_⟩, ?_⟩
      · apply (ofAlgebraic?_eq_some entry.root.exact r).mpr
        with_reducible rfl
      · simp only [toReal, r, Hex.AlgebraicRoot.exact_toComplex, hx, Complex.ofReal_re]

/-- Enumerate the distinct real roots of an exact algebraic polynomial. -/
def realRoots (p : Hex.AlgebraicPoly) : RealRoots :=
  RealRoots.ofComplex p.roots

/-- Soundness and completeness, including arbitrary Mathlib real roots. -/
theorem contains_realRoots (p : Hex.AlgebraicPoly) (x : ℝ) :
    (realRoots p).Contains x ↔ p.toPolynomial.eval (x : ℂ) = 0 := by
  rw [realRoots, RealRoots.contains_ofComplex, Hex.AlgebraicPoly.contains_roots_iff]

/-- Root membership directly in terms of the supplied real coefficients. -/
theorem contains_realRoots_polynomial (coefficients : List Scalar) (x : ℝ) :
    (realRoots (polynomial coefficients)).Contains x ↔
      coefficients.foldr (fun a value => toReal a + x * value) 0 = 0 := by
  rw [contains_realRoots, eval_polynomial, Complex.ofReal_eq_zero]

/-- Only the zero polynomial is classified as having every real root. -/
theorem realRoots_all_iff (p : Hex.AlgebraicPoly) :
    realRoots p = .all ↔ p.toPolynomial = 0 := by
  rw [← Hex.AlgebraicPoly.roots_all_iff]
  unfold realRoots RealRoots.ofComplex
  cases p.roots <;> simp

/-- A repeated root appears only once in the list offered to a caller. -/
theorem realRoots_nodup (p : Hex.AlgebraicPoly) (values : List Scalar)
    (h : realRoots p = .finite values) : values.Nodup := by
  unfold realRoots RealRoots.ofComplex at h
  cases hr : p.roots with
  | all => simp only [hr] at h; cases h
  | finite entries =>
    simp only [hr, RealRoots.finite.injEq] at h
    subst values
    exact List.nodup_dedup _

end LeanOrigami.Scalar
