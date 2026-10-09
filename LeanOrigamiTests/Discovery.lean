import LeanOrigami.Scalar.FoldDiscovery

/-!
# Discovery specifications and trust audit

These examples explain how a caller interprets empty, infinite, and nonempty
results. Native tests of concrete Hex choice lists are in `Interpreter.lean`;
no native result is used as a premise in these proofs.
-/

namespace LeanOrigamiTests.Discovery
open LeanOrigami

-- An empty list excludes every REAL crease, not just algebraic candidates.
example (input : FoldInput Scalar) (h : Scalar.folds input = some []) :
    ∀ crease : Line ℝ, ¬(input.map Scalar.realHom).Satisfies crease := by
  intro crease hc
  obtain ⟨candidate, hm, _⟩ := Scalar.folds_complete input [] h crease hc
  exact List.not_mem_nil hm

-- A missing list is an infinite family, not failure to isolate real roots.
example (input : FoldInput Scalar) (h : Scalar.folds input = none) :
    (input.map Scalar.realHom).solutions.Infinite :=
  (Scalar.folds_none_iff input).mp h

-- A chosen item has both the requested geometry and finite-choice legality.
example (input : FoldInput Scalar) (choices : List (Line Scalar))
    (h : Scalar.folds input = some choices) (crease : Line Scalar) (hc : crease ∈ choices) :
    (input.map Scalar.realHom).Legal (crease.map Scalar.realHom) :=
  Scalar.folds_sound input choices h crease hc

#print axioms Scalar.rootList_complete
#print axioms Scalar.crease_representable
#print axioms Scalar.folds_spec
#print axioms Scalar.folds_none_iff
#print axioms Scalar.folds_nodup

end LeanOrigamiTests.Discovery
