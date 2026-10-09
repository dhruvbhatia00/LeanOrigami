import LeanOrigami.Solvers.Candidates
import LeanOrigami.Construction.Program

/-!
# Certified primitive execution

Check a selected crease against the geometric equations and prove real
finite-choice legality. Finding candidates is separate from replay: a program
already contains its chosen exact crease. Certificates have no runtime role.
-/

namespace LeanOrigami
namespace Solver
universe u
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Proof-only result, in the same universe as the construction state. -/
structure FoldCertificate (input : FoldInput K) (selected : Line K) : Type u where
  legal : ∀ f : K →+* ℝ, (input.map f).Legal (selected.map f)

/-- Check a saved crease without rerunning root discovery. The real embeddings
occur only in the erased certificate, never in executable arguments. -/
def fold (input : FoldInput K) (selected : Line K) :
    Except ConstructionError (FoldCertificate input selected) :=
  if hf : input.FiniteCondition then
    if hs : input.Satisfies selected then
      .ok ⟨by
        intro f
        exact ⟨(FoldInput.finiteCondition_iff _).mp
            ((FoldInput.finiteCondition_map_iff f input).mpr hf),
          (FoldInput.satisfies_map_iff f input selected).mpr hs⟩⟩
    else .error (match input with
      | .axiom5 p q _ => if p = q then .noFoldSolutions else .incorrectOutput
      | .axiom7 _ l m =>
          if l.perpendicularAlignmentDot m = 0 then .noFoldSolutions else .incorrectOutput
      | _ => .incorrectOutput)
  else .error (match input with
    | .axiom1 .. | .axiom2 .. => .coincidentPoints
    | _ => .underconstrainedFold)

/-- Replay accepts exactly the finite, geometrically valid selected creases.
This specification is independent of the root finder and its enumeration order. -/
theorem fold_succeeds_iff (input : FoldInput K) (selected : Line K) :
    (∃ certificate, fold input selected = .ok certificate) ↔
      input.FiniteCondition ∧ input.Satisfies selected := by
  unfold fold
  split
  · rename_i hf
    split
    · rename_i hs
      exact ⟨fun _ => ⟨hf, hs⟩, fun _ => ⟨_, rfl⟩⟩
    · rename_i hs
      constructor
      · rintro ⟨certificate, h⟩; cases h
      · rintro ⟨_, hc⟩; exact False.elim (hs hc)
  · rename_i hf
    constructor
    · rintro ⟨certificate, h⟩; cases h
    · rintro ⟨hc, _⟩; exact False.elim (hf hc)

/-- A nonzero determinant computes a point with unique-intersection evidence. -/
def intersect (l m : Line K) :
    Except ConstructionError
      {p : Point K // ∀ f : K →+* ℝ, LegalIntersection (l.map f) (m.map f) (f p.1, f p.2)} :=
  if h : l.determinant m ≠ 0 then
    .ok ⟨l.intersection m h, by
      intro f
      have hd : (l.map f).determinant (m.map f) ≠ 0 := by
        change f l.a * f m.b - f m.a * f l.b ≠ 0
        rw [← map_mul, ← map_mul, ← map_sub, ← map_zero f]
        exact fun hz => h (f.injective hz)
      have hl := (Line.contains_map f _ _).mpr (l.intersection_mem m h).1
      have hm := (Line.contains_map f _ _).mpr (l.intersection_mem m h).2
      refine ⟨hl, hm, ?_⟩
      intro q hql hqm
      exact ((l.map f).intersection_unique (m.map f) hd q hql hqm).trans
        ((l.map f).intersection_unique (m.map f) hd _ hl hm).symm⟩
  else if l = m then .error .coincidentLines else .error .parallelLines

end Solver
end LeanOrigami
