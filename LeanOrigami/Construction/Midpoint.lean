import LeanOrigami.Construction.Composition

/-!
# A reusable midpoint theorem

The existing visual recipe joins two distinct points, folds their perpendicular
bisector, and intersects the two creases. Its public interface returns just the
midpoint. The two-fold/intersection argument is proved once; calls use `rule` instead of
replaying the internal construction. Coincident inputs remain outside the
advertised domain of this recipe.
-/

namespace LeanOrigami.Midpoint

/-- The public output of the midpoint recipe. -/
def point {K : Type*} [Field K] (p q : Point K) : Point K :=
  ((p.1 + q.1) / 2, (p.2 + q.2) / 2)

/-- The coordinate formula is preserved under interpretation in another field. -/
theorem point_map {K L : Type*} [Field K] [Field L] (f : K →+* L) (p q : Point K) :
    (f (point p q).1, f (point p q).2) = point (f p.1, f p.2) (f q.1, f q.2) := by
  simp only [point, map_div₀, map_add, map_ofNat]

/-- Joining and bisecting the inputs has precisely their midpoint in common. -/
theorem legalIntersection (p q : Point ℝ) (distinct : p ≠ q) :
    LegalIntersection (Line.through p q distinct) (Line.bisector p q distinct) (point p q) := by
  have norm : (q.1-p.1)^2 + (q.2-p.2)^2 ≠ 0 := by
    intro zero
    have hx : q.1 = p.1 := by nlinarith [sq_nonneg (q.2-p.2)]
    have hy : q.2 = p.2 := by nlinarith [sq_nonneg (q.1-p.1)]
    exact distinct (Prod.ext hx.symm hy.symm)
  refine ⟨?_, ?_, ?_⟩
  · simp only [Line.through, Line.contains_normalize, point]
    ring
  · rw [Line.contains_bisector]
    simp only [Line.distanceSq, point]
    ring
  · intro r through bisector
    rw [Line.through, Line.contains_normalize] at through
    rw [Line.bisector, Line.contains_normalize] at bisector
    apply Prod.ext
    · apply mul_left_cancel₀ norm
      dsimp [point]
      linear_combination (q.1-p.1)*bisector + (q.2-p.2)*through
    · apply mul_left_cancel₀ norm
      dsimp [point]
      linear_combination (q.2-p.2)*bisector - (q.1-p.1)*through

/-- The output is constructed by the existing A1/A2/intersection recipe.
This theorem is opaque to later calls: its internal proof is not replayed. -/
theorem constructible (p q : Point ℝ) (distinct : p ≠ q)
    (first : Constructible (.point p)) (second : Constructible (.point q)) :
    Constructible (.point (point p q)) := by
  have inputs (input : FoldInput ℝ) (h : input = .axiom1 p q ∨ input = .axiom2 p q) :
      input.Available Constructible := by
    rcases h with rfl | rfl <;>
      simpa [FoldInput.Available, FoldInput.objects] using And.intro first second
  have join : Constructible (.line (Line.through p q distinct)) :=
    .fold (.axiom1 p q) _ (inputs _ (Or.inl rfl))
      ⟨(FoldInput.axiom1_admissible_iff p q).mpr distinct,
        Line.through_left p q distinct, Line.through_right p q distinct⟩
  have bisector : Constructible (.line (Line.bisector p q distinct)) :=
    .fold (.axiom2 p q) _ (inputs _ (Or.inr rfl))
      ⟨(FoldInput.axiom2_admissible_iff p q).mpr distinct, Line.bisector_reflect p q distinct⟩
  exact .intersection _ _ _ join bisector (legalIntersection p q distinct)

/-- Input/output relation for the whole public output collection. Distinctness
is part of the relation, not merely an editor check. -/
def Produces {K : Type*} [Field K] (inputs outputs : Program.State K) : Prop :=
  ∃ p q : Point K, inputs = [.point p, .point q] ∧ p ≠ q ∧ outputs = [.point (point p q)]

/-- The same rule works over exact scalars or rational test coordinates. -/
def rule (K : Type*) [Field K] : Composition.RecipeRule K where
  Produces := Produces
  sound f inputs outputs produced available := by
    obtain ⟨p, q, rfl, distinct, rfl⟩ := produced
    intro object member
    have equal := List.mem_singleton.mp member
    subst object
    have first := available (.point p) (by simp)
    have second := available (.point q) (by simp)
    have mappedDistinct : (f p.1, f p.2) ≠ (f q.1, f q.2) := by
      intro equal
      exact distinct (Prod.ext (f.injective (congrArg Prod.fst equal))
        (f.injective (congrArg Prod.snd equal)))
    simpa only [Object.map, point_map] using constructible
      (f p.1, f p.2) (f q.1, f q.2) mappedDistinct first second

end LeanOrigami.Midpoint
