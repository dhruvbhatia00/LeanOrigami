import LeanOrigami.Geometry.Reflection
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Data.Set.Finite.Basic

/-!
# The seven fold relations and finite-choice legality

`FoldInput` records a requested operation and its geometric inputs. Its
`Satisfies` relation describes a crease, without running a solver. Legal
choices are defined over all real creases, so a finite list of candidates
cannot make an underconstrained operation legal.
-/

namespace LeanOrigami

/-- Inputs to one Huzita–Hatori operation. Constructor arguments name their roles. -/
inductive FoldInput (K : Type*) [Zero K] [One K] where
  | axiom1 (first second : Point K)
  | axiom2 (source target : Point K)
  | axiom3 (source target : Line K)
  | axiom4 (point : Point K) (perpendicularTo : Line K)
  | axiom5 (source fixedPoint : Point K) (target : Line K)
  | axiom6 (first second : Point K) (firstTarget secondTarget : Line K)
  | axiom7 (source : Point K) (target perpendicularTo : Line K)

namespace FoldInput
variable {K : Type*} [Field K]

/-- The geometric meaning of each rule, without admissibility restrictions.
In rule 3, the biconditional quantifies over the whole source line and plane. -/
def Satisfies (input : FoldInput K) (crease : Line K) : Prop :=
  match input with
  | .axiom1 p q => crease.Contains p ∧ crease.Contains q
  | .axiom2 p q => crease.reflect p = q
  | .axiom3 l m => ∀ p, l.Contains p ↔ m.Contains (crease.reflect p)
  | .axiom4 p l => crease.Contains p ∧ crease.Perpendicular l
  | .axiom5 p q l => l.Contains (crease.reflect p) ∧ crease.Contains q
  | .axiom6 p q l m => l.Contains (crease.reflect p) ∧ m.Contains (crease.reflect q)
  | .axiom7 p l m => l.Contains (crease.reflect p) ∧ crease.Perpendicular m

/-- Transport input objects through a field embedding. -/
def map {L : Type*} [Field L] (f : K →+* L) : FoldInput K → FoldInput L
  | .axiom1 p q => .axiom1 (Prod.map f f p) (Prod.map f f q)
  | .axiom2 p q => .axiom2 (Prod.map f f p) (Prod.map f f q)
  | .axiom3 l m => .axiom3 (l.map f) (m.map f)
  | .axiom4 p l => .axiom4 (Prod.map f f p) (l.map f)
  | .axiom5 p q l => .axiom5 (Prod.map f f p) (Prod.map f f q) (l.map f)
  | .axiom6 p q l m => .axiom6 (Prod.map f f p) (Prod.map f f q) (l.map f) (m.map f)
  | .axiom7 p l m => .axiom7 (Prod.map f f p) (l.map f) (m.map f)

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- Rule 3 means equality of the reflected source set with the target set. -/
theorem axiom3_iff_image (l m crease : Line K) :
    (axiom3 l m).Satisfies crease ↔
      crease.reflect '' {p | l.Contains p} = {p | m.Contains p} := by
  constructor
  · intro h
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact (h q).mp hq
    · intro hp
      refine ⟨crease.reflect p, ?_, crease.reflect_reflect p⟩
      exact (h (crease.reflect p)).mpr (by simpa using hp)
  · intro h p
    constructor
    · intro hp
      have hm : crease.reflect p ∈ crease.reflect '' {p | l.Contains p} := ⟨p, hp, rfl⟩
      rwa [h] at hm
    · intro hp
      have hm : crease.reflect p ∈ crease.reflect '' {p | l.Contains p} := by
        rw [h]; exact hp
      obtain ⟨q, hq, heq⟩ := hm
      exact crease.reflect_injective heq ▸ hq

/-- All real crease solutions, including those outside any computed candidate list. -/
def solutions (input : FoldInput ℝ) : Set (Line ℝ) := {crease | input.Satisfies crease}

/-- Finitely many real choices. An empty solution set is admissible but offers no selection. -/
def Admissible (input : FoldInput ℝ) : Prop := input.solutions.Finite

/-- A permitted selection both has finite-choice inputs and satisfies the fold relation. -/
def Legal (input : FoldInput ℝ) (crease : Line ℝ) : Prop :=
  input.Admissible ∧ input.Satisfies crease

/-- An explicit infinite family of distinct real lines through any point. -/
theorem infinite_lines_through (p : Point ℝ) : {l : Line ℝ | l.Contains p}.Infinite := by
  let family : ℝ → Line ℝ := fun t => ⟨1, t, p.1+t*p.2, Or.inl rfl⟩
  have hinj : Function.Injective family := by
    intro t u h
    exact congrArg Line.b h
  apply (Set.infinite_range_of_injective hinj).mono
  rintro l ⟨t, rfl⟩
  simp [family, Line.Contains]

/-- Repeating a point in rule 1 leaves infinitely many choices. -/
theorem axiom1_same_not_admissible (p : Point ℝ) : ¬ (axiom1 p p).Admissible := by
  simpa [Admissible, solutions, Satisfies] using infinite_lines_through p

/-- The same degeneracy occurs when rule 2 asks to leave a point fixed. -/
theorem axiom2_same_not_admissible (p : Point ℝ) : ¬ (axiom2 p p).Admissible := by
  simpa [Admissible, solutions, Satisfies, Line.reflect_eq_self] using infinite_lines_through p

/-- Distinct points give exactly one rule-1 crease. -/
theorem axiom1_solutions (p q : Point ℝ) (h : p ≠ q) :
    (axiom1 p q).solutions = {Line.through p q h} := by
  ext l
  constructor
  · intro hl
    exact Line.through_unique p q h l hl.1 hl.2
  · intro hl
    have heq : l = Line.through p q h := hl
    subst l
    exact ⟨Line.through_left p q h, Line.through_right p q h⟩

/-- Rule 1 is finite-choice exactly for distinct input points. -/
theorem axiom1_admissible_iff (p q : Point ℝ) : (axiom1 p q).Admissible ↔ p ≠ q := by
  constructor
  · intro h heq
    subst q
    exact axiom1_same_not_admissible p h
  · intro h
    unfold Admissible
    rw [axiom1_solutions p q h]
    exact Set.finite_singleton _

/-- A satisfying crease is still forbidden when its inputs are underconstrained. -/
theorem not_legal_of_not_admissible {input : FoldInput ℝ} (h : ¬ input.Admissible)
    (crease : Line ℝ) : ¬ input.Legal crease := fun hc => h hc.1

end FoldInput

/-- A selected intersection point must be the unique common point.
The executable determinant guard is a witness to this geometric condition. -/
def LegalIntersection (l m : Line ℝ) (p : Point ℝ) : Prop :=
  l.Contains p ∧ m.Contains p ∧ ∀ q, l.Contains q → m.Contains q → q = p

/-- A nonzero determinant produces a legal intersection. -/
theorem legalIntersection_of_determinant (l m : Line ℝ) (h : l.determinant m ≠ 0) :
    LegalIntersection l m (l.intersection m h) :=
  ⟨(l.intersection_mem m h).1, (l.intersection_mem m h).2,
    l.intersection_unique m h⟩

/-- A valid line contains a point other than any specified point on it. -/
private theorem exists_other_point (l : Line ℝ) (p : Point ℝ) (hp : l.Contains p) :
    ∃ q, q ≠ p ∧ l.Contains q := by
  refine ⟨(p.1-l.b, p.2+l.a), ?_, ?_⟩
  · intro heq
    have hx := congrArg Prod.fst heq
    have hy := congrArg Prod.snd heq
    rcases l.normal_ne_zero with h | h
    · apply h; dsimp at hy; linarith
    · apply h; dsimp at hx; linarith
  · dsimp [Line.Contains] at *
    linear_combination hp

/-- Coincident lines never supply a legal unique intersection. -/
theorem not_legalIntersection_self (l : Line ℝ) (p : Point ℝ) :
    ¬ LegalIntersection l l p := by
  rintro ⟨hp, _, huniq⟩
  obtain ⟨q, hne, hq⟩ := exists_other_point l p hp
  exact hne (huniq q hq hq)

/-- The determinant guard exactly characterizes unique real intersections. -/
theorem legalIntersection_iff (l m : Line ℝ) (p : Point ℝ) :
    LegalIntersection l m p ↔
      ∃ h : l.determinant m ≠ 0, p = l.intersection m h := by
  constructor
  · rintro ⟨hl, hm, hu⟩
    have hd : l.determinant m ≠ 0 := by
      intro h
      have heq := l.eq_of_determinant_zero_of_mem m h p hl hm
      subst m
      exact not_legalIntersection_self l p ⟨hl, hm, hu⟩
    exact ⟨hd, l.intersection_unique m hd p hl hm⟩
  · rintro ⟨h, rfl⟩
    exact legalIntersection_of_determinant l m h

end LeanOrigami
