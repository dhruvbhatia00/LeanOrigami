import LeanOrigami.Solvers.Cubic

/-!
# Candidate generation from exact polynomial roots

The root finder is an argument so the geometry stays independent of Hex.
It receives coefficients in increasing degree order and returns distinct
real roots. A missing list means an infinite family, while `some []` means
no crease. Every generated candidate is checked against the original rule.
-/

namespace LeanOrigami
namespace FoldInput
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Exact finite-choice guard, including requests with no solutions. -/
def FiniteCondition : FoldInput K → Prop
  | .axiom1 p q | .axiom2 p q => p ≠ q
  | .axiom3 l m => l ≠ m
  | .axiom4 .. => True
  | .axiom5 p q l => p ≠ q ∨ ¬l.Contains p
  | .axiom6 p q l m => ¬axiom6FreeDirection p q l m ∧ ¬(axiom6Polynomial p q l m).IsZero
  | .axiom7 p l m => l.perpendicularAlignmentDot m ≠ 0 ∨ ¬l.Contains p

instance (input : FoldInput K) : Decidable input.FiniteCondition := by
  cases input <;> unfold FiniteCondition <;> infer_instance

/-- The executable guard describes finiteness of the whole real solution set. -/
theorem finiteCondition_iff (input : FoldInput ℝ) : input.FiniteCondition ↔ input.Admissible := by
  cases input with
  | axiom1 p q => exact (axiom1_admissible_iff p q).symm
  | axiom2 p q => exact (axiom2_admissible_iff p q).symm
  | axiom3 l m => exact (axiom3_admissible_iff l m).symm
  | axiom4 p l => exact ⟨fun _ => axiom4_admissible p l, fun _ => trivial⟩
  | axiom5 p q l => exact (axiom5_admissible_iff p q l).symm
  | axiom6 p q l m => exact (axiom6_admissible_iff p q l m).symm
  | axiom7 p l m => exact (axiom7_admissible_iff p l m).symm

/-- All finite-choice tests survive coordinate embeddings, without assuming
that an arbitrary embedding preserves the chosen order. -/
theorem finiteCondition_map_iff {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L]
    (f : K →+* L) (input : FoldInput K) :
    (input.map f).FiniteCondition ↔ input.FiniteCondition := by
  have hp (p q : Point K) : Prod.map f f p = Prod.map f f q ↔ p = q := by
    simp only [Prod.map, f.injective.eq_iff, Prod.ext_iff]
  cases input <;>
    simp only [map, FiniteCondition, ne_eq, hp, (Line.map_injective f).eq_iff,
      axiom6FreeDirection_map_iff, axiom6Polynomial_map, Univariate.Cubic.isZero_map_iff,
      Line.perpendicularAlignmentDot_map] <;>
    simp only [Prod.map, Line.contains_map, ← map_zero f, f.injective.eq_iff]

/-- Checking a crease commutes with interpretation, including whole-line rule 3. -/
theorem satisfies_map_iff {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L]
    (f : K →+* L) (input : FoldInput K) (crease : Line K) :
    (input.map f).Satisfies (crease.map f) ↔ input.Satisfies crease := by
  cases input with
  | axiom3 l m =>
      have h₀ := Line.pointAt_map f l 0
      have h₁ := Line.pointAt_map f l 1
      simp only [map_zero] at h₀
      simp only [map_one] at h₁
      simp only [map, axiom3_iff_two_points, h₀, h₁, Line.reflect_map, Line.contains_map]
  | _ =>
      simp only [map, Satisfies, Prod.map, Line.reflect_map, Line.contains_map,
        Line.perpendicular_map, f.injective.eq_iff, Prod.ext_iff]

/-- Polynomial roots generate possibilities; checking the original relation
removes roots introduced by elimination and handles zero denominators safely. -/
def rawCandidates (roots : List K → List K) : FoldInput K → List (Line K)
  | .axiom1 p q => if h : p ≠ q then [Line.through p q h] else []
  | .axiom2 p q => if h : p ≠ q then [Line.bisector p q h] else []
  | .axiom3 l m =>
      let p := l.pointAt 0
      (roots [l.directionCross m, -2*l.directionDifference m, -l.directionCross m]).map
        (fun t => Line.chart t (p.1+t*p.2-m.residual p*(1+t^2)/(2*m.chartDot t))) ++
      [Line.horizontal (p.2-m.residual p/(2*m.b))]
  | .axiom4 p l => [Line.perpendicularThrough p l]
  | .axiom5 p q l => if h : p ≠ q then
      (roots (l.circleCoefficients q (Line.distanceSq q p))).map
        (fun t => Line.landingCrease p q (l.pointAt t) h)
      else []
  | .axiom6 p q l m =>
      (roots (axiom6Polynomial p q l m).coefficients).map (axiom6ChartCandidate p q l m) ++
      [axiom6HorizontalCandidate p q l m]
  | .axiom7 p l m => if h : l.perpendicularAlignmentDot m ≠ 0 then
      [Line.alignPerpendicular p l m h] else []

/-- The root finder need only cover the particular polynomial used by this
request. Filtering does not require its proposed roots to be correct. -/
def RootsCover (roots : List K → List K) : FoldInput K → Prop
  | .axiom3 l m => ∀ t,
      l.directionCross m*(1-t^2)-2*l.directionDifference m*t = 0 →
      t ∈ roots [l.directionCross m, -2*l.directionDifference m, -l.directionCross m]
  | .axiom5 p q l => ∀ t,
      Line.distanceSq q (l.pointAt t) = Line.distanceSq q p →
      t ∈ roots (l.circleCoefficients q (Line.distanceSq q p))
  | .axiom6 p q l m => ∀ t, (axiom6Polynomial p q l m).eval t = 0 →
      t ∈ roots (axiom6Polynomial p q l m).coefficients
  | _ => True

/-- Before filtering, the formulas include every valid finite-choice crease
whenever the root finder covers the request's polynomial. -/
theorem rawCandidates_complete (roots : List K → List K) (input : FoldInput K)
    (hf : input.FiniteCondition) (hr : input.RootsCover roots) (crease : Line K)
    (hc : input.Satisfies crease) : crease ∈ input.rawCandidates roots := by
  cases input with
  | axiom1 p q =>
      change p ≠ q at hf
      have he := Line.through_unique p q hf crease hc.1 hc.2
      simp [rawCandidates, hf, he]
  | axiom2 p q =>
      change p ≠ q at hf
      have he := Line.bisector_unique p q hf crease hc
      simp [rawCandidates, hf, he]
  | axiom3 l m =>
      simp only [rawCandidates]
      rcases crease.chart_cases with he | he
      · apply List.mem_append_left
        apply List.mem_map.mpr
        refine ⟨crease.b, hr crease.b ?_, ?_⟩
        · simpa [Line.chart] using axiom3_direction l m (Line.chart crease.b crease.c) (he ▸ hc)
        · exact (he.trans (congrArg (Line.chart crease.b)
            (axiom3_chart_offset l m _ _ hf (he ▸ hc)))).symm
      · apply List.mem_append_right
        exact List.mem_singleton.mpr
          (he.trans (congrArg Line.horizontal (axiom3_horizontal_offset l m _ hf (he ▸ hc))))
  | axiom4 p l =>
      simpa only [rawCandidates, List.mem_singleton] using
        Line.perpendicularThrough_unique p l crease hc.1 hc.2
  | axiom5 p q l =>
      have hn : p ≠ q := by
        intro he
        subst q
        have hp := hf.resolve_left (not_not_intro rfl)
        exact hp (by simpa only [(crease.reflect_eq_self p).mpr hc.2] using hc.1)
      obtain ⟨landing, hl, hd, he⟩ := (axiom5_iff_landing p q l crease hn).mp hc
      obtain ⟨t, ht⟩ := l.exists_pointAt landing hl
      simp only [rawCandidates, dite_eq_left hn, List.mem_map]
      exact ⟨t, hr t (by rw [ht]; exact hd.symm), by rw [ht, he]⟩
  | axiom6 p q l m =>
      simp only [rawCandidates]
      rcases crease.chart_cases with he | he
      · apply List.mem_append_left
        exact List.mem_map.mpr ⟨crease.b, hr crease.b (by
          rw [axiom6Polynomial_eval]
          exact axiom6_eliminant_zero p q l m _ _ (he ▸ hc)),
          (he.trans (axiom6_chart_eq_candidate p q l m _ _ hf.1 (he ▸ hc))).symm⟩
      · apply List.mem_append_right
        exact List.mem_singleton.mpr
          (he.trans (axiom6_horizontal_eq_candidate p q l m _ hf.1 (he ▸ hc)))
  | axiom7 p l m =>
      have hn : l.perpendicularAlignmentDot m ≠ 0 := by
        intro hz
        exact (hf.resolve_left (not_not_intro hz)) ((axiom7_zero_iff p l m crease hz).mp hc).1
      simp only [rawCandidates, dite_eq_left hn, List.mem_singleton]
      exact (axiom7_iff_candidate p l m crease hn).mp hc

/-- Discover distinct exact choices, separately reporting infinite families. -/
def candidates (roots : List K → List K) (input : FoldInput K) : Option (List (Line K)) :=
  if input.FiniteCondition then
    some (((input.rawCandidates roots).filter fun crease => decide (input.Satisfies crease)).dedup)
  else none

/-- No behavior of the root finder can make an invalid crease pass filtering. -/
theorem candidates_sound (roots : List K → List K) (input : FoldInput K)
    (choices : List (Line K)) (h : input.candidates roots = some choices)
    (crease : Line K) (hc : crease ∈ choices) : input.Satisfies crease := by
  unfold candidates at h
  split at h
  · cases Option.some.inj h
    simp only [List.mem_dedup, List.mem_filter, decide_eq_true_eq] at hc
    exact hc.2
  · cases h

/-- Filtering retains exactly the valid choices when root coverage holds. -/
theorem candidates_complete (roots : List K → List K) (input : FoldInput K)
    (hf : input.FiniteCondition) (hr : input.RootsCover roots) (crease : Line K)
    (hc : input.Satisfies crease) :
    ∃ choices, input.candidates roots = some choices ∧ crease ∈ choices := by
  refine ⟨((input.rawCandidates roots).filter fun c => decide (input.Satisfies c)).dedup, ?_, ?_⟩
  · simp only [candidates, ite_eq_left hf]
  · simp only [List.mem_dedup, List.mem_filter, decide_eq_true_eq]
    exact ⟨rawCandidates_complete roots input hf hr crease hc, hc⟩

/-- Infinite requests are reported separately from an empty finite list. -/
theorem candidates_eq_none_iff (roots : List K → List K) (input : FoldInput K) :
    input.candidates roots = none ↔ ¬input.FiniteCondition := by
  simp only [candidates]
  split <;> simp_all

/-- Repeated roots or coinciding formulas do not create extra GUI choices. -/
theorem candidates_nodup (roots : List K → List K) (input : FoldInput K)
    (choices : List (Line K)) (h : input.candidates roots = some choices) : choices.Nodup := by
  unfold candidates at h
  split at h
  · cases Option.some.inj h
    exact List.nodup_dedup _
  · cases h

end FoldInput
end LeanOrigami
