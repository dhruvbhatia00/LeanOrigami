import LeanOrigami.Solvers.Perpendicular
import LeanOrigami.Algebra.Cubic

/-!
# Rule 6: two point-to-line constraints

The direction equation has degree at most three. A common unconstrained
direction and an identically zero eliminant are separate infinite families.
Candidate reconstruction uses whichever alignment constrains the offset.
-/

namespace LeanOrigami
namespace FoldInput
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Coefficients of the rule-6 eliminant, including all degree drops. -/
def axiom6Polynomial (p q : Point K) (l m : Line K) : Univariate.Cubic K :=
  let dx := p.1-q.1
  let dy := p.2-q.2
  let s₀ := l.residual p*m.a-m.residual q*l.a
  let s₁ := l.residual p*m.b-m.residual q*l.b
  let u₀ := l.a*m.a
  let u₁ := l.a*m.b+l.b*m.a
  let u₂ := l.b*m.b
  ⟨2*dx*u₀-s₀, 2*dx*u₁+2*dy*u₀-s₁,
    2*dx*u₂+2*dy*u₁-s₀, 2*dy*u₂-s₁⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The coefficient representation is exactly the geometric elimination equation. -/
theorem axiom6Polynomial_eval (p q : Point K) (l m : Line K) (t : K) :
    (axiom6Polynomial p q l m).eval t = axiom6Eliminant p q l m t := by
  dsimp [axiom6Polynomial, Univariate.Cubic.eval, axiom6Eliminant, Line.chartDot]
  ring

/-- Parallel targets with both sources already on them admit every
perpendicular translate, regardless of the eliminant's coefficients. -/
def axiom6FreeDirection (p q : Point K) (l m : Line K) : Prop :=
  l.determinant m = 0 ∧ l.Contains p ∧ m.Contains q

instance (p q : Point K) (l m : Line K) : Decidable (axiom6FreeDirection p q l m) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Outside that exceptional case, at least one alignment constrains the offset. -/
theorem axiom6_dot_or_dot (p q : Point K) (l m crease : Line K)
    (hn : ¬axiom6FreeDirection p q l m) (h : (axiom6 p q l m).Satisfies crease) :
    l.a*crease.a+l.b*crease.b ≠ 0 ∨ m.a*crease.a+m.b*crease.b ≠ 0 := by
  by_contra hd
  push Not at hd
  have hl := ((axiom6_iff_equations p q l m crease).mp h).1
  have hm := ((axiom6_iff_equations p q l m crease).mp h).2
  simp only [Line.alignmentEquation, hd.1, hd.2, mul_zero, sub_zero, mul_eq_zero,
    crease.normalSq_ne_zero, or_false, Line.residual_eq_zero] at hl hm
  obtain ⟨ha, hb⟩ := Line.normal_eq_of_perpendicular l m crease hd.1 hd.2
  exact hn ⟨by simp [Line.determinant, ha, hb], hl, hm⟩

/-- Reconstruct a nonhorizontal candidate using a constraining target.
Extraneous roots are removed by checking the original fold relation. -/
def axiom6ChartCandidate (p q : Point K) (l m : Line K) (t : K) : Line K :=
  if l.chartDot t ≠ 0 then
    Line.chart t (p.1+t*p.2-l.residual p*(1+t^2)/(2*l.chartDot t))
  else Line.chart t (q.1+t*q.2-m.residual q*(1+t^2)/(2*m.chartDot t))

/-- Every valid nonhorizontal crease is reconstructed, including the direction
where the first target fails to constrain the offset. -/
theorem axiom6_chart_eq_candidate (p q : Point K) (l m : Line K) (t c : K)
    (hn : ¬axiom6FreeDirection p q l m)
    (h : (axiom6 p q l m).Satisfies (Line.chart t c)) :
    Line.chart t c = axiom6ChartCandidate p q l m t := by
  obtain ⟨hl, hm⟩ := (axiom6_iff_equations p q l m _).mp h
  have hd := axiom6_dot_or_dot p q l m _ hn h
  simp only [Line.chart, mul_one] at hd
  by_cases hd₁ : l.chartDot t ≠ 0
  · rw [axiom6ChartCandidate, ite_eq_left hd₁]
    exact congrArg (Line.chart t) ((Line.alignment_chart_iff_offset l p t c hd₁).mp hl)
  · have hd₂ : m.chartDot t ≠ 0 := hd.resolve_left hd₁
    rw [axiom6ChartCandidate, ite_eq_right hd₁]
    exact congrArg (Line.chart t) ((Line.alignment_chart_iff_offset m q t c hd₂).mp hm)

/-- The exceptional horizontal direction has its own candidate formula. -/
def axiom6HorizontalCandidate (p q : Point K) (l m : Line K) : Line K :=
  Line.horizontal (if l.b ≠ 0 then p.2-l.residual p/(2*l.b) else q.2-m.residual q/(2*m.b))

/-- Reconstruction also covers every valid horizontal crease. -/
theorem axiom6_horizontal_eq_candidate (p q : Point K) (l m : Line K) (c : K)
    (hn : ¬axiom6FreeDirection p q l m)
    (h : (axiom6 p q l m).Satisfies (Line.horizontal c)) :
    Line.horizontal c = axiom6HorizontalCandidate p q l m := by
  have offset (target : Line K) (r : Point K) (hb : target.b ≠ 0)
      (he : (Line.horizontal c).alignmentEquation target r = 0) :
      c = r.2-target.residual r/(2*target.b) := by
    rw [Line.alignmentEquation_horizontal] at he
    field_simp
    nlinarith
  obtain ⟨hl, hm⟩ := (axiom6_iff_equations p q l m _).mp h
  have hd := axiom6_dot_or_dot p q l m _ hn h
  simp only [Line.horizontal, mul_zero, mul_one, zero_add] at hd
  unfold axiom6HorizontalCandidate
  by_cases hb : l.b ≠ 0
  · rw [ite_eq_left hb]
    exact congrArg Line.horizontal (offset l p hb hl)
  · rw [ite_eq_right hb]
    exact congrArg Line.horizontal (offset m q (hd.resolve_left hb) hm)

/-- A horizontal solution lowers the polynomial degree, so it cannot add a
fourth solution to three nonhorizontal ones. -/
theorem axiom6_polynomial_leading_zero (p q : Point K) (l m : Line K) (c : K)
    (h : (axiom6 p q l m).Satisfies (Line.horizontal c)) :
    (axiom6Polynomial p q l m).cubic = 0 := by
  simpa only [axiom6Polynomial, mul_assoc] using axiom6_horizontal_leading_zero p q l m c h

/-- A nonzero eliminant without a free offset permits at most three creases. -/
theorem axiom6_solutions_subset_triple (p q : Point ℝ) (l m : Line ℝ)
    (hn : ¬axiom6FreeDirection p q l m) (hp : ¬(axiom6Polynomial p q l m).IsZero) :
    ∃ first second third : Line ℝ, (axiom6 p q l m).solutions ⊆ {first, second, third} := by
  have hc (crease : Line ℝ) (h : (axiom6 p q l m).Satisfies crease)
      (he : crease = Line.chart crease.b crease.c) :
      crease = axiom6ChartCandidate p q l m crease.b ∧
        (axiom6Polynomial p q l m).eval crease.b = 0 := by
    have h' : (axiom6 p q l m).Satisfies (Line.chart crease.b crease.c) := he ▸ h
    exact ⟨he.trans (axiom6_chart_eq_candidate p q l m _ _ hn h'),
      by rw [axiom6Polynomial_eval]; exact axiom6_eliminant_zero p q l m _ _ h'⟩
  by_cases hl : (axiom6Polynomial p q l m).cubic = 0
  · obtain ⟨r, s, hrs⟩ := (axiom6Polynomial p q l m).zeros_subset_pair hp hl
    refine ⟨axiom6ChartCandidate p q l m r, axiom6ChartCandidate p q l m s,
      axiom6HorizontalCandidate p q l m, ?_⟩
    intro crease h
    rcases crease.chart_cases with he | he
    · obtain ⟨heq, hr⟩ := hc crease h he
      exact (hrs crease.b hr).imp
        (fun hroot => heq.trans (congrArg (axiom6ChartCandidate p q l m) hroot))
        (fun hroot => Or.inl (heq.trans (congrArg (axiom6ChartCandidate p q l m) hroot)))
    · exact Or.inr (Or.inr (he.trans (axiom6_horizontal_eq_candidate p q l m _ hn (he ▸ h))))
  · obtain ⟨r, s, u, hrs⟩ := (axiom6Polynomial p q l m).zeros_subset_triple hp
    refine ⟨axiom6ChartCandidate p q l m r, axiom6ChartCandidate p q l m s,
      axiom6ChartCandidate p q l m u, ?_⟩
    intro crease h
    rcases crease.chart_cases with he | he
    · obtain ⟨heq, hr⟩ := hc crease h he
      rcases hrs crease.b hr with hr | hr | hr
      · exact Or.inl (heq.trans (congrArg (axiom6ChartCandidate p q l m) hr))
      · exact Or.inr (Or.inl (heq.trans (congrArg (axiom6ChartCandidate p q l m) hr)))
      · exact Or.inr (Or.inr (heq.trans (congrArg (axiom6ChartCandidate p q l m) hr)))
    · exact False.elim (hl (axiom6_polynomial_leading_zero p q l m _ (he ▸ h)))

/-- A common free direction gives an infinite family of valid offsets. -/
theorem axiom6_free_not_admissible (p q : Point ℝ) (l m : Line ℝ)
    (h : axiom6FreeDirection p q l m) : ¬(axiom6 p q l m).Admissible := by
  obtain ⟨ha, hb⟩ := l.normal_eq_of_determinant_zero m h.1
  apply (infinite_perpendicular_lines l).mono
  intro crease hc
  have hd₁ : l.a*crease.a+l.b*crease.b = 0 := (Line.perpendicular_comm _ _).mp hc
  have hd₂ : m.a*crease.a+m.b*crease.b = 0 := by rwa [ha, hb] at hd₁
  apply (axiom6_iff_equations p q l m crease).mpr
  simp only [Line.alignmentEquation, (Line.residual_eq_zero l p).mpr h.2.1,
    (Line.residual_eq_zero m q).mpr h.2.2, hd₁, hd₂, zero_mul, mul_zero, sub_self, and_self]

/-- A zero eliminant gives infinitely many distinct crease directions.
The construction avoids the one possible direction where division fails. -/
theorem axiom6_zero_polynomial_not_admissible (p q : Point ℝ) (l m : Line ℝ)
    (hp : (axiom6Polynomial p q l m).IsZero) : ¬(axiom6 p q l m).Admissible := by
  let direction (n : ℕ) : ℝ := if l.b = 0 then n else -l.a/l.b+n+1
  have hd (n : ℕ) : l.chartDot (direction n) ≠ 0 := by
    by_cases hb : l.b = 0
    · have ha := l.normal_ne_zero.resolve_right (not_not.mpr hb)
      simpa [Line.chartDot, direction, hb] using ha
    · have he : l.chartDot (direction n) = l.b*((n : ℝ)+1) := by
        dsimp [Line.chartDot, direction]
        rw [ite_eq_right hb]
        field_simp
        ring
      rw [he]
      exact mul_ne_zero hb (by positivity)
  let family (n : ℕ) := Line.chart (direction n)
    (p.1+direction n*p.2-l.residual p*(1+direction n^2)/(2*l.chartDot (direction n)))
  have hinj : Function.Injective family := by
    intro n k he
    have hv := congrArg Line.b he
    change direction n = direction k at hv
    by_cases hb : l.b = 0 <;> simpa [direction, hb] using hv
  have hf (n : ℕ) : (axiom6 p q l m).Satisfies (family n) := by
    apply (axiom6_iff_eliminant p q l m _ _ (hd n)).mpr
    refine ⟨rfl, ?_⟩
    rw [← axiom6Polynomial_eval]
    exact (axiom6Polynomial p q l m).eval_of_isZero hp _
  apply (Set.infinite_range_of_injective hinj).mono
  rintro crease ⟨n, rfl⟩
  exact hf n

/-- The two exceptional infinite families are the complete obstruction to
finite-choice admissibility, including empty and lower-degree solution sets. -/
theorem axiom6_admissible_iff (p q : Point ℝ) (l m : Line ℝ) :
    (axiom6 p q l m).Admissible ↔
      ¬axiom6FreeDirection p q l m ∧ ¬(axiom6Polynomial p q l m).IsZero := by
  constructor
  · intro h
    exact ⟨fun hf => axiom6_free_not_admissible p q l m hf h,
      fun hp => axiom6_zero_polynomial_not_admissible p q l m hp h⟩
  · rintro ⟨hn, hp⟩
    obtain ⟨first, second, third, hs⟩ := axiom6_solutions_subset_triple p q l m hn hp
    exact (Set.toFinite ({first, second, third} : Set (Line ℝ))).subset hs

/-- The three-crease bound stated directly for legal finite requests. -/
theorem axiom6_solutions_bound (p q : Point ℝ) (l m : Line ℝ)
    (h : (axiom6 p q l m).Admissible) :
    ∃ first second third : Line ℝ, (axiom6 p q l m).solutions ⊆ {first, second, third} :=
  axiom6_solutions_subset_triple p q l m ((axiom6_admissible_iff p q l m).mp h).1
    ((axiom6_admissible_iff p q l m).mp h).2

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The eliminant coefficients commute with coordinate interpretation. -/
theorem axiom6Polynomial_map {L : Type*} [Field L]
    (f : K →+* L) (p q : Point K) (l m : Line K) :
    axiom6Polynomial (Prod.map f f p) (Prod.map f f q) (l.map f) (m.map f) =
      (axiom6Polynomial p q l m).map f := by
  have htwo : f (2 : K) = (2 : L) := by
    convert map_add f (1 : K) 1 using 1 <;> norm_num
  simp [axiom6Polynomial, Univariate.Cubic.map, Line.residual, Line.map, Prod.map, htwo]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The free-direction guard is preserved and reflected by embeddings. -/
theorem axiom6FreeDirection_map_iff {L : Type*} [Field L]
    (f : K →+* L) (p q : Point K) (l m : Line K) :
    axiom6FreeDirection (Prod.map f f p) (Prod.map f f q) (l.map f) (m.map f) ↔
      axiom6FreeDirection p q l m := by
  have hd : (l.map f).determinant (m.map f) = f (l.determinant m) := by
    simp [Line.determinant, Line.map]
  simp only [axiom6FreeDirection, hd, ← map_zero f, f.injective.eq_iff, Prod.map,
    Line.contains_map]

end FoldInput
end LeanOrigami
