import LeanOrigami.Scalar.Roots
import LeanOrigami.Solvers.Candidates

/-!
# Exact fold discovery with Hex

Hex supplies polynomial roots; the geometric candidate layer reconstructs
creases and checks the original equations. Real interpretation appears only
in the proofs. Saved construction programs still retain an exact crease,
not an index into these lists.
-/

namespace LeanOrigami.Scalar

/-- Finite roots used after the fold's infinite-family guard has been checked.
The zero polynomial contributes no candidates here; callers prove that their
required polynomial is nonzero before relying on completeness. -/
def rootList (coefficients : List Scalar) : List Scalar :=
  match realRoots (polynomial coefficients) with
  | .all => []
  | .finite values => values

/-- A nonzero evaluation excludes the all-roots case and makes the finite list
complete even for a real root not already supplied as an algebraic number. -/
theorem rootList_complete (coefficients : List Scalar)
    (hn : ∃ x : ℝ, coefficients.foldr (fun a v => toReal a + x*v) 0 ≠ 0)
    (x : ℝ) (hx : coefficients.foldr (fun a v => toReal a + x*v) 0 = 0) :
    ∃ r ∈ rootList coefficients, toReal r = x := by
  have hs := (contains_realRoots_polynomial coefficients x).mpr hx
  cases he : realRoots (polynomial coefficients) with
  | all =>
      obtain ⟨y, hy⟩ := hn
      exact False.elim (hy ((contains_realRoots_polynomial coefficients y).mp
        (by rw [he]; trivial)))
  | finite values =>
      simpa only [rootList, he, RealRoots.Contains] using hs

/-- The finite extractor never invents a root, even for a zero polynomial. -/
theorem rootList_sound (coefficients : List Scalar) (r : Scalar)
    (hr : r ∈ rootList coefficients) :
    coefficients.foldr (fun a v => toReal a + toReal r*v) 0 = 0 := by
  apply (contains_realRoots_polynomial coefficients (toReal r)).mp
  cases he : realRoots (polynomial coefficients) with
  | all => simp only [RealRoots.Contains]
  | finite values =>
      exact ⟨r, by simpa only [rootList, he] using hr, rfl⟩

private theorem cubic_nonzero_eval (p : Univariate.Cubic ℝ) (hn : ¬p.IsZero) :
    ∃ t, p.eval t ≠ 0 := by
  by_contra h
  push Not at h
  have h₀ := h 0
  have h₁ := h 1
  have h₂ := h 2
  have hneg := h (-1)
  apply hn
  dsimp [Univariate.Cubic.eval] at h₀ h₁ h₂ hneg
  exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- Any real root of a nonzero cubic with algebraic coefficients is represented
exactly by the root finder, including lower degrees and repeated roots. -/
theorem rootList_cubic_complete (p : Univariate.Cubic Scalar) (hn : ¬p.IsZero)
    (x : ℝ) (hx : (p.map realHom).eval x = 0) :
    ∃ r ∈ rootList p.coefficients, toReal r = x := by
  have he (t : ℝ) :
      p.coefficients.foldr (fun a v => toReal a + t*v) 0 = (p.map realHom).eval t := by
    simp [Univariate.Cubic.coefficients, Univariate.Cubic.eval, Univariate.Cubic.map, realHom]
  apply rootList_complete p.coefficients
  · obtain ⟨t, ht⟩ := cubic_nonzero_eval (p.map realHom)
      (by simpa only [Univariate.Cubic.isZero_map_iff] using hn)
    exact ⟨t, by simpa only [he] using ht⟩
  · simpa only [he] using hx

/-- Quadratic and linear equations use the same exact-root guarantee. -/
theorem rootList_quadratic_complete (a b c : Scalar)
    (hn : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) (x : ℝ)
    (hx : toReal a*x^2+toReal b*x+toReal c = 0) :
    ∃ r ∈ rootList [c, b, a], toReal r = x := by
  let p : Univariate.Cubic Scalar := ⟨c, b, a, 0⟩
  have hp : ¬p.IsZero := by
    intro hz
    rcases hn with ha | hb | hc
    · exact ha hz.2.2.1
    · exact hb hz.2.1
    · exact hc hz.1
  have he (t : ℝ) : [c, b, a].foldr (fun a v => toReal a+t*v) 0 =
      (p.map realHom).eval t := by
    simp [p, Univariate.Cubic.map, Univariate.Cubic.eval, realHom]
  apply rootList_complete [c, b, a]
  · obtain ⟨t, ht⟩ := cubic_nonzero_eval (p.map realHom)
      (by simpa only [Univariate.Cubic.isZero_map_iff] using hp)
    exact ⟨t, by simpa only [he] using ht⟩
  · simp only [List.foldr_cons, List.foldr_nil, mul_zero, add_zero]
    nlinarith [hx]

private theorem point_ne_map (p q : Point Scalar) (h : p ≠ q) :
    (toReal p.1, toReal p.2) ≠ (toReal q.1, toReal q.2) := by
  intro he
  exact h (Prod.ext (realHom.injective (congrArg Prod.fst he))
    (realHom.injective (congrArg Prod.snd he)))

private theorem circle_coefficients_map (l : Line Scalar) (q : Point Scalar) (radius : Scalar) :
    (l.map realHom).circleCoefficients (toReal q.1, toReal q.2) (toReal radius) =
      (l.circleCoefficients q radius).map toReal := by
  have htwo : realHom (2 : Scalar) = (2 : ℝ) := by
    convert map_add realHom (1 : Scalar) 1 using 1 <;> norm_num
  change (l.map realHom).circleCoefficients (realHom q.1, realHom q.2) (realHom radius) =
    (l.circleCoefficients q radius).map realHom
  have hz : realHom l.a = 0 ↔ l.a = 0 := by
    rw [← map_zero realHom, realHom.injective.eq_iff]
  by_cases ha : l.a = 0 <;>
    simp [Line.circleCoefficients, Line.map, hz, ha, htwo]

private theorem circle_root_complete (l : Line Scalar) (q : Point Scalar) (radius : Scalar)
    (t : ℝ)
    (ht : Line.distanceSq (toReal q.1, toReal q.2) ((l.map realHom).pointAt t) = toReal radius) :
    ∃ r ∈ rootList (l.circleCoefficients q radius), toReal r = t := by
  have he (x : ℝ) :
      (l.circleCoefficients q radius).foldr (fun a v => toReal a+x*v) 0 =
      Line.distanceSq (toReal q.1, toReal q.2) ((l.map realHom).pointAt x)-toReal radius := by
    have h := (l.map realHom).circleCoefficients_eval (toReal q.1, toReal q.2) (toReal radius) x
    rw [circle_coefficients_map, List.foldr_map] at h
    exact h
  apply rootList_complete (l.circleCoefficients q radius)
  · by_contra hn
    push Not at hn
    have h₀ := hn 0
    have h₁ := hn 1
    have hneg := hn (-1)
    rw [he] at h₀ h₁ hneg
    dsimp [Line.pointAt, Line.distanceSq] at h₀ h₁ hneg
    split_ifs at h₀ h₁ hneg <;> nlinarith [sq_nonneg ((l.map realHom).b)]
  · rw [he, ht, sub_self]

private theorem distanceSq_map (p q : Point Scalar) :
    Line.distanceSq (toReal p.1, toReal p.2) (toReal q.1, toReal q.2) =
      toReal (Line.distanceSq p q) := by
  change Line.distanceSq (realHom p.1, realHom p.2) (realHom q.1, realHom q.2) =
    realHom (Line.distanceSq p q)
  simp [Line.distanceSq]

private theorem direction_root_complete (l m : Line Scalar) (t : ℝ)
    (ht : (l.map realHom).directionCross (m.map realHom)*(1-t^2)-
      2*(l.map realHom).directionDifference (m.map realHom)*t = 0) :
    ∃ r ∈ rootList [l.directionCross m, -2*l.directionDifference m, -l.directionCross m],
      toReal r = t := by
  apply rootList_quadratic_complete
  · rcases l.direction_coefficients_ne m with hs | hd
    · exact Or.inr (Or.inr hs)
    · right; left
      rw [neg_mul, neg_ne_zero]
      exact mul_ne_zero two_ne_zero hd
  · have hs : (l.map realHom).directionCross (m.map realHom) =
        realHom (l.directionCross m) := by simp [Line.directionCross, Line.map]
    have hd : (l.map realHom).directionDifference (m.map realHom) =
        realHom (l.directionDifference m) := by simp [Line.directionDifference, Line.map]
    have htwo : realHom (2 : Scalar) = (2 : ℝ) := by
      convert map_add realHom (1 : Scalar) 1 using 1 <;> norm_num
    change realHom (-l.directionCross m)*t^2+
      realHom (-2*l.directionDifference m)*t+realHom (l.directionCross m) = 0
    rw [map_neg, map_mul, map_neg, htwo]
    rw [hs, hd] at ht
    nlinarith [ht]

/-- Hex provides every root required by a finite fold request. -/
theorem rootsCover (input : FoldInput Scalar) (hf : input.FiniteCondition) :
    input.RootsCover rootList := by
  cases input with
  | axiom3 l m =>
      intro t ht
      obtain ⟨r, hr, he⟩ := direction_root_complete l m (toReal t) (by
        have h := congrArg realHom ht
        have htwo : realHom (2 : Scalar) = (2 : ℝ) := by
          convert map_add realHom (1 : Scalar) 1 using 1 <;> norm_num
        have htwo' : toReal (2 : Scalar) = 2 := htwo
        simpa [Line.directionCross, Line.directionDifference, Line.map,
          map_sub, map_mul, map_pow, realHom, htwo'] using h)
      exact realHom.injective he ▸ hr
  | axiom5 p q l =>
      intro t ht
      obtain ⟨r, hr, he⟩ := circle_root_complete l q (Line.distanceSq q p) (toReal t) (by
        rw [show toReal t = realHom t from rfl, Line.pointAt_map]
        change Line.distanceSq (toReal q.1, toReal q.2)
          (toReal (l.pointAt t).1, toReal (l.pointAt t).2) = toReal (Line.distanceSq q p)
        rw [distanceSq_map, ht])
      exact realHom.injective he ▸ hr
  | axiom6 p q l m =>
      intro t ht
      obtain ⟨r, hr, he⟩ := rootList_cubic_complete (FoldInput.axiom6Polynomial p q l m)
        hf.2 (toReal t) (by rw [show toReal t = realHom t from rfl, Univariate.Cubic.eval_map, ht, map_zero])
      exact realHom.injective he ▸ hr
  | _ => trivial

private theorem chart_map (t c : Scalar) :
    (Line.chart t c).map realHom = Line.chart (toReal t) (toReal c) := by
  apply Line.ext
  · exact map_one realHom
  · rfl
  · rfl

private theorem horizontal_map (c : Scalar) :
    (Line.horizontal c).map realHom = Line.horizontal (toReal c) := by
  apply Line.ext
  · exact map_zero realHom
  · exact map_one realHom
  · rfl

private theorem offset_map (p : Point Scalar) (l : Line Scalar) (t : Scalar) :
    realHom (p.1+t*p.2-l.residual p*(1+t^2)/(2*l.chartDot t)) =
      realHom p.1+realHom t*realHom p.2-
        (l.map realHom).residual (realHom p.1, realHom p.2)*(1+(realHom t)^2)/
          (2*(l.map realHom).chartDot (realHom t)) := by
  have htwo : realHom (2 : Scalar) = (2 : ℝ) := by
    convert map_add realHom (1 : Scalar) 1 using 1 <;> norm_num
  simp [Line.residual, Line.chartDot, Line.map, htwo]

private theorem horizontal_offset_map (p : Point Scalar) (l : Line Scalar) :
    realHom (p.2-l.residual p/(2*l.b)) =
      realHom p.2-(l.map realHom).residual (realHom p.1, realHom p.2)/(2*(l.map realHom).b) := by
  have htwo : realHom (2 : Scalar) = (2 : ℝ) := by
    convert map_add realHom (1 : Scalar) 1 using 1 <;> norm_num
  simp [Line.residual, Line.map, htwo]

private theorem cubic_chart_map (p q : Point Scalar) (l m : Line Scalar) (t : Scalar) :
    (FoldInput.axiom6ChartCandidate p q l m t).map realHom =
      FoldInput.axiom6ChartCandidate (Prod.map realHom realHom p) (Prod.map realHom realHom q)
        (l.map realHom) (m.map realHom) (realHom t) := by
  have hd : (l.map realHom).chartDot (realHom t) = realHom (l.chartDot t) := by
    simp [Line.chartDot, Line.map]
  have hz : (l.map realHom).chartDot (realHom t) = 0 ↔ l.chartDot t = 0 := by
    rw [hd, ← map_zero realHom, realHom.injective.eq_iff]
  simp only [FoldInput.axiom6ChartCandidate, ne_eq, hz]
  split <;> rw [chart_map] <;>
    exact congrArg (Line.chart (realHom t)) (offset_map _ _ t)

private theorem cubic_horizontal_map (p q : Point Scalar) (l m : Line Scalar) :
    (FoldInput.axiom6HorizontalCandidate p q l m).map realHom =
      FoldInput.axiom6HorizontalCandidate (Prod.map realHom realHom p) (Prod.map realHom realHom q)
        (l.map realHom) (m.map realHom) := by
  have hz : (l.map realHom).b = 0 ↔ l.b = 0 := by
    change realHom l.b = 0 ↔ l.b = 0
    rw [← map_zero realHom, realHom.injective.eq_iff]
  simp only [FoldInput.axiom6HorizontalCandidate, ne_eq, hz]
  split <;> rw [horizontal_map] <;>
    exact congrArg Line.horizontal (horizontal_offset_map _ _)

/-- Every real crease of a finite request has algebraic coordinates. This is
proved over all real creases, independently of a proposed list of choices. -/
theorem crease_representable (input : FoldInput Scalar) (hf : input.FiniteCondition)
    (crease : Line ℝ) (hc : (input.map realHom).Satisfies crease) :
    ∃ exactCrease : Line Scalar, exactCrease.map realHom = crease := by
  cases input with
  | axiom1 p q =>
      refine ⟨Line.through p q hf, ?_⟩
      apply Line.eq_of_common_points _ _ (realHom p.1, realHom p.2)
        (realHom q.1, realHom q.2) (point_ne_map p q hf)
      · exact (Line.contains_map realHom _ _).mpr (Line.through_left p q hf)
      · exact (Line.contains_map realHom _ _).mpr (Line.through_right p q hf)
      · exact hc.1
      · exact hc.2
  | axiom2 p q =>
      change p ≠ q at hf
      refine ⟨Line.bisector p q hf, ?_⟩
      have h₁ := Line.bisector_unique _ _ (point_ne_map p q hf) crease hc
      have h₂ := Line.bisector_unique _ _ (point_ne_map p q hf)
        ((Line.bisector p q hf).map realHom) (by
          change ((Line.bisector p q hf).map realHom).reflect (realHom p.1, realHom p.2) =
            (realHom q.1, realHom q.2)
          rw [Line.reflect_map, Line.bisector_reflect])
      exact h₂.trans h₁.symm
  | axiom3 l m =>
      have hlm : l.map realHom ≠ m.map realHom :=
        fun he => hf (Line.map_injective realHom he)
      let p := l.pointAt 0
      have hp : (l.map realHom).pointAt 0 = (realHom p.1, realHom p.2) := by
        simpa only [map_zero] using Line.pointAt_map realHom l 0
      rcases crease.chart_cases with he | he
      · have hs := FoldInput.axiom3_direction _ _ (Line.chart crease.b crease.c) (he ▸ hc)
        obtain ⟨t, _, ht⟩ := direction_root_complete l m crease.b (by simpa [Line.chart] using hs)
        refine ⟨Line.chart t (p.1+t*p.2-m.residual p*(1+t^2)/(2*m.chartDot t)), ?_⟩
        rw [chart_map]
        have ho := offset_map p m t
        change toReal _ = _ at ho
        rw [show realHom t = crease.b from ht] at ho
        rw [ho, ht]
        exact (he.trans (congrArg (Line.chart crease.b)
          (by simpa only [hp] using FoldInput.axiom3_chart_offset _ _ _ _ hlm (he ▸ hc)))).symm
      · refine ⟨Line.horizontal (p.2-m.residual p/(2*m.b)), ?_⟩
        rw [horizontal_map]
        have ho := horizontal_offset_map p m
        change toReal _ = _ at ho
        rw [ho]
        exact (he.trans (congrArg Line.horizontal
          (by simpa only [hp] using FoldInput.axiom3_horizontal_offset _ _ _ hlm (he ▸ hc)))).symm
  | axiom4 p l =>
      refine ⟨Line.perpendicularThrough p l, ?_⟩
      exact Line.perpendicular_unique (realHom p.1, realHom p.2) (l.map realHom) _ crease
        ((Line.contains_map realHom _ _).mpr (Line.perpendicularThrough_mem p l)) hc.1
        ((Line.perpendicular_map realHom _ _).mpr (Line.perpendicularThrough_perpendicular p l)) hc.2
  | axiom5 p q l =>
      change (l.map realHom).Contains (crease.reflect (realHom p.1, realHom p.2)) ∧
        crease.Contains (realHom q.1, realHom q.2) at hc
      have hn : p ≠ q := by
        intro he
        subst q
        have hl := hf.resolve_left (not_not_intro rfl)
        apply hl
        apply (Line.contains_map realHom l p).mp
        simpa only [(crease.reflect_eq_self (realHom p.1, realHom p.2)).mpr hc.2] using hc.1
      have hnR := point_ne_map p q hn
      obtain ⟨landing, hl, hd, he⟩ := (FoldInput.axiom5_iff_landing _ _ _ crease hnR).mp hc
      obtain ⟨t, ht⟩ := (l.map realHom).exists_pointAt landing hl
      obtain ⟨r, _, hr⟩ := circle_root_complete l q (Line.distanceSq q p) t (by
        rw [ht, ← distanceSq_map]
        exact hd.symm)
      have hp : (toReal (l.pointAt r).1, toReal (l.pointAt r).2) = landing := by
        have h := Line.pointAt_map realHom l r
        change (l.map realHom).pointAt (toReal r) =
          (toReal (l.pointAt r).1, toReal (l.pointAt r).2) at h
        rw [hr, ht] at h
        exact h.symm
      have hdist : Line.distanceSq q p = Line.distanceSq q (l.pointAt r) := by
        apply toReal_injective
        rw [← distanceSq_map, ← distanceSq_map, hp]
        exact hd
      let candidate := Line.landingCrease p q (l.pointAt r) hn
      obtain ⟨href, hfixed⟩ := Line.landingCrease_spec p q (l.pointAt r) hn hdist
      refine ⟨candidate, ?_⟩
      apply Eq.trans (Line.eq_landingCrease _ _ landing hnR (candidate.map realHom)
        ((Line.contains_map realHom _ _).mpr hfixed) ?_) he.symm
      change (candidate.map realHom).reflect (realHom p.1, realHom p.2) = landing
      rw [Line.reflect_map]
      change (realHom ((Line.landingCrease p q (l.pointAt r) hn).reflect p).1,
        realHom ((Line.landingCrease p q (l.pointAt r) hn).reflect p).2) = landing
      rw [href]
      exact hp
  | axiom6 p q l m =>
      have hn := (FoldInput.axiom6FreeDirection_map_iff realHom p q l m).not.mpr hf.1
      rcases crease.chart_cases with he | he
      · obtain ⟨t, _, ht⟩ := rootList_cubic_complete (FoldInput.axiom6Polynomial p q l m)
          hf.2 crease.b (by
            rw [← FoldInput.axiom6Polynomial_map, FoldInput.axiom6Polynomial_eval]
            exact FoldInput.axiom6_eliminant_zero _ _ _ _ _ _ (he ▸ hc))
        refine ⟨FoldInput.axiom6ChartCandidate p q l m t, ?_⟩
        rw [cubic_chart_map, show realHom t = crease.b from ht]
        exact (he.trans (FoldInput.axiom6_chart_eq_candidate _ _ _ _ _ _ hn (he ▸ hc))).symm
      · refine ⟨FoldInput.axiom6HorizontalCandidate p q l m, ?_⟩
        rw [cubic_horizontal_map]
        exact (he.trans (FoldInput.axiom6_horizontal_eq_candidate _ _ _ _ _ hn (he ▸ hc))).symm
  | axiom7 p l m =>
      have hn : l.perpendicularAlignmentDot m ≠ 0 := by
        intro hz
        have hzR : (l.map realHom).perpendicularAlignmentDot (m.map realHom) = 0 := by
          rw [Line.perpendicularAlignmentDot_map, hz, map_zero]
        exact (hf.resolve_left (not_not_intro hz)) ((Line.contains_map realHom _ _).mp
          ((FoldInput.axiom7_zero_iff _ _ _ crease hzR).mp hc).1)
      let candidate := Line.alignPerpendicular p l m hn
      have hsat : (FoldInput.axiom7 p l m).Satisfies candidate :=
        (FoldInput.axiom7_iff_candidate p l m candidate hn).mpr rfl
      have hfinite := (FoldInput.finiteCondition_iff _).mp
        ((FoldInput.finiteCondition_map_iff realHom (.axiom7 p l m)).mpr hf)
      exact ⟨candidate, FoldInput.axiom7_solutions_subsingleton _ _ _ hfinite
        ((FoldInput.satisfies_map_iff realHom _ candidate).mpr hsat) hc⟩

/-- Discover the distinct exact crease choices for a specified fold request. -/
def folds (input : FoldInput Scalar) : Option (List (Line Scalar)) :=
  input.candidates rootList

/-- Returned creases satisfy the original real geometric relation and its
finite-choice condition; no correctness claim about candidate search is trusted. -/
theorem folds_sound (input : FoldInput Scalar) (choices : List (Line Scalar))
    (h : folds input = some choices) (crease : Line Scalar) (hc : crease ∈ choices) :
    (input.map realHom).Legal (crease.map realHom) := by
  have hf : input.FiniteCondition := by
    by_contra hn
    have he := (FoldInput.candidates_eq_none_iff rootList input).mpr hn
    rw [show input.candidates rootList = some choices from h] at he
    cases he
  exact ⟨(FoldInput.finiteCondition_iff _).mp
      ((FoldInput.finiteCondition_map_iff realHom input).mpr hf),
    (FoldInput.satisfies_map_iff realHom input crease).mpr
      (FoldInput.candidates_sound rootList input choices h crease hc)⟩

/-- Infinite solution sets, not merely empty lists, are reported as missing choices. -/
theorem folds_none_iff (input : FoldInput Scalar) :
    folds input = none ↔ ¬(input.map realHom).Admissible := by
  rw [folds, FoldInput.candidates_eq_none_iff, ← FoldInput.finiteCondition_iff,
    FoldInput.finiteCondition_map_iff]

/-- Every real solution occurs in the returned finite list. No assumption that
the crease was already algebraic is needed. -/
theorem folds_complete (input : FoldInput Scalar) (choices : List (Line Scalar))
    (h : folds input = some choices) (crease : Line ℝ)
    (hc : (input.map realHom).Satisfies crease) :
    ∃ exactCrease ∈ choices, exactCrease.map realHom = crease := by
  have hf : input.FiniteCondition := by
    by_contra hn
    have he := (FoldInput.candidates_eq_none_iff rootList input).mpr hn
    rw [show input.candidates rootList = some choices from h] at he
    cases he
  obtain ⟨exactCrease, he⟩ := crease_representable input hf crease hc
  have hs : input.Satisfies exactCrease :=
    (FoldInput.satisfies_map_iff realHom input exactCrease).mp (he ▸ hc)
  obtain ⟨found, hfound, hmem⟩ :=
    FoldInput.candidates_complete rootList input hf (rootsCover input hf) exactCrease hs
  have heq : found = choices := Option.some.inj (hfound.symm.trans h)
  exact ⟨exactCrease, heq ▸ hmem, he⟩

/-- A finite discovery result describes exactly the original real solution set. -/
theorem folds_spec (input : FoldInput Scalar) (choices : List (Line Scalar))
    (h : folds input = some choices) (crease : Line ℝ) :
    (input.map realHom).Satisfies crease ↔
      ∃ exactCrease ∈ choices, exactCrease.map realHom = crease := by
  constructor
  · exact folds_complete input choices h crease
  · rintro ⟨exactCrease, hc, rfl⟩
    exact (folds_sound input choices h exactCrease hc).2

/-- Choice identity is geometric: duplicate normalized creases are removed. -/
theorem folds_nodup (input : FoldInput Scalar) (choices : List (Line Scalar))
    (h : folds input = some choices) : choices.Nodup :=
  FoldInput.candidates_nodup rootList input choices h

end LeanOrigami.Scalar
