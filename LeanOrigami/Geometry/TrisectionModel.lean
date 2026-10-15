import LeanOrigami.Geometry.Angles

/-!
# Algebraic data for general angle trisection

The two ray directions must be noncollinear. Five selected roots normalize
the rays, choose the side containing the second ray, and specify the two
interior trisectors. These numbers are proposed construction outputs, not
additional starting points. Their realization by folds is a separate recipe.
-/

namespace LeanOrigami.Trisection
variable {K : Type*} [Field K]

/-- Nonzero, nonstraight rays from a common vertex. Either orientation is allowed. -/
def Domain (vertex first second : Point K) : Prop :=
  (first-vertex).det (second-vertex) ≠ 0

/-- Normalize a displacement using a proposed positive length. -/
def unitVector (vertex endpoint : Point K) (length : K) : Point K :=
  ((endpoint.1-vertex.1)/length, (endpoint.2-vertex.2)/length)

/-- Exact root choices needed by the construction. No trigonometric function
is used to compute or store these values. -/
structure Roots (K : Type*) where
  firstLength : K
  secondLength : K
  sine : K
  thirdCosine : K
  thirdSine : K

/-- The cosine is obtained from the normalized input directions. -/
def Roots.cosine (roots : Roots K) (vertex first second : Point K) : K :=
  (unitVector vertex first roots.firstLength).dot
    (unitVector vertex second roots.secondLength)

/-- The perpendicular unit direction lies on the side of the second ray.
This works for clockwise as well as counterclockwise input rays. -/
def Roots.perpendicularUnit (roots : Roots K) (vertex first second : Point K) : Point K :=
  let u := unitVector vertex first roots.firstLength
  let v := unitVector vertex second roots.secondLength
  let c := roots.cosine vertex first second
  ((v.1-c*u.1)/roots.sine, (v.2-c*u.2)/roots.sine)

/-- First trisector endpoint, one unit from the original vertex. -/
def Roots.firstPoint (roots : Roots K) (vertex first second : Point K) : Point K :=
  let u := unitVector vertex first roots.firstLength
  let w := roots.perpendicularUnit vertex first second
  (vertex.1 + roots.thirdCosine*u.1 + roots.thirdSine*w.1,
   vertex.2 + roots.thirdCosine*u.2 + roots.thirdSine*w.2)

/-- Second trisector endpoint, using the double-angle polynomial formulas. -/
def Roots.secondPoint (roots : Roots K) (vertex first second : Point K) : Point K :=
  let u := unitVector vertex first roots.firstLength
  let w := roots.perpendicularUnit vertex first second
  (vertex.1 + (2*roots.thirdCosine^2-1)*u.1 + 2*roots.thirdCosine*roots.thirdSine*w.1,
   vertex.2 + (2*roots.thirdCosine^2-1)*u.2 + 2*roots.thirdCosine*roots.thirdSine*w.2)

/-- Polynomial equations and strict branch choices for all five roots. The
interval `(1/2, 1)` selects the cosine of a third of an angle in `(0, π)`. -/
def Roots.Valid [LinearOrder K] (roots : Roots K) (vertex first second : Point K) : Prop :=
  0 < roots.firstLength ∧ roots.firstLength^2 = (first-vertex).sqNorm ∧
  0 < roots.secondLength ∧ roots.secondLength^2 = (second-vertex).sqNorm ∧
  0 < roots.sine ∧ roots.sine^2 = 1-(roots.cosine vertex first second)^2 ∧
  1/2 < roots.thirdCosine ∧ roots.thirdCosine < 1 ∧
  4*roots.thirdCosine^3-3*roots.thirdCosine = roots.cosine vertex first second ∧
  0 < roots.thirdSine ∧ roots.thirdSine^2 = 1-roots.thirdCosine^2

/-- Dividing a direction by its nonzero length gives a unit vector. -/
theorem unitVector_sqNorm (vertex endpoint : Point K) (length : K)
    (hn : length ≠ 0) (hs : length^2 = (endpoint-vertex).sqNorm) :
    (unitVector vertex endpoint length).sqNorm = 1 := by
  dsimp [Point.sqNorm] at hs
  dsimp [unitVector, Point.sqNorm]
  field_simp
  exact hs.symm

section Ordered
variable [LinearOrder K] [IsStrictOrderedRing K]

/-- The cubic is strictly increasing on the branch used for trisection.
No numerical ordering or solver enumeration is used to identify that branch. -/
theorem thirdCosine_unique {c x y : K} (hx : 1/2 < x) (hy : 1/2 < y)
    (hex : 4*x^3-3*x = c) (hey : 4*y^3-3*y = c) : x = y := by
  have hxx : 1/4 < x^2 := by nlinarith
  have hyy : 1/4 < y^2 := by nlinarith
  have hxy : 1/4 < x*y := by
    nlinarith [mul_pos (by linarith : 0 < x-1/2) (by linarith : 0 < y-1/2)]
  have hf : (x-y)*(4*(x^2+x*y+y^2)-3) = 0 := by nlinarith [hex, hey]
  have hn : 4*(x^2+x*y+y^2)-3 ≠ 0 := by linarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right hn)

/-- Noncollinear rays have strictly positive squared lengths. -/
theorem domain_lengths (vertex first second : Point K) (h : Domain vertex first second) :
    0 < (first-vertex).sqNorm ∧ 0 < (second-vertex).sqNorm := by
  constructor
  · apply (Point.sqNorm_pos_iff _).mpr
    intro hz
    simp [Domain, hz, Point.det] at h
  · apply (Point.sqNorm_pos_iff _).mpr
    intro hz
    simp [Domain, hz, Point.det] at h

/-- Positive normalization preserves noncollinearity and puts the cosine
strictly between -1 and 1. This is the domain needed for all later roots. -/
theorem cosine_bounds (vertex first second : Point K) (a b : K)
    (h : Domain vertex first second) (ha : 0 < a) (hb : 0 < b)
    (ha2 : a^2 = (first-vertex).sqNorm) (hb2 : b^2 = (second-vertex).sqNorm) :
    let c := (unitVector vertex first a).dot (unitVector vertex second b);
    -1 < c ∧ c < 1 := by
  let u := unitVector vertex first a
  let v := unitVector vertex second b
  have hu : u.sqNorm = 1 := unitVector_sqNorm _ _ _ (ne_of_gt ha) ha2
  have hv : v.sqNorm = 1 := unitVector_sqNorm _ _ _ (ne_of_gt hb) hb2
  have hd : u.det v = (first-vertex).det (second-vertex) / (a*b) := by
    dsimp [u, v, unitVector, Point.det]
    field_simp
  have hd0 : u.det v ≠ 0 := by
    rw [hd]
    exact div_ne_zero h (mul_ne_zero (ne_of_gt ha) (ne_of_gt hb))
  have he := Point.dot_sq_add_det_sq u v
  rw [hu, hv] at he
  have hp := sq_pos_of_ne_zero hd0
  change -1 < u.dot v ∧ u.dot v < 1
  constructor <;> nlinarith [sq_nonneg (u.dot v - 1), sq_nonneg (u.dot v + 1)]

/-- The constructed perpendicular direction is a unit vector orthogonal to
the first ray, and reconstructs the second ray with a positive sine. -/
theorem Roots.frame (roots : Roots K) (vertex first second : Point K)
    (h : roots.Valid vertex first second) :
    let u := unitVector vertex first roots.firstLength
    let v := unitVector vertex second roots.secondLength
    let w := roots.perpendicularUnit vertex first second
    let c := roots.cosine vertex first second
    u.sqNorm = 1 ∧ w.sqNorm = 1 ∧ u.dot w = 0 ∧
      v = (c*u.1+roots.sine*w.1, c*u.2+roots.sine*w.2) := by
  rcases h with ⟨ha, ha2, hb, hb2, hs, hs2, _⟩
  let u := unitVector vertex first roots.firstLength
  let v := unitVector vertex second roots.secondLength
  let c := roots.cosine vertex first second
  let w := roots.perpendicularUnit vertex first second
  have hu : u.sqNorm = 1 := unitVector_sqNorm _ _ _ (ne_of_gt ha) ha2
  have hv : v.sqNorm = 1 := unitVector_sqNorm _ _ _ (ne_of_gt hb) hb2
  have hc : c = u.1*v.1+u.2*v.2 := rfl
  have hn : roots.sine ≠ 0 := ne_of_gt hs
  change u.sqNorm = 1 ∧ w.sqNorm = 1 ∧ u.dot w = 0 ∧
    v = (c*u.1+roots.sine*w.1, c*u.2+roots.sine*w.2)
  refine ⟨hu, ?_, ?_, ?_⟩
  · change ((v.1-c*u.1)/roots.sine)^2 + ((v.2-c*u.2)/roots.sine)^2 = 1
    field_simp
    dsimp [Point.sqNorm] at hu hv
    change roots.sine^2 = 1-c^2 at hs2
    linear_combination hv + c^2*hu + 2*c*hc - hs2
  · change u.1*((v.1-c*u.1)/roots.sine) + u.2*((v.2-c*u.2)/roots.sine) = 0
    field_simp
    dsimp [Point.sqNorm] at hu
    linear_combination -hc - c*hu
  · apply Prod.ext
    all_goals change _ = c*_ + roots.sine*((_-c*_)/roots.sine)
    all_goals field_simp
    all_goals ring

/-- Both proposed endpoints are one unit from the vertex. This algebraic
fact supplies the nondegeneracy needed to fold their output lines. -/
theorem Roots.output_lengths (roots : Roots K) (vertex first second : Point K)
    (h : roots.Valid vertex first second) :
    (roots.firstPoint vertex first second-vertex).sqNorm = 1 ∧
      (roots.secondPoint vertex first second-vertex).sqNorm = 1 := by
  let u := unitVector vertex first roots.firstLength
  let w := roots.perpendicularUnit vertex first second
  let t := roots.thirdCosine
  let r := roots.thirdSine
  have hf := roots.frame vertex first second h
  change u.sqNorm = 1 ∧ w.sqNorm = 1 ∧ u.dot w = 0 ∧ _ at hf
  rcases hf with ⟨hu, hw, horth, _⟩
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, hr2⟩
  change r^2 = 1-t^2 at hr2
  dsimp [Point.sqNorm] at hu hw
  dsimp [Point.dot] at horth
  constructor
  · change (vertex.1+t*u.1+r*w.1-vertex.1)^2 + (vertex.2+t*u.2+r*w.2-vertex.2)^2 = 1
    linear_combination t^2*hu + r^2*hw + 2*t*r*horth + hr2
  · change (vertex.1+(2*t^2-1)*u.1+2*t*r*w.1-vertex.1)^2 +
      (vertex.2+(2*t^2-1)*u.2+2*t*r*w.2-vertex.2)^2 = 1
    linear_combination (2*t^2-1)^2*hu + (2*t*r)^2*hw + 2*(2*t^2-1)*(2*t*r)*horth + 4*t^2*hr2

/-- Each endpoint determines a genuine line through the vertex. -/
theorem Roots.output_ne (roots : Roots K) (vertex first second : Point K)
    (h : roots.Valid vertex first second) :
    vertex ≠ roots.firstPoint vertex first second ∧ vertex ≠ roots.secondPoint vertex first second := by
  obtain ⟨hfirst, hsecond⟩ := roots.output_lengths vertex first second h
  constructor
  · intro he
    rw [← he, sub_self] at hfirst
    norm_num [Point.sqNorm] at hfirst
  · intro he
    rw [← he, sub_self] at hsecond
    norm_num [Point.sqNorm] at hsecond

end Ordered

section Map
variable {L : Type*} [Field L]

/-- Interpret the selected roots in another field, without recomputing them. -/
def Roots.map (f : K →+* L) (roots : Roots K) : Roots L :=
  ⟨f roots.firstLength, f roots.secondLength, f roots.sine,
    f roots.thirdCosine, f roots.thirdSine⟩

/-- The cosine calculation commutes with field interpretation. -/
theorem Roots.cosine_map (f : K →+* L) (roots : Roots K) (vertex first second : Point K) :
    (roots.map f).cosine (f vertex.1, f vertex.2) (f first.1, f first.2) (f second.1, f second.2) =
      f (roots.cosine vertex first second) := by
  simp [Roots.map, Roots.cosine, unitVector, Point.dot]

/-- Both proposed endpoints commute with interpretation in the real plane. -/
theorem Roots.points_map (f : K →+* L) (roots : Roots K) (vertex first second : Point K) :
    (roots.map f).firstPoint (f vertex.1, f vertex.2) (f first.1, f first.2) (f second.1, f second.2) =
      (f (roots.firstPoint vertex first second).1, f (roots.firstPoint vertex first second).2) ∧
    (roots.map f).secondPoint (f vertex.1, f vertex.2) (f first.1, f first.2) (f second.1, f second.2) =
      (f (roots.secondPoint vertex first second).1, f (roots.secondPoint vertex first second).2) := by
  constructor <;> apply Prod.ext
  all_goals simp [map_ofNat, Roots.firstPoint, Roots.secondPoint, Roots.perpendicularUnit,
    Roots.cosine, Roots.map, unitVector, Point.dot]

/-- An order-preserving field embedding preserves every equation and branch
choice. In particular, exact algebraic witnesses may be interpreted in ℝ. -/
theorem Roots.map_valid [LinearOrder K] [LinearOrder L] (f : K →+* L)
    (hf : StrictMono f) (roots : Roots K) (vertex first second : Point K)
    (h : roots.Valid vertex first second) :
    (roots.map f).Valid (f vertex.1, f vertex.2) (f first.1, f first.2) (f second.1, f second.2) := by
  rcases h with ⟨ha, ha2, hb, hb2, hs, hs2, ht, ht1, ht3, hr, hr2⟩
  unfold Roots.Valid
  rw [Roots.cosine_map]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Roots.map] using hf ha
  · simpa [Roots.map, Point.sqNorm] using congrArg f ha2
  · simpa [Roots.map] using hf hb
  · simpa [Roots.map, Point.sqNorm] using congrArg f hb2
  · simpa [Roots.map] using hf hs
  · simpa [Roots.map] using congrArg f hs2
  · simpa [Roots.map, map_ofNat] using hf ht
  · simpa [Roots.map, map_ofNat] using hf ht1
  · simpa [Roots.map, map_ofNat] using congrArg f ht3
  · simpa [Roots.map] using hf hr
  · simpa [Roots.map] using congrArg f hr2

end Map
end LeanOrigami.Trisection
