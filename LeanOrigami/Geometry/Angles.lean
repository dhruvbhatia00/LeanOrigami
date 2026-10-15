import LeanOrigami.Geometry.Reflection

/-!
# Exact angle relations

Dot products and squared lengths express the named acute angles without
trigonometric computation. Unoriented directions allow either sign; rays retain
the positive-dot-product condition. Both relations exclude zero directions.
The real-angle interpretation is proved separately in `AngleSemantics`.
-/

namespace LeanOrigami
namespace Point
variable {K : Type*} [Field K]

/-- Coordinate dot product, also used for displacement vectors. -/
def dot (u v : Point K) : K := u.1*v.1 + u.2*v.2

/-- Squared length of a coordinate vector. -/
def sqNorm (u : Point K) : K := u.1^2 + u.2^2

/-- Signed area of two coordinate vectors. -/
def det (u v : Point K) : K := u.1*v.2 - u.2*v.1

/-- A squared length is positive exactly for a nonzero direction. -/
theorem sqNorm_pos_iff [LinearOrder K] [IsStrictOrderedRing K]
    (u : Point K) : 0 < u.sqNorm ↔ u ≠ 0 := by
  constructor
  · intro h hz
    subst u
    norm_num [sqNorm] at h
  · intro h
    by_cases hx : u.1 = 0
    · have hy : u.2 ≠ 0 := by
        intro hy
        exact h (Prod.ext hx hy)
      have := sq_pos_of_ne_zero hy
      dsimp [sqNorm]
      nlinarith [sq_nonneg u.1]
    · have := sq_pos_of_ne_zero hx
      dsimp [sqNorm]
      nlinarith [sq_nonneg u.2]

/-- The planar dot/determinant identity detects strict, nonstraight angles. -/
theorem dot_sq_add_det_sq (u v : Point K) :
    u.dot v ^ 2 + u.det v ^ 2 = u.sqNorm * v.sqNorm := by
  simp only [dot, det, sqNorm]
  ring

/-- Scaling a direction scales its squared length by the square of the factor. -/
theorem sqNorm_scale (a : K) (u : Point K) :
    sqNorm (a*u.1, a*u.2) = a^2*u.sqNorm := by
  simp only [sqNorm]
  ring

/-- Each factor acts linearly on the coordinate dot product. -/
theorem dot_scale (a b : K) (u v : Point K) :
    dot (a*u.1, a*u.2) (b*v.1, b*v.2) = a*b*u.dot v := by
  simp only [dot]
  ring

end Point

/-- The acute angle families exposed by the recipe requirement editor. -/
inductive NamedAngle where
  | thirty | fortyFive | sixty
  deriving DecidableEq, Repr

namespace NamedAngle
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Four times the squared cosine, so the executable relation has integer coefficients. -/
def cosineNumerator : NamedAngle → Nat
  | .thirty => 3 | .fortyFive => 2 | .sixty => 1

/-- The smaller angle between two unoriented, nonzero directions. -/
def Unoriented (angle : NamedAngle) (u v : Point K) : Prop :=
  0 < u.sqNorm ∧ 0 < v.sqNorm ∧
    4 * u.dot v ^ 2 = (angle.cosineNumerator : K) * u.sqNorm * v.sqNorm

/-- Rays distinguish an acute angle from its obtuse supplement. -/
def Rays (angle : NamedAngle) (u v : Point K) : Prop :=
  angle.Unoriented u v ∧ 0 < u.dot v

/-- Line normals may be used instead of tangents: rotating both by 90°
preserves their angle. Canonical line validity already excludes zero normals. -/
def Lines (angle : NamedAngle) (l m : Line K) : Prop :=
  angle.Unoriented (l.a, l.b) (m.a, m.b)

/-- Ray points are interpreted relative to the common vertex. -/
def AtVertex (angle : NamedAngle) (vertex first second : Point K) : Prop :=
  angle.Rays (first - vertex) (second - vertex)

instance (angle : NamedAngle) (u v : Point K) : Decidable (angle.Unoriented u v) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance (angle : NamedAngle) (u v : Point K) : Decidable (angle.Rays u v) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (angle : NamedAngle) (l m : Line K) : Decidable (angle.Lines l m) :=
  inferInstanceAs (Decidable (angle.Unoriented _ _))

instance (angle : NamedAngle) (vertex first second : Point K) :
    Decidable (angle.AtVertex vertex first second) :=
  inferInstanceAs (Decidable (angle.Rays _ _))

/-- Neither the sign nor magnitude of a direction representative changes an
unoriented angle. This includes independently reversing either line. -/
theorem unoriented_scale_iff (angle : NamedAngle) (u v : Point K)
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    angle.Unoriented (a*u.1, a*u.2) (b*v.1, b*v.2) ↔ angle.Unoriented u v := by
  have ha2 : 0 < a^2 := sq_pos_of_ne_zero ha
  have hb2 : 0 < b^2 := sq_pos_of_ne_zero hb
  have hn : a^2*b^2 ≠ 0 := ne_of_gt (mul_pos ha2 hb2)
  simp only [Unoriented, Point.sqNorm_scale, Point.dot_scale,
    mul_pos_iff_of_pos_left ha2, mul_pos_iff_of_pos_left hb2]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  constructor
  · intro h
    apply mul_left_cancel₀ hn
    calc
      a^2*b^2*(4*u.dot v^2) = 4*(a*b*u.dot v)^2 := by ring
      _ = (angle.cosineNumerator : K)*(a^2*u.sqNorm)*(b^2*v.sqNorm) := h
      _ = a^2*b^2*((angle.cosineNumerator : K)*u.sqNorm*v.sqNorm) := by ring
  · intro h
    calc
      4*(a*b*u.dot v)^2 = a^2*b^2*(4*u.dot v^2) := by ring
      _ = a^2*b^2*((angle.cosineNumerator : K)*u.sqNorm*v.sqNorm) := by rw [h]
      _ = (angle.cosineNumerator : K)*(a^2*u.sqNorm)*(b^2*v.sqNorm) := by ring

/-- Positive rescaling preserves a ray; negative scaling deliberately does not. -/
theorem rays_scale_iff (angle : NamedAngle) (u v : Point K)
    (a b : K) (ha : 0 < a) (hb : 0 < b) :
    angle.Rays (a*u.1, a*u.2) (b*v.1, b*v.2) ↔ angle.Rays u v := by
  simp only [Rays, unoriented_scale_iff angle u v a b (ne_of_gt ha) (ne_of_gt hb),
    Point.dot_scale, mul_pos_iff_of_pos_left (mul_pos ha hb)]

end NamedAngle
end LeanOrigami
