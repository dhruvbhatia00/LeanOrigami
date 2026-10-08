import LeanOrigami.Geometry.Basic

/-!
# Reflection and perpendicularity

Reflection uses the nonzero squared length of the normal. The formulas are
shared by exact coordinates and real geometry; no square root is required.
-/

namespace LeanOrigami
namespace Line
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Squared length of a line's normal. -/
def normalSq (l : Line K) : K := l.a^2 + l.b^2

/-- A valid normal has positive squared length. -/
theorem normalSq_pos (l : Line K) : 0 < l.normalSq := by
  rcases l.normal_ne_zero with ha | hb
  · have := sq_pos_of_ne_zero ha
    have := sq_nonneg l.b
    dsimp [normalSq]; linarith
  · have := sq_pos_of_ne_zero hb
    have := sq_nonneg l.a
    dsimp [normalSq]; linarith

/-- Division by the normal's squared length is always valid. -/
theorem normalSq_ne_zero (l : Line K) : l.normalSq ≠ 0 := ne_of_gt l.normalSq_pos

/-- Signed equation residual; zero is exactly incidence. -/
def residual (l : Line K) (p : Point K) : K := l.a*p.1 + l.b*p.2 - l.c

/-- Reflection of a point across the line. -/
def reflect (l : Line K) (p : Point K) : Point K :=
  (p.1 - 2*l.residual p/l.normalSq*l.a,
   p.2 - 2*l.residual p/l.normalSq*l.b)

/-- Perpendicular lines have orthogonal normals (and hence directions). -/
def Perpendicular (l m : Line K) : Prop := l.a*m.a + l.b*m.b = 0

instance (l m : Line K) : Decidable (l.Perpendicular m) :=
  inferInstanceAs (Decidable (_ = _))

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Perpendicularity is symmetric. -/
theorem perpendicular_comm (l m : Line K) : l.Perpendicular m ↔ m.Perpendicular l := by
  simp only [Perpendicular, mul_comm]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Incidence is exactly a vanishing equation residual. -/
@[simp] theorem residual_eq_zero (l : Line K) (p : Point K) :
    l.residual p = 0 ↔ l.Contains p := sub_eq_zero

/-- Reflection reverses the signed residual. -/
@[simp] theorem residual_reflect (l : Line K) (p : Point K) :
    l.residual (l.reflect p) = -l.residual p := by
  have hn := l.normalSq_ne_zero
  dsimp [reflect, residual]
  field_simp
  dsimp [normalSq]
  ring

/-- Reflection is its own inverse, including on the crease itself. -/
@[simp] theorem reflect_reflect (l : Line K) (p : Point K) :
    l.reflect (l.reflect p) = p := by
  unfold reflect
  rw [show l.residual (p.1 - 2*l.residual p/l.normalSq*l.a,
    p.2 - 2*l.residual p/l.normalSq*l.b) = -l.residual p from residual_reflect l p]
  apply Prod.ext <;> dsimp <;> ring

/-- A point remains fixed exactly when it lies on the crease. -/
@[simp] theorem reflect_eq_self (l : Line K) (p : Point K) :
    l.reflect p = p ↔ l.Contains p := by
  constructor
  · intro hp
    have hr := l.residual_reflect p
    rw [hp] at hr
    apply (residual_eq_zero l p).mp
    linarith
  · intro hp
    have hr := (residual_eq_zero l p).mpr hp
    simp [reflect, hr]

/-- Reflection never identifies two different points. -/
theorem reflect_injective (l : Line K) : Function.Injective l.reflect :=
  Function.LeftInverse.injective (l.reflect_reflect)

/-- The midpoint of a point and its reflection lies on the crease. -/
theorem midpoint_mem (l : Line K) (p : Point K) :
    l.Contains ((p.1+(l.reflect p).1)/2, (p.2+(l.reflect p).2)/2) := by
  have hr := l.residual_reflect p
  dsimp [residual] at hr
  dsimp [Contains]
  linarith

/-- Squared Euclidean distance, without introducing square roots. -/
def distanceSq (p q : Point K) : K := (p.1-q.1)^2 + (p.2-q.2)^2

/-- Reflection preserves Euclidean squared distance. -/
theorem distanceSq_reflect (l : Line K) (p q : Point K) :
    distanceSq (l.reflect p) (l.reflect q) = distanceSq p q := by
  have hn := l.normalSq_ne_zero
  dsimp [distanceSq, reflect, residual]
  field_simp
  dsimp [normalSq]
  ring

variable {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L]

omit [LinearOrder K] [IsStrictOrderedRing K] [LinearOrder L] [IsStrictOrderedRing L] in
/-- Perpendicularity is preserved and reflected by field embeddings. -/
@[simp] theorem perpendicular_map (f : K →+* L) (l m : Line K) :
    (l.map f).Perpendicular (m.map f) ↔ l.Perpendicular m := by
  dsimp [Perpendicular, map]
  rw [← map_mul, ← map_mul, ← map_add, ← map_zero f, f.injective.eq_iff]

omit [LinearOrder K] [IsStrictOrderedRing K] [LinearOrder L] [IsStrictOrderedRing L] in
/-- Computing a reflection commutes with interpreting its coordinates. -/
theorem reflect_map (f : K →+* L) (l : Line K) (p : Point K) :
    (l.map f).reflect (f p.1, f p.2) = (f (l.reflect p).1, f (l.reflect p).2) := by
  have htwo : f (2 : K) = (2 : L) := by
    convert map_add f (1 : K) 1 using 1 <;> norm_num
  simp [reflect, residual, normalSq, map, map_sub, map_add, map_mul, map_pow, htwo]

end Line
end LeanOrigami
