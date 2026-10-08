import Mathlib.Algebra.Order.Field.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Points and canonical lines

The same coordinate definitions serve exact algebraic computation and real
geometry. A line has equation `a*x + b*y = c`; its first nonzero normal
coefficient is one. No choice of slope or square root is needed.
-/

namespace LeanOrigami

/-- A point in the coordinate plane over `K`. -/
abbrev Point (K : Type*) := K × K

/-- A valid line with uniquely normalized coefficients. -/
@[ext] structure Line (K : Type*) [Zero K] [One K] where
  a : K
  b : K
  c : K
  normalized : a = 1 ∨ (a = 0 ∧ b = 1)

/-- Equality is executable by comparing the three canonical coefficients. -/
instance {K : Type*} [Zero K] [One K] [DecidableEq K] : DecidableEq (Line K) :=
  fun l m => decidable_of_iff (l.a = m.a ∧ l.b = m.b ∧ l.c = m.c)
    ⟨fun h => Line.ext h.1 h.2.1 h.2.2,
      fun h => ⟨congrArg Line.a h, congrArg Line.b h, congrArg Line.c h⟩⟩

namespace Line
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A line's normal vector cannot vanish. -/
theorem normal_ne_zero (l : Line K) : l.a ≠ 0 ∨ l.b ≠ 0 := by
  rcases l.normalized with h | ⟨_, h⟩
  · exact Or.inl (by rw [h]; exact one_ne_zero)
  · exact Or.inr (by rw [h]; exact one_ne_zero)

/-- Point incidence is the line's defining equation. -/
def Contains (l : Line K) (p : Point K) : Prop := l.a * p.1 + l.b * p.2 = l.c

instance (l : Line K) (p : Point K) : Decidable (l.Contains p) :=
  inferInstanceAs (Decidable (_ = _))

/-- Normalize a nonzero normal. The proof prevents division by zero. -/
def normalize (a b c : K) (_h : a ≠ 0 ∨ b ≠ 0) : Line K :=
  if a = 0 then
    ⟨0, 1, c / b, Or.inr ⟨rfl, rfl⟩⟩
  else ⟨1, b / a, c / a, Or.inl rfl⟩

/-- Public checked construction from arbitrary coefficients. -/
def ofCoefficients? (a b c : K) : Option (Line K) :=
  if h : a ≠ 0 ∨ b ≠ 0 then some (normalize a b c h) else none

/-- Normalizing coefficients preserves precisely the same incidence equation. -/
@[simp] theorem contains_normalize (a b c : K) (h : a ≠ 0 ∨ b ≠ 0) (p : Point K) :
    (normalize a b c h).Contains p ↔ a * p.1 + b * p.2 = c := by
  by_cases ha : a = 0
  · have hb : b ≠ 0 := h.resolve_left (not_not.mpr ha)
    simp only [normalize, ha, ite_true, Contains, zero_mul, one_mul, zero_add]
    rw [eq_div_iff hb]
    constructor <;> intro hp <;> nlinarith
  · simp only [normalize, ha, ite_false, Contains, one_mul]
    constructor <;> intro hp
    · field_simp at hp
      nlinarith
    · field_simp
      nlinarith

/-- Canonical lines are equal if they contain exactly the same points. -/
theorem ext_contains {l m : Line K} (h : ∀ p, l.Contains p ↔ m.Contains p) : l = m := by
  rcases l.normalized with hl | ⟨hl, hlb⟩ <;>
    rcases m.normalized with hm | ⟨hm, hmb⟩
  · have h₀ := (h (l.c, 0)).mp (by simp [Contains, hl])
    have h₁ := (h (l.c - l.b, 1)).mp (by simp [Contains, hl])
    simp only [Contains, hm, one_mul, mul_zero, add_zero, mul_one] at h₀ h₁
    apply Line.ext
    · exact hl.trans hm.symm
    · linarith
    · exact h₀
  · have h₀ := (h (l.c, 0)).mp (by simp [Contains, hl])
    have h₁ := (h (l.c - l.b, 1)).mp (by simp [Contains, hl])
    simp [Contains, hm, hmb] at h₀ h₁
    exact False.elim (by linarith)
  · have h₀ := (h (0, l.c)).mp (by simp [Contains, hl, hlb])
    have h₁ := (h (1, l.c)).mp (by simp [Contains, hl, hlb])
    simp [Contains, hm] at h₀ h₁
    exact False.elim (by linarith)
  · have hc := (h (0, l.c)).mp (by simp [Contains, hl, hlb])
    simp [Contains, hm, hmb] at hc
    exact Line.ext (hl.trans hm.symm) (hlb.trans hmb.symm) hc

/-- Equality of canonical coefficients is exactly equality of geometric lines. -/
theorem eq_iff_contains (l m : Line K) : l = m ↔ ∀ p, l.Contains p ↔ m.Contains p :=
  ⟨by rintro rfl; exact fun _ => Iff.rfl, ext_contains⟩

/-- Normalization is unchanged by any nonzero coefficient scaling. -/
theorem normalize_scale (a b c k : K) (h : a ≠ 0 ∨ b ≠ 0) (hk : k ≠ 0) :
    normalize (k*a) (k*b) (k*c)
      (h.imp (mul_ne_zero hk) (mul_ne_zero hk)) = normalize a b c h := by
  apply ext_contains
  intro p
  simp only [contains_normalize]
  rw [show k*a*p.1 + k*b*p.2 = k*(a*p.1+b*p.2) by ring]
  exact ⟨mul_left_cancel₀ hk, congrArg (k * ·)⟩

/-- A canonical line remains unchanged when normalized again. -/
@[simp] theorem normalize_self (l : Line K) :
    normalize l.a l.b l.c l.normal_ne_zero = l := by
  apply ext_contains
  intro p
  exact contains_normalize _ _ _ _ _

omit [IsStrictOrderedRing K] in
/-- Invalid normal coefficients are rejected, whatever the constant term. -/
@[simp] theorem ofCoefficients_zero (c : K) : ofCoefficients? 0 0 c = none := by
  simp [ofCoefficients?]

/-- The unique candidate line through two distinct points. -/
def through (p q : Point K) (h : p ≠ q) : Line K :=
  normalize (q.2-p.2) (p.1-q.1) ((q.2-p.2)*p.1+(p.1-q.1)*p.2) (by
    by_contra hn
    push Not at hn
    apply h
    exact Prod.ext (sub_eq_zero.mp hn.2) (sub_eq_zero.mp hn.1).symm)

@[simp] theorem through_left (p q : Point K) (h : p ≠ q) :
    (through p q h).Contains p := by
  simp [through]

@[simp] theorem through_right (p q : Point K) (h : p ≠ q) :
    (through p q h).Contains q := by
  simp only [through, contains_normalize]
  ring

/-- The determinant of two normals detects unique intersection. -/
def determinant (l m : Line K) : K := l.a*m.b - m.a*l.b

/-- Cramer's formula, available only when the intersection is unique. -/
def intersection (l m : Line K) (_h : determinant l m ≠ 0) : Point K :=
  ((l.c*m.b-m.c*l.b)/determinant l m,
   (l.a*m.c-m.a*l.c)/determinant l m)

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The computed intersection lies on both lines. -/
theorem intersection_mem (l m : Line K) (h : determinant l m ≠ 0) :
    l.Contains (intersection l m h) ∧ m.Contains (intersection l m h) := by
  constructor <;> dsimp [Contains, intersection] <;> field_simp
  all_goals dsimp [determinant]; ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- No other common point exists when the determinant is nonzero. -/
theorem intersection_unique (l m : Line K) (h : determinant l m ≠ 0)
    (p : Point K) (hl : l.Contains p) (hm : m.Contains p) :
    p = intersection l m h := by
  dsimp [Contains] at hl hm
  apply Prod.ext <;> dsimp [intersection] <;> apply (eq_div_iff h).mpr
  · dsimp [determinant]
    linear_combination m.b * hl - l.b * hm
  · dsimp [determinant]
    linear_combination l.a * hm - m.a * hl

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- A line cannot supply a unique intersection with itself. -/
@[simp] theorem determinant_self (l : Line K) : determinant l l = 0 := by
  simp [determinant]

/-- Parallel normals and one shared point force canonical lines to coincide. -/
theorem eq_of_determinant_zero_of_mem (l m : Line K)
    (hd : determinant l m = 0) (p : Point K)
    (hp : l.Contains p) (hq : m.Contains p) : l = m := by
  rcases l.normalized with hl | ⟨hl, hlb⟩ <;>
    rcases m.normalized with hm | ⟨hm, hmb⟩
  · simp [determinant, hl, hm] at hd
    have hb : l.b = m.b := by linarith
    apply Line.ext (hl.trans hm.symm) hb
    dsimp [Contains] at hp hq
    rw [hl, hb] at hp
    rw [hm] at hq
    exact hp.symm.trans hq
  · simp [determinant, hl, hm, hmb] at hd
  · simp [determinant, hl, hlb, hm] at hd
  · apply Line.ext (hl.trans hm.symm) (hlb.trans hmb.symm)
    simp [Contains, hl, hlb] at hp
    simp [Contains, hm, hmb] at hq
    exact hp.symm.trans hq

/-- Two distinct common points determine the whole line. -/
theorem eq_of_common_points (l m : Line K) (p q : Point K) (h : p ≠ q)
    (hlp : l.Contains p) (hlq : l.Contains q)
    (hmp : m.Contains p) (hmq : m.Contains q) : l = m := by
  by_cases hd : determinant l m = 0
  · exact eq_of_determinant_zero_of_mem l m hd p hlp hmp
  · exact False.elim (h ((intersection_unique l m hd p hlp hmp).trans
      (intersection_unique l m hd q hlq hmq).symm))

/-- The line through distinct points is unique. -/
theorem through_unique (p q : Point K) (h : p ≠ q) (l : Line K)
    (hp : l.Contains p) (hq : l.Contains q) : l = through p q h :=
  eq_of_common_points l (through p q h) p q h hp hq
    (through_left p q h) (through_right p q h)

variable {L : Type*} [Field L]

/-- Transport line coefficients through a field embedding. -/
def map (f : K →+* L) (l : Line K) : Line L where
  a := f l.a
  b := f l.b
  c := f l.c
  normalized := by
    rcases l.normalized with h | ⟨h, hb⟩
    · left; simp [h]
    · right; simp [h, hb]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Transport preserves and reflects incidence, not only forward membership. -/
@[simp] theorem contains_map (f : K →+* L) (l : Line K) (p : Point K) :
    (l.map f).Contains (f p.1, f p.2) ↔ l.Contains p := by
  change f l.a * f p.1 + f l.b * f p.2 = f l.c ↔ _
  rw [← map_mul, ← map_mul, ← map_add, f.injective.eq_iff]
  rfl

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Distinct canonical lines remain distinct under a field embedding. -/
theorem map_injective (f : K →+* L) : Function.Injective (map f) := by
  intro l m h
  exact Line.ext (f.injective (congrArg Line.a h))
    (f.injective (congrArg Line.b h)) (f.injective (congrArg Line.c h))

end Line
end LeanOrigami
