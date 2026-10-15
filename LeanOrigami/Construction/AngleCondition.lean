import LeanOrigami.Construction.Condition
import LeanOrigami.Geometry.Angles

/-!
# Named angles in the condition language

These families expand into the same polynomial and Boolean nodes as every
other requirement. Reference validation, serialization, exact decision, and
field interpretation therefore continue to use the existing checker.
-/

namespace LeanOrigami.Condition

private def zero : ConditionExpr := .constant 0 1

private def dot (u v : ConditionExpr × ConditionExpr) : ConditionExpr :=
  .add (.mul u.1 v.1) (.mul u.2 v.2)

private def unsigned (angle : NamedAngle) (u v : ConditionExpr × ConditionExpr) : Condition :=
  let uv := dot u v
  .and (.lt zero (dot u u)) (.and (.lt zero (dot v v))
    (.eq (.mul (.constant 4 1) (.mul uv uv))
      (.mul (.mul (.constant angle.cosineNumerator 1) (dot u u)) (dot v v))))

private def displacement (vertex point : Nat) : ConditionExpr × ConditionExpr :=
  (.add (.component point .x) (.neg (.component vertex .x)),
   .add (.component point .y) (.neg (.component vertex .y)))

/-- The smaller named angle between two lines, with no slope conversion. -/
def lineAngle (angle : NamedAngle) (first second : Nat) : Condition :=
  unsigned angle (.component first .a, .component first .b)
    (.component second .a, .component second .b)

/-- A named angle between rays from a common vertex. Nonzero directions and
the positive dot product are part of the exact condition, not GUI-only checks. -/
def rayAngle (angle : NamedAngle) (vertex first second : Nat) : Condition :=
  let u := displacement vertex first
  let v := displacement vertex second
  .and (unsigned angle u v) (.lt zero (dot u v))

/-- The line family expresses the exact geometric predicate on its arguments. -/
theorem lineAngle_holds {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (angle : NamedAngle) (l m : Line K) :
    (lineAngle angle 0 1).Holds (Component.value [.line l, .line m]) ↔ angle.Lines l m := by
  simp [lineAngle, unsigned, dot, zero, Holds, ConditionExpr.eval, Component.value,
    NamedAngle.Lines, NamedAngle.Unoriented, Point.dot, Point.sqNorm, pow_two]

/-- The ray family includes validity and the sign that rejects supplements. -/
theorem rayAngle_holds {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (angle : NamedAngle) (vertex first second : Point K) :
    (rayAngle angle 0 1 2).Holds (Component.value [.point vertex, .point first, .point second]) ↔
      angle.AtVertex vertex first second := by
  simp [rayAngle, unsigned, displacement, dot, zero, Holds, ConditionExpr.eval, Component.value,
    NamedAngle.AtVertex, NamedAngle.Rays, NamedAngle.Unoriented, Point.dot, Point.sqNorm,
    pow_two, sub_eq_add_neg]

end LeanOrigami.Condition
