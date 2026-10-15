import LeanOrigami.Widget.Requirements
import LeanOrigami.Geometry.AngleSemantics

/-!
# Exact angle requirements

Rational examples exercise the executable checker. The irrational examples
check the intended real angles through the proved interpretation, without
using numerical trigonometry in a condition.
-/

namespace LeanOrigamiTests.Angles
open LeanOrigami

/-- A vertical line and a diagonal make an ordinary 45-degree line angle. -/
example : (Condition.lineAngle .fortyFive 0 1).checkObjects
    ([.line (⟨1, 0, 0, Or.inl rfl⟩), .line (⟨1, 1, 0, Or.inl rfl⟩)] : List (Object ℚ)) = true := by
  decide +kernel

/-- Translating the vertex does not change the angle of two rays. -/
example : (Condition.rayAngle .fortyFive 0 1 2).checkObjects
    ([.point (2, -1), .point (3, -1), .point (3, 0)] : List (Object ℚ)) = true := by
  decide +kernel

/-- Squaring alone would accept this 135-degree supplement; the ray sign rejects it. -/
example : (Condition.rayAngle .fortyFive 0 1 2).checkObjects
    ([.point (0, 0), .point (1, 0), .point (-1, 1)] : List (Object ℚ)) = false := by
  decide +kernel

/-- A zero-length ray is not an angle input. -/
example : (Condition.rayAngle .fortyFive 0 1 2).checkObjects
    ([.point (0, 0), .point (0, 0), .point (1, 1)] : List (Object ℚ)) = false := by
  decide +kernel

/-- A right angle is outside these acute named families. -/
example : (Condition.lineAngle .sixty 0 1).checkObjects
    ([.line (⟨0, 1, 0, Or.inr ⟨rfl, rfl⟩⟩), .line (⟨1, 0, 0, Or.inl rfl⟩)] : List (Object ℚ)) = false := by
  decide +kernel

/-- A malformed reference stays invalid even when its condition is negated. -/
example : (Condition.not (.rayAngle .thirty 0 1 2)).checkObjects
    ([.point (0, 0), .line (⟨1, 0, 0, Or.inl rfl⟩)] : List (Object ℚ)) = false := by
  decide +kernel

/-- Nonzero scaling, including sign reversal, preserves an unoriented angle. -/
example : NamedAngle.fortyFive.Unoriented ((-2 : ℚ), 0) (3, 3) := by
  norm_num [NamedAngle.Unoriented, NamedAngle.cosineNumerator, Point.dot, Point.sqNorm]

/-- The exact thirty-degree polynomial means the actual Mathlib angle. -/
example : InnerProductGeometry.angle (Point.toPlane (1, 0))
    (Point.toPlane (Real.sqrt 3, 1)) = Real.pi/6 := by
  apply ((NamedAngle.thirty.rays_iff_angle _ _).mp ?_).2.2
  norm_num [NamedAngle.Rays, NamedAngle.Unoriented, NamedAngle.cosineNumerator,
    Point.dot, Point.sqNorm]

/-- Swapping the long and short coordinates gives sixty degrees. -/
example : InnerProductGeometry.angle (Point.toPlane (1, 0))
    (Point.toPlane (1, Real.sqrt 3)) = Real.pi/3 := by
  apply ((NamedAngle.sixty.rays_iff_angle _ _).mp ?_).2.2
  norm_num [NamedAngle.Rays, NamedAngle.Unoriented, NamedAngle.cosineNumerator,
    Point.dot, Point.sqNorm]

/-- The editor's line-angle form uses the same exact condition as the library. -/
example : ((Widget.RequirementInput.condition
    ⟨"lineAngle", #[0, 1], #["45"]⟩ #[]).toOption.map
      (fun c => c.checkObjects ([.line ⟨1, 0, 0, Or.inl rfl⟩,
        .line ⟨1, 1, 0, Or.inl rfl⟩] : List (Object ℚ)))) = some true := by
  decide +kernel

/-- Ray authoring retains the sign check that excludes the supplement. -/
example : ((Widget.RequirementInput.condition
    ⟨"rayAngle", #[0, 1, 2], #["45"]⟩ #[]).toOption.map
      (fun c => c.checkObjects ([.point (0, 0), .point (1, 0),
        .point (-1, 1)] : List (Object ℚ)))) = some false := by
  decide +kernel

/-- Unsupported angle values are rejected rather than rounded to a named angle. -/
example : (Widget.RequirementInput.condition
    ⟨"lineAngle", #[0, 1], #["44.999"]⟩ #[]).toOption.isNone = true := by
  decide +kernel

#print axioms NamedAngle.unoriented_scale_iff
#print axioms NamedAngle.rays_iff_angle
#print axioms NamedAngle.lines_iff_angle
#print axioms NamedAngle.atVertex_iff_angle
#print axioms Condition.lineAngle_holds
#print axioms Condition.rayAngle_holds

end LeanOrigamiTests.Angles
