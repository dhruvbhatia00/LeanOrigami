import LeanOrigami.Widget.Recipe

/-!
# Shared coordinate-frame parameters for visual recipes

Library recipes take their frame as explicit, already available inputs.
These exact requirements prevent a sample frame from silently becoming an
extra proof seed. Arithmetic and measurement templates share this definition.
-/

namespace LeanOrigami.Widget.RecipeFrame

/-- An exact component value, used for frame and branch conditions. -/
def coordinateIs (index : Nat) (field : Component) (n : Int) : Condition :=
  .eq (.component index field) (.constant n 1)

/-- A named input denotes the specified point exactly. -/
def pointIs (index : Nat) (x y : Int) : Condition :=
  .and (coordinateIs index .x x) (coordinateIs index .y y)

/-- Line coefficients are canonical, so this specifies one geometric line. -/
def lineIs (index : Nat) (a b c : Int) : Condition :=
  .and (coordinateIs index .a a) (.and (coordinateIs index .b b) (coordinateIs index .c c))

/-- The five frame roles, in the same order as the primitive library recipes. -/
def parameters : Array RecipeParameter :=
  #[⟨"Origin (0, 0)", .point⟩, ⟨"Unit X (1, 0)", .point⟩,
    ⟨"X-axis", .line⟩, ⟨"Y-axis", .line⟩, ⟨"Unit Y (0, 1)", .point⟩]

/-- Concrete values of the required coordinate frame. -/
def requirements : Array Condition :=
  #[pointIs 0 0 0, pointIs 1 1 0, lineIs 2 0 1 0, lineIs 3 1 0 0, pointIs 4 0 1]

end LeanOrigami.Widget.RecipeFrame
