import LeanOrigami.Construction.ArithmeticCorrectness

/-!
# Arithmetic operations with execution specifications

Unary operations reuse subtraction and division by aliasing the appropriate
frame point. All operations expand into ordinary primitive instructions; the
frame and scalar inputs are explicit, including in standalone recipe workspaces.
-/

namespace LeanOrigami

/-- The elementary signed-coordinate operations offered by the recipe library. -/
inductive ArithmeticOperation where
  | add | sub | neg | mul | inv | div
  deriving DecidableEq, Repr

namespace ArithmeticOperation
variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Five coordinate-frame objects, then one or two scalar inputs. -/
def arity : ArithmeticOperation → Nat
  | .neg | .inv => 6
  | _ => 7

/-- The only extra arithmetic restriction is a nonzero divisor. -/
def Valid (op : ArithmeticOperation) (x y : K) : Prop :=
  match op with
  | .inv => x ≠ 0
  | .div => y ≠ 0
  | _ => True

instance (op : ArithmeticOperation) (x y : K) : Decidable (op.Valid x y) := by
  cases op <;> unfold Valid <;> infer_instance

/-- Advertised signed result; `y` is ignored by unary operations. -/
def value (op : ArithmeticOperation) (x y : K) : K :=
  match op with
  | .add => x+y | .sub => x-y | .neg => -x
  | .mul => x*y | .inv => x⁻¹ | .div => x/y

/-- Standard frame followed by the actual operand objects. -/
def inputs (op : ArithmeticOperation) (x y : K) : Program.State K :=
  (ArithmeticRecipe.inputs x y).take op.arity

/-- Expand the selected operation. Unary operations supply the origin or unit
as the first operand of the existing binary construction. -/
def recipe (op : ArithmeticOperation) (x y : K) (h : op.Valid x y) : Recipe K op.arity :=
  match op with
  | .add => ArithmeticRecipe.add x y
  | .sub => ArithmeticRecipe.sub x y
  | .mul => ArithmeticRecipe.mul x y
  | .div => ArithmeticRecipe.div x y h
  | .neg => RecipeBuilder.build 6 do
    RecipeBuilder.use (ArithmeticRecipe.sub 0 x)
      (fun i => if i.val == 5 then 0 else if i.val == 6 then 5 else i.val)
  | .inv => RecipeBuilder.build 6 do
    RecipeBuilder.use (ArithmeticRecipe.div 1 x h)
      (fun i => if i.val == 5 then 1 else if i.val == 6 then 5 else i.val)

/-- Every valid invocation has a successful execution and its selected output
is precisely the advertised signed coordinate. This includes unary aliases. -/
theorem computes (op : ArithmeticOperation) (x y : K) (h : op.Valid x y) :
    let recipe := op.recipe x y h
    let final := op.inputs x y ++ recipe.steps.map ArithmeticRecipe.selectedObject
    Program.execute (op.inputs x y) recipe.steps = .ok final ∧
      Program.point final recipe.output = .ok (op.value x y, 0) := by
  cases op with
  | add => exact ArithmeticRecipe.add_computes x y
  | sub => exact ArithmeticRecipe.sub_computes x y
  | mul => exact ArithmeticRecipe.mul_computes x y
  | div => exact ArithmeticRecipe.div_computes x y h
  | neg =>
    constructor
    · unfold inputs arity ArithmeticRecipe.inputs
      origami_execute using
        try origami_geometry
        all_goals try split_ifs
        all_goals simp_all
    · change Except.ok (0 - x, 0) = Except.ok (-x, 0)
      rw [zero_sub]
  | inv =>
    constructor
    · unfold inputs arity ArithmeticRecipe.inputs
      origami_execute using
        try origami_geometry
        all_goals simp_all [Valid]
    · simp only [recipe, value]
      change Except.ok (1 / x, 0) = Except.ok (x⁻¹, 0)
      rw [one_div]

end ArithmeticOperation
end LeanOrigami
