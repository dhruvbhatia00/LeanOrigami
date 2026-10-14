import LeanOrigami.Construction.ArithmeticRecipe
import LeanOrigami.Text.Replay

/-!
# Arithmetic recipe execution contracts

These specifications concern the actual primitive programs, not merely the
existence of some construction of the same number. The seven local inputs
include the standard coordinate frame and two signed axis coordinates.
-/

namespace LeanOrigami.ArithmeticRecipe
variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Exact local inputs of the arithmetic recipes. Frame objects must already
have been constructed when a recipe is used inside a proof. -/
def inputs (x y : K) : Program.State K :=
  [.point (0, 0), .point (1, 0), .line (Line.horizontal 0),
   .line (Line.chart 0 0), .point (0, 1), .point (x, 0), .point (y, 0)]

/-- The claimed output of an instruction. This is data, not evidence that the
instruction is legal; `Program.execute` checks that separately. -/
def selectedObject : Instruction K → Object K
  | .fold _ line => .line line
  | .intersect _ _ point => .point point

/-- Complete claimed state, used to state successful execution precisely. -/
def resultState (recipe : Recipe K 7) (x y : K) : Program.State K :=
  inputs x y ++ recipe.steps.map selectedObject

/-- A recipe succeeds with the advertised coordinate on the given operands.
Both the full execution and the final reference are part of the contract. -/
def Computes (recipe : Recipe K 7) (x y result : K) : Prop :=
  Program.execute (inputs x y) recipe.steps = .ok (resultState recipe x y) ∧
  Program.point (resultState recipe x y) recipe.output = .ok (result, 0)

/-- Discharge the rational identities and zero cases in arithmetic recipes. -/
local macro "arithmetic_geometry" : tactic => `(tactic|
  (try origami_geometry
   all_goals try split_ifs
   all_goals simp_all [sub_eq_add_neg]
   all_goals try (field_simp <;> ring)))

/-- Addition works for all signed inputs, including zero and equal inputs. -/
theorem add_computes (x y : K) : Computes (add x y) x y (x + y) := by
  constructor
  · unfold inputs resultState
    origami_execute using arithmetic_geometry
  · rfl

/-- Subtraction has no distinctness or nonzero requirement on its operands. -/
theorem sub_computes (x y : K) : Computes (sub x y) x y (x - y) := by
  constructor
  · unfold inputs resultState
    origami_execute using arithmetic_geometry
  · rfl

/-- The positive diagonal policy in multiplication succeeds also at zero. -/
theorem mul_computes (x y : K) : Computes (mul x y) x y (x * y) := by
  constructor
  · unfold inputs resultState
    origami_execute using arithmetic_geometry
  · rfl

/-- Division requires precisely a nonzero divisor. The numerator may be zero. -/
theorem div_computes (x y : K) (hne : y ≠ 0) : Computes (div x y hne) x y (x / y) := by
  constructor
  · unfold inputs resultState
    origami_execute using arithmetic_geometry
  · rfl

/-- Any accepted execution of this concrete recipe has the promised output;
the checker is a function, so it cannot return a different successful state. -/
theorem Computes.output_of_execute {recipe : Recipe K 7} {x y value : K}
    (contract : Computes recipe x y value) {state : Program.State K}
    (execution : Program.execute (inputs x y) recipe.steps = .ok state) :
    Program.point state recipe.output = .ok (value, 0) := by
  rw [contract.1] at execution
  cases execution
  exact contract.2

end LeanOrigami.ArithmeticRecipe
