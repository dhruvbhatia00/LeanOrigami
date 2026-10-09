import LeanOrigami.Text.Syntax

/-!
# Named primitive commands and rejected constructions

The successful example uses all seven axioms, including both branches of rule 5
and a saved rule-6 crease. Negative examples fail inside `fail_if_success`, so
no failed theorem or proof hole is introduced into the environment.
-/

namespace LeanOrigamiTests.Text
open LeanOrigami

-- Importing the language must leave common mathematical variable names usable.
example (x y : ℝ) : x + y = y + x := add_comm x y

/-- Named primitive replay, ending at the midpoint of the seed segment. -/
theorem all_rules : ConstructibleNumber (1/2 : ℝ) := by
  origami
    point O := origin
    point U := unit
    line axis := fold1 O U choose (LeanOrigami.Line.horizontal 0)
    line vertical := fold4 O axis choose (LeanOrigami.Line.chart 0 0)
    line unitVertical := fold4 U axis choose (LeanOrigami.Line.chart 0 1)
    line upper := fold5 U O vertical choose (LeanOrigami.Line.chart (-1) 0)
    point upperRight := intersect unitVertical upper choose (1, 1)
    line upperLevel := fold4 upperRight vertical choose (LeanOrigami.Line.horizontal 1)
    point upperUnit := intersect vertical upperLevel choose (0, 1)
    line lower := fold5 U O vertical choose (LeanOrigami.Line.chart 1 0)
    point lowerRight := intersect unitVertical lower choose (1, -1)
    line lowerLevel := fold4 lowerRight vertical choose (LeanOrigami.Line.horizontal (-1))
    point lowerUnit := intersect vertical lowerLevel choose (0, -1)
    line cubic := fold6 upperUnit lowerUnit lowerLevel vertical choose (LeanOrigami.Line.chart 1 (-1))
    line bisector := fold3 axis vertical choose (LeanOrigami.Line.chart 1 0)
    line alignment := fold7 U vertical axis choose (LeanOrigami.Line.chart 0 (1/2))
    point midpoint := intersect alignment axis choose (1/2, 0)
    line midpointFold := fold2 O U choose (LeanOrigami.Line.chart 0 (1/2))
    point result := intersect midpointFold axis choose (1/2, 0)
    number coordinate := x result
    submit coordinate

-- A discovery client may present either order, but selects by exact identity.
private def positiveCandidate (reverse : Bool) : ℤ :=
  ((if reverse then [1, -1] else [-1, 1]).find? (· == 1)).getD 0

/-- The selected exact root, rather than a candidate index, enters the proof. -/
noncomputable def reorderedQuadratic (reverse : Bool) : Text.Number := by
  origami
    point O := origin
    point U := unit
    number zero := x O
    number one := x U
    number negativeOne := sub zero one
    number root := quadratic one zero negativeOne choose (positiveCandidate reverse : ℝ) proving (by
      origami_values
      cases reverse <;> norm_num [positiveCandidate])
    finish root

example : (reorderedQuadratic false).value = 1 := by
  norm_num [reorderedQuadratic, Text.quadratic, positiveCandidate]
example : (reorderedQuadratic true).value = 1 := by
  norm_num [reorderedQuadratic, Text.quadratic, positiveCandidate]
example : (reorderedQuadratic false).value = (reorderedQuadratic true).value := rfl

/-- Missing names and forward references cannot supply construction evidence. -/
example : ConstructibleNumber (1 : ℝ) := by
  fail_if_success
    origami
      number result := x missing
      submit result
  exact ConstructibleNumber.one

/-- The typed interface rejects a point where a line is required. -/
example : ConstructibleNumber (1 : ℝ) := by
  fail_if_success
    origami
      point O := origin
      point U := unit
      line invalid := fold4 O U choose (LeanOrigami.Line.horizontal 0)
      number result := x U
      submit result
  exact ConstructibleNumber.one

/-- Names cannot silently shadow earlier construction objects. -/
example : ConstructibleNumber (1 : ℝ) := by
  fail_if_success
    origami
      point P := origin
      point P := unit
      number result := x P
      submit result
  exact ConstructibleNumber.one

/-- A wrong final coordinate cannot close the requested goal. -/
example : ConstructibleNumber (1 : ℝ) := by
  fail_if_success
    origami
      point O := origin
      number result := x O
      submit result
  exact ConstructibleNumber.one

/-- Reusable division cannot bypass its nonzero-divisor condition. -/
example : ConstructibleNumber (1 : ℝ) := by
  fail_if_success
    origami
      point O := origin
      point U := unit
      number zero := x O
      number one := x U
      number result := div one zero
      submit result
  exact ConstructibleNumber.one

/-- Even a correct square is insufficient for a negative square-root choice. -/
example : ConstructibleNumber (1 : ℝ) := by
  fail_if_success
    origami
      point U := unit
      number one := x U
      number result := sqrt one choose (-1)
      submit result
  exact ConstructibleNumber.one

/-- Selecting a crease that misses its inputs is rejected at that fold. -/
example : ConstructibleNumber (1 : ℝ) := by
  fail_if_success
    origami
      point O := origin
      point U := unit
      line invalid := fold1 O U choose (LeanOrigami.Line.horizontal 1)
      number result := x U
      submit result
  exact ConstructibleNumber.one

/-- An underconstrained fold is invalid even when the selected line satisfies
its geometric incidence conditions. -/
example : ConstructibleNumber (1 : ℝ) := by
  fail_if_success
    origami
      point O := origin
      point U := unit
      line invalid := fold1 O O choose (LeanOrigami.Line.horizontal 0)
      number result := x U
      submit result
  exact ConstructibleNumber.one

/-- A zero leading coefficient is not accepted as a quadratic construction. -/
example : ConstructibleNumber (1 : ℝ) := by
  fail_if_success
    origami
      point O := origin
      point U := unit
      number zero := x O
      number one := x U
      number invalid := quadratic zero zero zero choose 1
      submit one
  exact ConstructibleNumber.one

#print axioms all_rules
#print axioms reorderedQuadratic

end LeanOrigamiTests.Text
