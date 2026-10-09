import LeanOrigami.Construction.Basis

/-!
# Replay all seven axioms, including three choices for one rule-6 request

The basis gives `(0,1)`. A second rule-5 branch constructs `(0,-1)`, after
which rule 6 can align these points with `y=-1` and `x=0` in three ways.
The remaining steps exercise rules 3, 7, and 2 and finish at `(1/2,0)`.
-/

namespace LeanOrigamiDemos.AllFolds
open LeanOrigami

/-- Names for the three exact choices, independent of enumeration order. -/
inductive Branch where
  | firstDiagonal | secondDiagonal | horizontal
  deriving DecidableEq

/-- The chosen rule-6 crease. One choice uses the separate horizontal chart. -/
def Branch.crease (K : Type) [Field K] : Branch → Line K
  | .firstDiagonal => Line.chart 1 (-1)
  | .secondDiagonal => Line.chart (-1) 1
  | .horizontal => Line.horizontal 0

/-- Every instruction uses references to objects already constructed in this program. -/
def program (K : Type) [Field K] (branch : Branch) : Program K :=
  Basis.program K true ++
  [.fold (.axiom5 ⟨1⟩ ⟨0⟩ ⟨3⟩) (Line.chart 1 0), -- 9: lower diagonal
   .intersect ⟨4⟩ ⟨9⟩ (1, -1),                 -- 10
   .fold (.axiom4 ⟨10⟩ ⟨3⟩) (Line.horizontal (-1)), -- 11
   .intersect ⟨3⟩ ⟨11⟩ (0, -1),                -- 12
   .fold (.axiom6 ⟨8⟩ ⟨12⟩ ⟨11⟩ ⟨3⟩) (branch.crease K), -- 13
   .fold (.axiom3 ⟨2⟩ ⟨3⟩) (Line.chart 1 0),    -- 14
   .fold (.axiom7 ⟨1⟩ ⟨3⟩ ⟨2⟩) (Line.chart 0 (1/2)), -- 15
   .intersect ⟨15⟩ ⟨2⟩ (1/2, 0),               -- 16
   .fold (.axiom2 ⟨0⟩ ⟨1⟩) (Line.chart 0 (1/2)), -- 17
   .intersect ⟨17⟩ ⟨2⟩ (1/2, 0)]               -- 18

/-- All three choices replay successfully through the same primitive checker. -/
theorem accepts (branch : Branch) : Program.accepts (program ℚ branch) ⟨18⟩ .x (1/2) = true := by
  cases branch <;> decide +kernel

/-- Full expected state, including the selected rule-6 crease at object 13. -/
def objects (branch : Branch) : List (Object ℚ) :=
  Basis.objects true ++
    [.line (Line.chart 1 0), .point (1, -1), .line (Line.horizontal (-1)), .point (0, -1),
     .line (branch.crease ℚ), .line (Line.chart 1 0), .line (Line.chart 0 (1/2)),
     .point (1/2, 0), .line (Line.chart 0 (1/2)), .point (1/2, 0)]

/-- The entire replayed state is checked, not just the final submission. -/
theorem replay (branch : Branch) : Program.run (program ℚ branch) = .ok (objects branch) := by
  cases branch <;> decide +kernel

/-- Each rule-6 branch has a real construction history from the original seeds. -/
theorem crease_constructible (branch : Branch) : Constructible (.line (branch.crease ℝ)) := by
  have h := Program.run_sound (Rat.castHom ℝ) (program ℚ branch) (objects branch)
    (replay branch) (.line (branch.crease ℚ)) (by simp [objects])
  cases branch <;> simpa [Object.map, Branch.crease, Line.map, Line.chart, Line.horizontal] using h

#print axioms crease_constructible

end LeanOrigamiDemos.AllFolds
