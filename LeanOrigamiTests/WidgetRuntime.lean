import LeanOrigami.Widget

/-!
# Editing-session and saved-proof integration

Run explicitly with Lake's native library setup. Every fold below is selected
from actual discovery, then committed through the same session API as the GUI.
The generated proofs are checked separately in a fresh Lean process.
-/

namespace LeanOrigamiTests.WidgetRuntime
open LeanOrigami LeanOrigami.Widget

private def get {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"FAIL: {label}")

private def fold (session : Session) (number : Nat) (inputs : List Nat)
    (select : Line Scalar → Bool := fun _ => true) : IO Session := do
  let preview ← get (session.preview (← get (foldRequest number inputs)))
  let some (_, choices) := preview.pending | throw (IO.userError "missing preview")
  let some index := choices.findIdx? select | throw (IO.userError "missing desired branch")
  get (preview.choose index)

/-- Seven visible operations produce the axes, (1,1), and the horizontal unit line. -/
private def basis : IO Session := do
  let s ← fold {} 1 [0, 1]                 -- 2: x-axis
  let s ← fold s 4 [0, 2]                 -- 3: y-axis
  let s ← fold s 4 [1, 2]                 -- 4: x=1
  let s ← fold s 5 [1, 0, 3] (fun l => decide (l.b < 0)) -- 5: y=x
  let s ← get (s.intersect 4 5)            -- 6: (1,1)
  let s ← fold s 4 [6, 3]                 -- 7: y=1
  get (s.intersect 3 7)                   -- 8: (0,1)

private def saveProof (name goal : String) (session : Session) (point : Nat)
    (coordinate : Coordinate) : IO String := do
  let saved ← get (← prepareComposition session point coordinate)
  IO.println s!"PASS: {name}, {session.program.length} exact editing steps; proof prepared"
  return s!"theorem {name} : LeanOrigami.ConstructibleNumber ({goal}) := by\n  origami composed ({saved.replace "\n" "\n  "})\n#print axioms {name}\n\n"

/-- Focused runtime checks plus rational, square-root, and cube-root proof files. -/
def run : IO Unit := do
  IO.FS.createDirAll ".lake/phase6"
  let s ← fold {} 1 [0, 1]
  let half ← fold s 2 [0, 1]
  let half ← get (half.intersect 2 3)
  require "half" ((← get (half.selected 4 .x)) == (1/2 : Scalar))
  require "wrong kind rejected" (match half.intersect 0 2 with | .error _ => true | _ => false)
  require "missing reference rejected" (match half.intersect 2 999 with | .error _ => true | _ => false)
  require "coincident lines rejected" (match half.intersect 2 2 with | .error _ => true | _ => false)
  require "missing preview rejected" (match half.choose 0 with | .error _ => true | _ => false)
  let undone ← get half.undo
  require "undo removes last object" (undone.objects.length == 4 && undone.pending.isNone)
  let view := half.view 32
  let refined := half.view 128
  require "refinement preserves identities" (view.objects.map (·.index) == refined.objects.map (·.index))
  let mut source := "import LeanOrigami.Widget\n\n"
  source := source ++ (← saveProof "half" "(1 / 2 : ℝ)" half 4 .x)
  let base ← basis
  let bisectors ← get (base.preview (.axiom3 ⟨2⟩ ⟨3⟩))
  require "axiom 3 offers both bisectors" ((bisectors.view 48).choices.size == 2)
  discard (get (bisectors.choose 1))
  let perpendicular ← get (base.preview (.axiom7 ⟨1⟩ ⟨3⟩ ⟨2⟩))
  require "axiom 7 has a unique crease" ((perpendicular.view 48).choices.size == 1)
  discard (get (perpendicular.choose 0))
  let sqrt ← fold base 5 [6, 0, 2]
    (fun l => decide (0 < (l.reflect (1, 1)).1)) -- 9: selected crease
  let sqrt ← fold sqrt 4 [6, 9]                -- 10: source/landing line
  let sqrt ← get (sqrt.intersect 10 2)          -- 11: (sqrt 2,0)
  require "square root equation" ((← get (sqrt.selected 11 .x)) ^ 2 == (2 : Scalar))
  source := source ++ (← saveProof "squareRoot" "Real.sqrt 2" sqrt 11 .x)
  -- Construct the rational input of y=t*x-t² for t³=2.
  let s ← fold base 5 [1, 0, 3] (fun l => decide (0 < l.b)) -- 9: y=-x
  let s ← get (s.intersect 4 9)                 -- 10: (1,-1)
  let s ← fold s 4 [10, 3]                     -- 11: y=-1
  let s ← get (s.intersect 7 9)                 -- 12: (-1,1)
  let s ← fold s 4 [6, 5]                      -- 13: y=-x+2
  let s ← get (s.intersect 13 2)                -- 14: (2,0)
  let s ← fold s 4 [14, 2]                     -- 15: x=2
  let s ← fold s 4 [12, 9]                     -- 16: y=x+2
  let s ← get (s.intersect 16 2)                -- 17: (-2,0)
  let preview ← get (s.preview (.axiom6 ⟨8⟩ ⟨17⟩ ⟨11⟩ ⟨15⟩))
  let some (_, choices) := preview.pending | throw (IO.userError "missing cubic preview")
  require "one real cube root" (choices.length == 1)
  let s ← get (preview.choose 0)               -- 18: y=t*x-t²
  let s ← fold s 4 [0, 18]                     -- 19: perpendicular through origin
  let s ← fold s 4 [0, 19]                     -- 20: y=t*x
  let cube ← get (s.intersect 20 4)            -- 21: (1,cube root 2)
  require "cube root equation" ((← get (cube.selected 21 .y)) ^ 3 == (2 : Scalar))
  source := source ++ (← saveProof "cubeRoot" "(2 : ℝ) ^ (1 / (3 : ℝ))" cube 21 .y)
  -- The scaled trisection cubic t³-3t-1 has three distinct real branches.
  let s ← fold base 5 [1, 0, 3] (fun l => decide (0 < l.b)) -- 9: y=-x
  let s ← get (s.intersect 4 9)                -- 10: (1,-1)
  let s ← fold s 4 [10, 3]                    -- 11: y=-1
  let s ← get (s.intersect 7 9)                -- 12: (-1,1)
  let s ← fold s 4 [12, 2]                    -- 13: x=-1
  let s ← fold s 4 [10, 9]                    -- 14: y=x-2
  let s ← get (s.intersect 13 14)              -- 15: (-1,-3)
  let trisection ← get (s.preview (.axiom6 ⟨8⟩ ⟨15⟩ ⟨11⟩ ⟨4⟩))
  require "three trisection previews" ((trisection.view 64).choices.size == 3)
  require "precision preserves branch indices"
    ((trisection.view 32).choices.map (·.index) == (trisection.view 128).choices.map (·.index))
  IO.FS.writeFile ".lake/phase6/trisection.json" (Lean.toJson (trisection.view 64)).compress
  IO.FS.writeFile ".lake/phase6/Saved.lean" source
  IO.FS.writeFile ".lake/phase6/scene.json" (Lean.toJson (cube.view 64)).compress
  IO.println "PASS: invalid inputs, undo, display identity; fresh proof replay remains separate"

end LeanOrigamiTests.WidgetRuntime

def main : IO Unit := LeanOrigamiTests.WidgetRuntime.run
