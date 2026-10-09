import LeanOrigami.Construction.Basis

/-!
# Choosing either side of the initial axis

The reusable basis recipe starts with only `(0,0)` and `(1,0)`. Object 8 is
`(0,1)` or `(0,-1)`, depending on the exact rule-5 crease saved at object 5.
These examples expose both replay and the resulting geometric histories.
-/

namespace LeanOrigamiDemos.OffAxis
open LeanOrigami

example : Program.run (Basis.program ℚ true) = .ok (Basis.objects true) := Basis.replay true
example : Program.run (Basis.program ℚ false) = .ok (Basis.objects false) := Basis.replay false
example : Constructible (.point (0, 1)) := Basis.point_constructible true
example : Constructible (.point (0, -1)) := Basis.point_constructible false

end LeanOrigamiDemos.OffAxis
