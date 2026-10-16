import LeanOrigami.Widget.LibraryRules
import LeanOrigami.Scalar.Roots

/-!
# Direct discovery for proved library calls

Only public geometry and a small list of root witnesses are computed. The same
formulas run with the ordinary scalar field for preview and the recording field
for export. Discovery supplies data, not proof; `LibraryRecipe.Produces` is the
independent obligation checked by the exported certificate.
-/

namespace LeanOrigami.Widget.LibraryRecipe

/-- Extra scalars are private certificate witnesses, not constructed objects.
Sign differences are recorded explicitly for short rational-enclosure proofs. -/
structure Discovery (K : Type*) [Field K] where
  outputs : Program.State K
  witnesses : List K := []
  signs : List K := []

section Formulas
variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {m : Type → Type} [Monad m] [MonadExceptOf String m]

private def point (inputs : Program.State K) (index : Nat) : m (Point K) :=
  match inputs[index]? with
  | some (.point p) => pure p
  | _ => throw s!"Recipe input {index + 1} must be a point."

/-- Evaluate the theorem's public formulas. The caller supplies root discovery;
all frame, domain, and branch restrictions remain checked on exact values. -/
def discover (recipe : LibraryRecipe)
    (chooseRoot : List K → (K → Bool) → m K) (inputs : Program.State K) : m (Discovery K) := do
  let squareRoot (x : K) := chooseRoot [-x, 0, 1] (fun t => decide (0 ≤ t))
  match recipe with
  | .midpoint =>
    let p ← point inputs 0
    let q ← point inputs 1
    unless inputs.length == 2 do throw "Midpoint requires two points."
    if p = q then throw "Choose two distinct points."
    return ⟨[.point (Midpoint.point p q)], [], []⟩
  | .arithmetic op =>
    let p ← point inputs 5
    let y ← if op.arity == 7 then do pure (← point inputs 6).1 else pure 0
    unless inputs = op.inputs p.1 y do throw "Arithmetic inputs must use the specified coordinate frame and x-axis."
    unless op.Valid p.1 y do throw "The divisor must be nonzero."
    return ⟨[.point (op.value p.1 y, 0)], [], []⟩
  | .measurement op =>
    let p ← point inputs 5
    let q ← if op.arity == 7 then point inputs 6 else pure (0, 0)
    unless inputs = op.inputs p q do throw "Measurement inputs must use the specified coordinate frame."
    let root ← match op with
      | .sqrt =>
        unless p.2 = 0 ∧ 0 ≤ p.1 do throw "Square root requires a nonnegative point on the x-axis."
        squareRoot p.1
      | .cbrt =>
        unless p.2 = 0 do throw "Cube root requires a point on the x-axis."
        chooseRoot [-p.1, 0, 0, 1] (fun _ => true)
      | .distanceX | .distanceY => squareRoot (DistanceRecipe.squared p q)
      | _ => pure 0
    let signs := match op with
      | .sqrt | .distanceX | .distanceY => [root]
      | _ => []
    return ⟨[.point (op.value p root)], [root], signs⟩
  | .trisection =>
    let vertex ← point inputs 5
    let first ← point inputs 6
    let second ← point inputs 7
    unless inputs = TrisectionRecipe.inputs vertex first second do
      throw "Trisection inputs must use the specified coordinate frame."
    if (first-vertex).det (second-vertex) = 0 then
      throw "Trisection requires noncollinear rays."
    let a ← squareRoot (first-vertex).sqNorm
    let b ← squareRoot (second-vertex).sqNorm
    let c := (Trisection.unitVector vertex first a).dot (Trisection.unitVector vertex second b)
    let s ← squareRoot (1-c^2)
    let t ← chooseRoot [-c, -3, 0, 4] (fun t => decide (1/2 < t ∧ t < 1))
    let r ← squareRoot (1-t^2)
    let roots : Trisection.Roots K := ⟨a, b, s, t, r⟩
    let p := roots.firstPoint vertex first second
    let q := roots.secondPoint vertex first second
    if hp : vertex = p then throw "Trisection produced a degenerate first ray."
    else if hq : vertex = q then throw "Trisection produced a degenerate second ray."
    else return ⟨[.point p, .point q, .line (Line.through vertex p hp),
      .line (Line.through vertex q hq)], [a, b, s, t, r], [a, b, s, t-1/2, 1-t, r]⟩

end Formulas

/-- Exact real-root enumeration followed by the specified algebraic branch.
No screen coordinates or floating-point comparisons enter this selection. -/
def chooseRoot (coefficients : List Scalar) (branch : Scalar → Bool) : Except String Scalar := do
  let .finite roots := Scalar.realRoots (Scalar.polynomial coefficients)
    | throw "A library root equation unexpectedly vanished."
  let [root] := roots.filter branch
    | throw "The library root equation did not have exactly one admissible root."
  return root

end LeanOrigami.Widget.LibraryRecipe
