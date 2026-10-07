import HexNumberField

/-!
# Phase 0 runtime experiments

Run with `lake exe phase0-runtime`, which builds and links the native
dependencies. These executable assertions exercise the backend; the
kernel-checked semantic results live in `Feasibility.lean`.
-/

open Hex

private def check (label : String) (condition : Bool) : IO Unit := do
  unless condition do throw <| IO.userError s!"FAIL: {label}"
  IO.println s!"PASS: {label}"

private def timed (label : String) (action : IO α) : IO α := do
  IO.println s!"RUN: {label}"
  (← IO.getStdout).flush
  let start ← IO.monoMsNow
  let result ← action
  IO.println s!"TIME: {label}: {(← IO.monoMsNow) - start} ms"
  (← IO.getStdout).flush
  return result

private def finiteRoots (p : AlgebraicPoly) : IO (Array AlgebraicNumber) := do
  match p.roots? with
  | none => throw <| IO.userError "root certificate search failed"
  | some .all => throw <| IO.userError "unexpected zero polynomial"
  | some (.finite roots) => return roots.map (·.root.exact)

/-- Exercise exact arithmetic, real branch filtering, and display conversion. -/
def main : IO Unit := do
  timed "rational arithmetic" do
    let a := AlgebraicNumber.ofRat (2 / 3)
    check "rational inverse" (a * a⁻¹ == 1)
    check "exact order" (decide (a < 1))
  let s₂ ← timed "sqrt(2)" do pure (2 : AlgebraicNumber).sqrt
  let s₃ ← timed "sqrt(3)" do pure (3 : AlgebraicNumber).sqrt
  timed "irrational arithmetic sequence" do
    check "real radicals" (s₂.isReal && s₃.isReal)
    check "positive branch" (decide (0 < s₂))
    check "square root identity" (s₂ ^ 2 == 2)
    check "two-field identity" ((s₂ + s₃) * (s₂ - s₃) == -1)
    check "inverse identity" ((s₂ + s₃)⁻¹ == s₃ - s₂)
  timed "algebraic-coefficient quadratic" do
    let roots ← finiteRoots (AlgebraicPoly.ofArray #[-s₂, 0, 1])
    check "two real roots" (roots.size == 2 && roots.all (·.isReal))
    check "each root squares to sqrt(2)" (roots.all fun r => r ^ 2 == s₂)
    check "one positive and one negative" (roots.any (fun r => decide (0 < r)) &&
      roots.any (fun r => decide (r < 0)))
  timed "cubic real-root filtering" do
    let roots ← finiteRoots (AlgebraicPoly.ofArray #[-2, 0, 0, 1])
    let realRoots := roots.filter (·.isReal)
    check "three complex roots, one real" (roots.size == 3 && realRoots.size == 1)
    check "cube root equation" (realRoots.all fun r => r ^ 3 == 2)
  timed "zero polynomial classification" do
    check "all roots, not empty" (match (AlgebraicPoly.ofArray #[]).roots? with
      | some .all => true
      | _ => false)
  timed "40-bit rendering approximation" do
    let ball := s₂.approx 40
    let q := ball.re.toRat
    let pixelValue := Float.ofInt q.num / Float.ofNat q.den
    check "small certified radius" (decide (ball.radius ≤ Dyadic.ofIntWithPrec 1 40))
    check "useful floating value" (pixelValue > 1.4142 && pixelValue < 1.4143)
    IO.println s!"DISPLAY: sqrt(2) ≈ {pixelValue}"
