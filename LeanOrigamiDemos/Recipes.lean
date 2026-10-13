import LeanOrigami.Widget

/-!
# Creating a recipe and using it in a proof

Place the cursor on `origami_recipe` to view or edit the midpoint recipe
created with the GUI. Its sample points are parameters. Place the cursor on
`origami history` below to view the saved proof built by invoking that recipe.
See docs/recipes.md for creating a new workspace and the complete workflow.
-/

namespace LeanOrigamiDemos.Recipes
open LeanOrigami LeanOrigami.Widget

-- A standalone editing workspace. Its points are sample parameters.
origami_recipe midpoint  samples ([("A", .point (0, 0)), ("B", .point (1, 0))]) saved ({ parameters := #[⟨"A", .point⟩, ⟨"B", .point⟩], steps := [.fold (.axiom1 ⟨0⟩ ⟨1⟩), .fold (.axiom2 ⟨0⟩ ⟨1⟩), .intersect ⟨2⟩ ⟨3⟩], output := 4, groups := #[] })

/-- The GUI-authored midpoint recipe, applied to the proof's seed points.
The saved certificate proves that its x coordinate is one half. -/
theorem half : ConstructibleNumber (1 / 2 : ℝ) := by
  origami history (#[⟨"LeanOrigamiDemos.Recipes.midpoint", 0, 3, #[0, 1], 4⟩]) saved (set_option maxRecDepth 8192 in
  set_option maxHeartbeats 4000000 in
  set_option exponentiation.threshold 8192 in
  open LeanOrigami LeanOrigami.Text Hex in
  by
    let field : LeanOrigami.Scalar.Presentation := ⟨#p[0, 1], ⟨by decide +kernel, by decide +kernel⟩, ⟨⟨⟨0, 0, 12⟩, (@Hex.AtomCertificate.nk (#p[0, 1]) (⟨0, 0, 12⟩) (by decide))⟩, by decide +kernel⟩, by decide +kernel⟩
    let program : LeanOrigami.Program LeanOrigami.Scalar := [
    .fold (LeanOrigami.FoldRequest.axiom1 { index := 0 } { index := 1 }) (⟨0, 1, ((0 : LeanOrigami.Scalar) / 1), Or.inr ⟨rfl, rfl⟩⟩),
    .fold (LeanOrigami.FoldRequest.axiom2 { index := 0 } { index := 1 }) (⟨1, ((0 : LeanOrigami.Scalar) / 1), ((1 : LeanOrigami.Scalar) / 2), Or.inl rfl⟩),
    .intersect ⟨2⟩ ⟨3⟩ (((1 : LeanOrigami.Scalar) / 2), ((0 : LeanOrigami.Scalar) / 1))]
    let target : LeanOrigami.Scalar := ((1 : LeanOrigami.Scalar) / 2)
    have accepted : LeanOrigami.Program.accepts program ⟨4⟩ .x target = true := by
      dsimp only [program, target]
      origami_check using first | origami_coordinates field
    refine ⟨program, ⟨4⟩, .x, target, accepted, ?_⟩
    origami_identify target using first | origami_coordinates field
  )

end LeanOrigamiDemos.Recipes
