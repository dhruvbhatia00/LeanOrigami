import LeanOrigami.Widget

/-!
# Two midpoint calls and an ordinary fold

Place the cursor on `origami` below to reopen the saved proof.
The caller has the two seed points, a midpoint, a quarter point, and one crease.
Use Inspect beside either midpoint in the history to see its private folds;
Return to construction restores the editable public scene.

The certificate applies the midpoint theorem twice. It does not replay those
private folds. Only the final ordinary fold uses the primitive checker.
-/
namespace LeanOrigami.Demos.ComposedRecipes

theorem quarter : LeanOrigami.ConstructibleNumber ((1/4 : ℝ)) := by
  origami history (#[⟨"Midpoint", 0, 1, #[0, 1], { index := 2, names := #[⟨"Result", 2⟩] }⟩, ⟨"Midpoint again", 1, 1, #[0, 2], { index := 3, names := #[⟨"Result", 3⟩] }⟩]) composed (set_option maxRecDepth 8192 in
  set_option maxHeartbeats 16000000 in
  set_option exponentiation.threshold 8192 in
  open LeanOrigami LeanOrigami.Text LeanOrigami.Widget Hex in
  by
    let field : Scalar.Presentation := ⟨#p[0, 1], ⟨by decide +kernel, by decide +kernel⟩, ⟨⟨⟨0, 0, 12⟩, (@Hex.AtomCertificate.nk (#p[0, 1]) (⟨0, 0, 12⟩) (by decide))⟩, by decide +kernel⟩, by decide +kernel⟩
    let history : Execution.History Scalar := [Execution.Step.call "Midpoint" (midpointRecipe) (#[0, 1]) ([.point ((((1 : LeanOrigami.Scalar) / 2), (0 : LeanOrigami.Scalar)))]) ([]),
  Execution.Step.call "Midpoint again" (midpointRecipe) (#[0, 2]) ([.point ((((1 : LeanOrigami.Scalar) / 4), (0 : LeanOrigami.Scalar)))]) ([]),
  Execution.Step.primitive (.fold (LeanOrigami.FoldRequest.axiom1 { index := 0 } { index := 3 }) (⟨0, 1, (0 : LeanOrigami.Scalar), Or.inr ⟨rfl, rfl⟩⟩))]
    let final : Program.State Scalar := [.point (((0 : LeanOrigami.Scalar), (0 : LeanOrigami.Scalar))), .point (((1 : LeanOrigami.Scalar), (0 : LeanOrigami.Scalar))), .point ((((1 : LeanOrigami.Scalar) / 2), (0 : LeanOrigami.Scalar))), .point ((((1 : LeanOrigami.Scalar) / 4), (0 : LeanOrigami.Scalar))), .line (⟨0, 1, (0 : LeanOrigami.Scalar), Or.inr ⟨rfl, rfl⟩⟩)]
    let target : Scalar := ((1 : LeanOrigami.Scalar) / 4)
    refine ⟨history, final, ⟨3⟩, .x, target, ?_, ?_, ?_⟩
    · dsimp only [history, final]
      apply Composition.Certified.cons
      · refine Composition.Checked.call _ _ ([.point (((0 : LeanOrigami.Scalar), (0 : LeanOrigami.Scalar))), .point (((1 : LeanOrigami.Scalar), (0 : LeanOrigami.Scalar)))]) _ _ rfl rfl ?_
        refine Or.inl ⟨rfl, ?_⟩
        refine ⟨_, _, rfl, ?_, ?_⟩
        · first | origami_coordinates field
        · simp only [Midpoint.point, List.cons.injEq, Object.point.injEq, and_true, Prod.ext_iff]
          first | origami_coordinates field
      apply Composition.Certified.cons
      · refine Composition.Checked.call _ _ ([.point (((0 : LeanOrigami.Scalar), (0 : LeanOrigami.Scalar))), .point ((((1 : LeanOrigami.Scalar) / 2), (0 : LeanOrigami.Scalar)))]) _ _ rfl rfl ?_
        refine Or.inl ⟨rfl, ?_⟩
        refine ⟨_, _, rfl, ?_, ?_⟩
        · first | origami_coordinates field
        · simp only [Midpoint.point, List.cons.injEq, Object.point.injEq, and_true, Prod.ext_iff]
          first | origami_coordinates field
      apply Composition.Certified.cons
      · exact Composition.Checked.primitive _ _ (by origami_step using first | origami_coordinates field)
      exact Composition.Certified.nil _
    · exact ⟨_, rfl, rfl⟩
    · origami_identify target using first | origami_coordinates field
  )

end LeanOrigami.Demos.ComposedRecipes
