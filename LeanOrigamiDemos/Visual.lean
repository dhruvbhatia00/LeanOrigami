import LeanOrigami.Widget
import LeanOrigamiDemos.Roots

/-!
# Reopenable visual proofs and construction starting points

Place the cursor on `origami saved` in `half` or `squareRoot` to view and edit
constructions made through the GUI. Their saved certificates prove the goals.
The remaining bare `origami` examples are starting points: their `all_goals`
fallbacks keep the file checked, but do not certify an unfinished GUI session.
See docs/widget.md for the construction steps and save/reopen workflow.
-/

namespace LeanOrigamiDemos.Visual
open LeanOrigami

/-- Three visual operations construct one half. -/
theorem half : ConstructibleNumber (1 / 2 : ℝ) := by
  origami saved (set_option maxRecDepth 8192 in
  set_option maxHeartbeats 4000000 in
  set_option exponentiation.threshold 8192 in
  open LeanOrigami LeanOrigami.Text Hex in
  by
    let field : LeanOrigami.Scalar.Presentation := ⟨#p[0, 1], ⟨by decide +kernel, by decide +kernel⟩, ⟨⟨⟨0, 0, 12⟩, (@Hex.AtomCertificate.nk (#p[0, 1]) (⟨0, 0, 12⟩) (by decide))⟩, by decide +kernel⟩, by decide +kernel⟩
    let program : LeanOrigami.Program LeanOrigami.Scalar := [
    .fold (LeanOrigami.FoldRequest.axiom1 { index := 0 } { index := 1 }) (⟨0, 1, ((0 : LeanOrigami.Scalar) / 1), Or.inr ⟨rfl, rfl⟩⟩),
    .fold (LeanOrigami.FoldRequest.axiom2 { index := 0 } { index := 1 }) (⟨1, ((0 : LeanOrigami.Scalar) / 1), ((1 : LeanOrigami.Scalar) / 2), Or.inl rfl⟩),
    .intersect ⟨3⟩ ⟨2⟩ (((1 : LeanOrigami.Scalar) / 2), ((0 : LeanOrigami.Scalar) / 1))]
    let target : LeanOrigami.Scalar := ((1 : LeanOrigami.Scalar) / 2)
    have accepted : LeanOrigami.Program.accepts program ⟨4⟩ .x target = true := by
      dsimp only [program, target]
      origami_check using first | origami_coordinates field
    refine ⟨program, ⟨4⟩, .x, target, accepted, ?_⟩
    origami_identify target using first | origami_coordinates field
  )

/-- Select the positive landing when folding (1,1) onto the x-axis. -/
theorem squareRoot : ConstructibleNumber (Real.sqrt 2) := by
  origami saved (set_option maxRecDepth 8192 in
  set_option maxHeartbeats 4000000 in
  set_option exponentiation.threshold 8192 in
  open LeanOrigami LeanOrigami.Text Hex in
  by
    let field : LeanOrigami.Scalar.Presentation := ⟨#p[-2, 0, 1], ⟨by decide +kernel, by decide +kernel⟩, ⟨⟨⟨((11863283 : _root_.Dyadic) >>> 23), 0, 21⟩, (@Hex.AtomCertificate.nk (#p[-2, 0, 1]) (⟨((11863283 : _root_.Dyadic) >>> 23), 0, 21⟩) (by decide))⟩, by decide +kernel⟩, by decide +kernel⟩
    let program : LeanOrigami.Program LeanOrigami.Scalar := [
    .fold (LeanOrigami.FoldRequest.axiom1 { index := 0 } { index := 1 }) (⟨0, 1, ((0 : LeanOrigami.Scalar) / 1), Or.inr ⟨rfl, rfl⟩⟩),
    .fold (LeanOrigami.FoldRequest.axiom4 { index := 0 } { index := 2 }) (⟨1, ((0 : LeanOrigami.Scalar) / 1), ((0 : LeanOrigami.Scalar) / 1), Or.inl rfl⟩),
    .fold (LeanOrigami.FoldRequest.axiom4 { index := 1 } { index := 2 }) (⟨1, ((0 : LeanOrigami.Scalar) / 1), ((1 : LeanOrigami.Scalar) / 1), Or.inl rfl⟩),
    .fold (LeanOrigami.FoldRequest.axiom5 { index := 1 } { index := 0 } { index := 3 }) (⟨1, ((-1 : LeanOrigami.Scalar) / 1), ((0 : LeanOrigami.Scalar) / 1), Or.inl rfl⟩),
    .intersect ⟨4⟩ ⟨5⟩ (((1 : LeanOrigami.Scalar) / 1), ((1 : LeanOrigami.Scalar) / 1)),
    .fold (LeanOrigami.FoldRequest.axiom5 { index := 6 } { index := 0 } { index := 2 }) (⟨1, (field.scalar (Hex.PolyQuot.reduce _ _ (#p[-1, -1]))), ((0 : LeanOrigami.Scalar) / 1), Or.inl rfl⟩),
    .fold (LeanOrigami.FoldRequest.axiom4 { index := 6 } { index := 7 }) (⟨1, (field.scalar (Hex.PolyQuot.reduce _ _ (#p[-1, 1]))), (field.scalar (Hex.PolyQuot.reduce _ _ (#p[0, 1]))), Or.inl rfl⟩),
    .intersect ⟨2⟩ ⟨8⟩ ((field.scalar (Hex.PolyQuot.reduce _ _ (#p[0, 1]))), ((0 : LeanOrigami.Scalar) / 1))]
    let target : LeanOrigami.Scalar := (field.scalar (Hex.PolyQuot.reduce _ _ (#p[0, 1])))
    have accepted : LeanOrigami.Program.accepts program ⟨9⟩ .x target = true := by
      dsimp only [program, target]
      origami_check using first | origami_coordinates field
    refine ⟨program, ⟨9⟩, .x, target, accepted, ?_⟩
    origami_identify target using first | origami_coordinates field
  )

/-- A double alignment constructs the cube root as a crease's slope. -/
theorem cubeRoot : ConstructibleNumber ((2 : ℝ) ^ (1 / (3 : ℝ))) := by
  origami
  all_goals exact Roots.cube_root_two

/-- The three trisection branches can be explored; cosine goal submission is
outside the initial named-target matcher and must report that limitation. -/
theorem trisection : ConstructibleNumber (Real.cos (Real.pi / 9)) := by
  origami
  all_goals exact Roots.trisection_cos

end LeanOrigamiDemos.Visual
