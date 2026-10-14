import LeanOrigami.Widget

/-!
# Explore an exact square-root recipe

Place the cursor on `origami_recipe` to open the saved construction. The final
point is (√2, 0). Use Edit samples to replace the scalar input with 0, 4, or -1:
the editor selects the nonnegative root, or reports the failed requirement.
Samples are for exploration; they do not assert constructibility of new seeds.

The same operation menu contains signed coordinate transfers, axis projections,
distances, and real cube roots (including negative inputs).
-/
namespace LeanOrigamiDemos.Measurements
open LeanOrigami LeanOrigami.Widget

/-- Explicit frame and radicand samples; the template contains no sample values. -/
def samples : RecipeSamples :=
  (measurementTemplate .sqrt).parameters.toList.map (·.name) |>.zip
    (MeasurementOperation.inputs .sqrt ((2 : Scalar), 0) (0, 0))

origami_recipe squareRoot samples (samples) saved (measurementTemplate .sqrt)

/-- Built and saved through the widget: construct the standard frame, add one
to one, then take the nonnegative square root. Put the cursor on `origami` to
view or edit the complete construction; Lean checks the saved proof on replay. -/
theorem squareRootTwo : ConstructibleNumber (Real.sqrt 2) := by
  origami history (#[⟨"Addition", 7, 7, #[0, 1, 2, 3, 8, 1, 1], { index := 15, names := #[⟨"Result", 15⟩] }⟩, ⟨"Nonnegative square root", 14, 39, #[0, 1, 2, 3, 8, 15], { index := 54, names := #[⟨"Result", 54⟩] }⟩]) saved (set_option maxRecDepth 8192 in
  set_option maxHeartbeats 4000000 in
  set_option exponentiation.threshold 8192 in
  open LeanOrigami LeanOrigami.Text Hex in
  by
    let field : LeanOrigami.Scalar.Presentation := ⟨#p[-8, 0, 1], ⟨by decide +kernel, by decide +kernel⟩, ⟨⟨⟨((94906265 : _root_.Dyadic) >>> 25), 0, 21⟩, (@Hex.AtomCertificate.nk (#p[-8, 0, 1]) (⟨((94906265 : _root_.Dyadic) >>> 25), 0, 21⟩) (by decide))⟩, by decide +kernel⟩, by decide +kernel⟩
    let program : LeanOrigami.Program LeanOrigami.Scalar := [
    .fold (LeanOrigami.FoldRequest.axiom1 { index := 0 } { index := 1 }) (⟨0, 1, ((0 : LeanOrigami.Scalar) / 1), Or.inr ⟨rfl, rfl⟩⟩),
    .fold (LeanOrigami.FoldRequest.axiom4 { index := 0 } { index := 2 }) (⟨1, ((0 : LeanOrigami.Scalar) / 1), ((0 : LeanOrigami.Scalar) / 1), Or.inl rfl⟩),
    .fold (LeanOrigami.FoldRequest.axiom4 { index := 1 } { index := 2 }) (⟨1, ((0 : LeanOrigami.Scalar) / 1), ((1 : LeanOrigami.Scalar) / 1), Or.inl rfl⟩),
    .fold (LeanOrigami.FoldRequest.axiom5 { index := 1 } { index := 0 } { index := 3 }) (⟨1, ((-1 : LeanOrigami.Scalar) / 1), ((0 : LeanOrigami.Scalar) / 1), Or.inl rfl⟩),
    .intersect ⟨4⟩ ⟨5⟩ (((1 : LeanOrigami.Scalar) / 1), ((1 : LeanOrigami.Scalar) / 1)),
    .fold (LeanOrigami.FoldRequest.axiom4 { index := 6 } { index := 3 }) (⟨0, 1, ((1 : LeanOrigami.Scalar) / 1), Or.inr ⟨rfl, rfl⟩⟩),
    .intersect ⟨3⟩ ⟨7⟩ (((0 : LeanOrigami.Scalar) / 1), ((1 : LeanOrigami.Scalar) / 1)),
    .fold (LeanOrigami.FoldRequest.axiom4 { index := 8 } { index := 3 }) (⟨0, 1, ((1 : LeanOrigami.Scalar) / 1), Or.inr ⟨rfl, rfl⟩⟩),
    .fold (LeanOrigami.FoldRequest.axiom4 { index := 1 } { index := 2 }) (⟨1, ((0 : LeanOrigami.Scalar) / 1), ((1 : LeanOrigami.Scalar) / 1), Or.inl rfl⟩),
    .intersect ⟨10⟩ ⟨9⟩ (((1 : LeanOrigami.Scalar) / 1), ((1 : LeanOrigami.Scalar) / 1)),
    .fold (LeanOrigami.FoldRequest.axiom1 { index := 8 } { index := 1 }) (⟨1, ((1 : LeanOrigami.Scalar) / 1), ((1 : LeanOrigami.Scalar) / 1), Or.inl rfl⟩),
    .fold (LeanOrigami.FoldRequest.axiom4 { index := 11 } { index := 12 }) (⟨1, ((-1 : LeanOrigami.Scalar) / 1), ((0 : LeanOrigami.Scalar) / 1), Or.inl rfl⟩),
    .fold (LeanOrigami.FoldRequest.axiom4 { index := 11 } { index := 13 }) (⟨1, ((1 : LeanOrigami.Scalar) / 1), ((2 : LeanOrigami.Scalar) / 1), Or.inl rfl⟩),
    .intersect ⟨14⟩ ⟨2⟩ (((2 : LeanOrigami.Scalar) / 1), ((0 : LeanOrigami.Scalar) / 1)),
    .fold (LeanOrigami.FoldRequest.axiom4 { index := 8 } { index := 3 }) (⟨0, 1, ((1 : LeanOrigami.Scalar) / 1), Or.inr ⟨rfl, rfl⟩⟩),
    .fold (LeanOrigami.FoldRequest.axiom4 { index := 0 } { index := 2 }) (⟨1, ((0 : LeanOrigami.Scalar) / 1), ((0 : LeanOrigami.Scalar) / 1), Or.inl rfl⟩),
    .intersect ⟨17⟩ ⟨16⟩ (((0 : LeanOrigami.Scalar) / 1), ((1 : LeanOrigami.Scalar) / 1)),
    .fold (LeanOrigami.FoldRequest.axiom4 { index := 1 } { index := 2 }) (⟨1, ((0 : LeanOrigami.Scalar) / 1), ((1 : LeanOrigami.Scalar) / 1), Or.inl rfl⟩),
    .intersect ⟨19⟩ ⟨16⟩ (((1 : LeanOrigami.Scalar) / 1), ((1 : LeanOrigami.Scalar) / 1)),
    .fold (LeanOrigami.FoldRequest.axiom1 { index := 0 } { index := 20 }) (⟨1, ((-1 : LeanOrigami.Scalar) / 1), ((0 : LeanOrigami.Scalar) / 1), Or.inl rfl⟩),
    .fold (LeanOrigami.FoldRequest.axiom4 { index := 18 } { index := 21 }) (⟨1, ((1 : LeanOrigami.Scalar) / 1), ((1 : LeanOrigami.Scalar) / 1), Or.inl rfl⟩),
    .fold (LeanOrigami.FoldRequest.axiom4 { index := 18 } { index := 22 }) (⟨1, ((-1 : LeanOrigami.Scalar) / 1), ((-1 : LeanOrigami.Scalar) / 1), Or.inl rfl⟩),
    .intersect ⟨23⟩ ⟨2⟩ (((-1 : LeanOrigami.Scalar) / 1), ((0 : LeanOrigami.Scalar) / 1)),
    .fold (LeanOrigami.FoldRequest.axiom5 { index := 1 } { index := 0 } { index := 3 }) (⟨1, ((-1 : LeanOrigami.Scalar) / 1), ((0 : LeanOrigami.Scalar) / 1), Or.inl rfl⟩),
    .fold (LeanOrigami.FoldRequest.axiom4 { index := 24 } { index := 2 }) (⟨1, ((0 : LeanOrigami.Scalar) / 1), ((-1 : LeanOrigami.Scalar) / 1), Or.inl rfl⟩),
    .intersect ⟨26⟩ ⟨25⟩ (((-1 : LeanOrigami.Scalar) / 1), ((-1 : LeanOrigami.Scalar) / 1)),
    .fold (LeanOrigami.FoldRequest.axiom4 { index := 27 } { index := 3 }) (⟨0, 1, ((-1 : LeanOrigami.Scalar) / 1), Or.inr ⟨rfl, rfl⟩⟩),
    .intersect ⟨3⟩ ⟨28⟩ (((0 : LeanOrigami.Scalar) / 1), ((-1 : LeanOrigami.Scalar) / 1)),
    .fold (LeanOrigami.FoldRequest.axiom4 { index := 29 } { index := 3 }) (⟨0, 1, ((-1 : LeanOrigami.Scalar) / 1), Or.inr ⟨rfl, rfl⟩⟩),
    .fold (LeanOrigami.FoldRequest.axiom4 { index := 8 } { index := 3 }) (⟨0, 1, ((1 : LeanOrigami.Scalar) / 1), Or.inr ⟨rfl, rfl⟩⟩),
    .fold (LeanOrigami.FoldRequest.axiom4 { index := 0 } { index := 2 }) (⟨1, ((0 : LeanOrigami.Scalar) / 1), ((0 : LeanOrigami.Scalar) / 1), Or.inl rfl⟩),
    .intersect ⟨32⟩ ⟨31⟩ (((0 : LeanOrigami.Scalar) / 1), ((1 : LeanOrigami.Scalar) / 1)),
    .fold (LeanOrigami.FoldRequest.axiom4 { index := 15 } { index := 2 }) (⟨1, ((0 : LeanOrigami.Scalar) / 1), ((2 : LeanOrigami.Scalar) / 1), Or.inl rfl⟩),
    .intersect ⟨34⟩ ⟨31⟩ (((2 : LeanOrigami.Scalar) / 1), ((1 : LeanOrigami.Scalar) / 1)),
    .fold (LeanOrigami.FoldRequest.axiom1 { index := 0 } { index := 35 }) (⟨1, ((-2 : LeanOrigami.Scalar) / 1), ((0 : LeanOrigami.Scalar) / 1), Or.inl rfl⟩),
    .fold (LeanOrigami.FoldRequest.axiom4 { index := 33 } { index := 36 }) (⟨1, ((1 : LeanOrigami.Scalar) / 2), ((1 : LeanOrigami.Scalar) / 2), Or.inl rfl⟩),
    .fold (LeanOrigami.FoldRequest.axiom4 { index := 33 } { index := 37 }) (⟨1, ((-2 : LeanOrigami.Scalar) / 1), ((-2 : LeanOrigami.Scalar) / 1), Or.inl rfl⟩),
    .intersect ⟨38⟩ ⟨2⟩ (((-2 : LeanOrigami.Scalar) / 1), ((0 : LeanOrigami.Scalar) / 1)),
    .fold (LeanOrigami.FoldRequest.axiom5 { index := 1 } { index := 0 } { index := 3 }) (⟨1, ((-1 : LeanOrigami.Scalar) / 1), ((0 : LeanOrigami.Scalar) / 1), Or.inl rfl⟩),
    .fold (LeanOrigami.FoldRequest.axiom4 { index := 39 } { index := 2 }) (⟨1, ((0 : LeanOrigami.Scalar) / 1), ((-2 : LeanOrigami.Scalar) / 1), Or.inl rfl⟩),
    .intersect ⟨41⟩ ⟨40⟩ (((-2 : LeanOrigami.Scalar) / 1), ((-2 : LeanOrigami.Scalar) / 1)),
    .fold (LeanOrigami.FoldRequest.axiom4 { index := 42 } { index := 3 }) (⟨0, 1, ((-2 : LeanOrigami.Scalar) / 1), Or.inr ⟨rfl, rfl⟩⟩),
    .intersect ⟨3⟩ ⟨43⟩ (((0 : LeanOrigami.Scalar) / 1), ((-2 : LeanOrigami.Scalar) / 1)),
    .fold (LeanOrigami.FoldRequest.axiom5 { index := 8 } { index := 44 } { index := 30 }) (⟨1, (field.scalar (Hex.PolyQuot.reduce _ _ (#p[0, (-1 : Rat)/4]))), (field.scalar (Hex.PolyQuot.reduce _ _ (#p[0, (1 : Rat)/2]))), Or.inl rfl⟩),
    .fold (LeanOrigami.FoldRequest.axiom4 { index := 0 } { index := 45 }) (⟨1, (field.scalar (Hex.PolyQuot.reduce _ _ (#p[0, (1 : Rat)/2]))), ((0 : LeanOrigami.Scalar) / 1), Or.inl rfl⟩),
    .fold (LeanOrigami.FoldRequest.axiom4 { index := 0 } { index := 46 }) (⟨1, (field.scalar (Hex.PolyQuot.reduce _ _ (#p[0, (-1 : Rat)/4]))), ((0 : LeanOrigami.Scalar) / 1), Or.inl rfl⟩),
    .fold (LeanOrigami.FoldRequest.axiom4 { index := 1 } { index := 2 }) (⟨1, ((0 : LeanOrigami.Scalar) / 1), ((1 : LeanOrigami.Scalar) / 1), Or.inl rfl⟩),
    .intersect ⟨47⟩ ⟨48⟩ (((1 : LeanOrigami.Scalar) / 1), (field.scalar (Hex.PolyQuot.reduce _ _ (#p[0, (1 : Rat)/2])))),
    .fold (LeanOrigami.FoldRequest.axiom5 { index := 1 } { index := 0 } { index := 3 }) (⟨1, ((-1 : LeanOrigami.Scalar) / 1), ((0 : LeanOrigami.Scalar) / 1), Or.inl rfl⟩),
    .fold (LeanOrigami.FoldRequest.axiom4 { index := 49 } { index := 3 }) (⟨0, 1, (field.scalar (Hex.PolyQuot.reduce _ _ (#p[0, (1 : Rat)/2]))), Or.inr ⟨rfl, rfl⟩⟩),
    .intersect ⟨50⟩ ⟨51⟩ ((field.scalar (Hex.PolyQuot.reduce _ _ (#p[0, (1 : Rat)/2]))), (field.scalar (Hex.PolyQuot.reduce _ _ (#p[0, (1 : Rat)/2])))),
    .fold (LeanOrigami.FoldRequest.axiom4 { index := 52 } { index := 2 }) (⟨1, ((0 : LeanOrigami.Scalar) / 1), (field.scalar (Hex.PolyQuot.reduce _ _ (#p[0, (1 : Rat)/2]))), Or.inl rfl⟩),
    .intersect ⟨53⟩ ⟨2⟩ ((field.scalar (Hex.PolyQuot.reduce _ _ (#p[0, (1 : Rat)/2]))), ((0 : LeanOrigami.Scalar) / 1))]
    let target : LeanOrigami.Scalar := (field.scalar (Hex.PolyQuot.reduce _ _ (#p[0, (1 : Rat)/2])))
    have accepted : LeanOrigami.Program.accepts program ⟨54⟩ .x target = true := by
      dsimp only [program, target]
      origami_check using first | origami_coordinates field
    refine ⟨program, ⟨54⟩, .x, target, accepted, ?_⟩
    origami_identify target using first | origami_coordinates field
  )

#print axioms squareRootTwo

end LeanOrigamiDemos.Measurements
