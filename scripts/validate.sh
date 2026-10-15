#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
# Keep the initial Hex build usable on an 8 GB machine; callers may override.
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"
lake build LeanOrigami LeanOrigami.Text LeanOrigamiTests LeanOrigamiDemos phase0-runtime
mkdir -p .lake/phase0
lake exe phase0-runtime
lake lean LeanOrigamiTests/Interpreter.lean
lake lean LeanOrigamiTests/RootInterpreter.lean
lake env lean --run LeanOrigamiDemos/WidgetHarness.lean > .lake/phase0/widget-edit.json
node --experimental-vm-modules scripts/widget-smoke.mjs
lake env lean .lake/phase0/WidgetReplay.lean

# Round-trip exact text artifacts and check the saved proof in a fresh process.
lake env lean LeanOrigamiTests/TextPersistence.lean
lake env lean .lake/phase5/TextReplay.lean

# Discover exact branches, export their field certificates, and replay independently.
lake lean LeanOrigamiTests/ExactExport.lean -- --run LeanOrigamiTests/ExactExport.lean
lake lean .lake/exact/Replay.lean

# Exercise exact widget editing, then replay named-goal proofs independently.
node --experimental-vm-modules scripts/widget-construction-test.mjs
lake lean LeanOrigamiTests/WidgetRuntime.lean -- --run LeanOrigamiTests/WidgetRuntime.lean
lake lean .lake/phase6/Saved.lean

# Parameterized recipes: execution on new inputs and independent saved-proof replay.
lake lean LeanOrigamiTests/RecipeRuntime.lean -- --run LeanOrigamiTests/RecipeRuntime.lean
lake lean .lake/recipes/Replay.lean

# GUI sample setup, changed-input replay, and exact sample persistence.
lake lean LeanOrigamiTests/SampleWorkspace.lean -- --run LeanOrigamiTests/SampleWorkspace.lean

# Exact condition proofs and focused recipe requirement integration.
lake lean LeanOrigamiTests/Conditions.lean
lake lean LeanOrigamiTests/RecipeRequirements.lean
lake lean LeanOrigamiTests/RecipeContracts.lean
lake lean LeanOrigamiTests/ArithmeticRecipes.lean
lake lean LeanOrigamiTests/MeasurementRecipes.lean
lake lean LeanOrigamiTests/Angles.lean
lake lean LeanOrigamiTests/Trisection.lean
lake lean LeanOrigamiTests/TrisectionRecipes.lean -- --run LeanOrigamiTests/TrisectionRecipes.lean
lake lean .lake/phase7/TrisectionReplay.lean

# Retained calls: theorem reuse, edited fallback, and public multi-output proofs.
lake lean LeanOrigamiTests/CompositionExport.lean -- --run LeanOrigamiTests/CompositionExport.lean
lake lean .lake/composition/Replay.lean
