#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
# Keep the initial Hex build usable on an 8 GB machine; callers may override.
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"
lake build LeanOrigami LeanOrigamiTests LeanOrigamiDemos phase0-runtime
mkdir -p .lake/phase0
lake exe phase0-runtime
lake env lean --run LeanOrigamiDemos/WidgetHarness.lean > .lake/phase0/widget-edit.json
node --experimental-vm-modules scripts/widget-smoke.mjs
lake env lean .lake/phase0/WidgetReplay.lean
