# Phase 7 checkpoint 4 — angles and trisection

Status: implementation, live checks, and final integration validation passed.
Completion bookkeeping is pending; Phase 7 now also includes checkpoint 5.

## Mathematical meaning and organization

`Geometry/Angles.lean` defines exact 30°, 45°, and 60° relations using dot
products and squared lengths. Unoriented lines use their smaller angle; rays
retain the dot-product sign so an obtuse supplement is rejected. Zero directions
are excluded. `Geometry/AngleSemantics.lean` proves agreement with Mathlib angles.
`Construction/AngleCondition.lean` connects these relations to the existing
polynomial condition checker.

`Geometry/TrisectionModel.lean` defines the root equations and coordinate
formulas. `Geometry/Trisection.lean` proves the full geometric result: for either
orientation of an angle strictly between 0° and 180°, both output endpoints are
one unit from the vertex, strictly inside the angle, and ordered so all three
angle gaps are equal. This is stronger than satisfying a cubic equation.
`Scalar/Trisection.lean` proves the required exact algebraic roots exist.

`Construction/TrisectionRecipe.lean` constructs the lengths, normalized
directions, positive square roots, and the cubic root strictly between 1/2 and 1.
All witnesses are intermediate constructed points, never extra seeds. Its
execution theorem checks the actual primitive folds and intersections.
`Construction/TrisectionCondition.lean` interprets the denominator-cleared output
contract. `Widget/Trisection.lean` supplies branch selection, the four named
outputs, universal completion, and the link from the checked contract to real
geometry. Edited templates cannot retain the built-in proved specification.

The implementation reuses the condition AST, reference checking, root recipes,
and certificate checker. Exact execution does not use real trigonometry or
approximate display coordinates. Tests and the visual demo are separate modules.

## Validation

- Complete LSP diagnostics and targeted builds passed for the new library
  modules. The full library, test, and demo build also passed.
- Named-angle tests cover irrational angles, vertical lines, independently
  signed direction scaling, translated rays, supplements, zero directions,
  and invalid references.
- Trisection tests cover translated/rotated inputs with unequal ray lengths,
  clockwise inputs, exact branch selection under changed samples, all four
  outputs, swapped-output rejection, zero/straight inputs, and edited-template
  specification invalidation. A right-angle sample exports the positive
  coordinate whose square is 3/4.
- Key semantic, condition, existence, execution, contract, and branch theorems
  were audited transitively and use only ordinary Mathlib axioms. The new source
  contains no proof holes, project axioms, or native proof shortcuts.
- Live checks passed in `LeanOrigamiDemos/Trisection.lean`, line 27: the workspace
  opens, all four named outputs and the trisection operation are available,
  clockwise sample edits replay, a zero ray is rejected, and correcting it
  recovers the construction. The requirement editor exposes line/ray modes and
  exactly 30°/45°/60°. A false angle requirement is rejected; removing it recovers
  the recipe. Ray mode explains vertex and supplement conventions.
- Integration validation has passed the interpreters, exact export/replay,
  saved widget and recipe replay, sample workspace, and all ten JavaScript
  suites. Remaining recipe checks and the default trisection export/replay also passed
  (final process exit status 0, confirmed 2026-10-15). The saved theorem reports
  only the ordinary Mathlib axioms. This does not complete the new checkpoint 5.

The full script exposed a template-metadata test that could no longer reduce
through output-name trimming with `decide +kernel`. Its three UI validation
cases now use executable assertions. They pass fresh validation. Geometric
condition tests remain kernel-checked proofs; no mathematical checker or theorem
was weakened. Earlier successful script stages are retained when resuming after
this test-only fix.

## Performance and remaining limitations

The recipe expands to **856 primitive instructions**. This is the cost of its
coordinate-arithmetic implementation, not a lower bound on origami trisection.
The live canvas is crowded. A direct geometric replacement should preserve the
general domain, exact branch guarantees, and both interior outputs. Abe's
construction is a useful starting point: see [Fuchs, §2](https://ems.press/content/serial-article-files/45434).
Grouped display alone does not reduce the construction itself.

The original monolithic execution proof exceeded this 8 GB machine's practical
memory capacity. `Text/Replay.lean` now reduces reference lookups directly,
shares structural normalization, and packages 32-step batches in ordinary
kernel-checked auxiliary theorems. The final execution theorem compiled without
warnings in 518 seconds. Existing arithmetic, coordinate, root, and distance
consumers compile with this refactor. A theorem-local unused-tactic annotation
covers an intentional inspection-only guard; no global linter is disabled.

The saved trisection proof exceeded the former four-million-heartbeat budget.
A bounded sixteen-million-heartbeat replay passed, including its axiom audit.
`Text/Exact.lean` now defines the shared finite budget used by export and widget
checking. Both changed modules pass LSP and targeted builds. The default export
without experimental outer options passed independent replay.
Certification can still take minutes; it is not yet a fast interactive example.

Phase 8 contains the approved design work, including labels, contextual canvas
operations, crease selection, default frames, readable linked requirements,
visibility controls, sample handles, and navigation. It is not implemented by
this checkpoint.

## Editor preservation

The three unsaved editor buffers and existing user changes remain intact.
Arc remains open. Background editor workers temporarily paused during live
checks were resumed. VS Code's Lean server restart was requested through its command palette after
validation finished. The editor confirmed server startup; no intentionally paused
worker remains.
