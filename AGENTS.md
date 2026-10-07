# Agent Instructions

## Project purpose

LeanOrigami formalizes origami constructions and supports producing Lean
proofs from explicit construction sequences, eventually through a graphical
interface.

Mathematical correctness includes both proving theorems and checking that
their statements accurately express the intended geometry. A compiling proof
of an inadequate definition does not meet the project goals.

Follow the approved PLAN.md when it exists. Implement and validate work in
coherent increments. Do not silently weaken acceptance criteria or theorem
statements to make a phase pass.

## Lean development workflow

Use the Lean LSP MCP as the primary tool for interactive proof development.

- Use `lean_diagnostic_messages` for errors and warnings in the active file.
- Use `lean_goal` to inspect the proof state before changing tactics.
- Use `lean_hover_info` to inspect declaration signatures and documentation.
- Use `lean_local_search` and the available theorem-search tools to find
  existing results before guessing names or proving duplicate lemmas.
- Use `lean_multi_attempt` for focused tactic experiments when helpful.
- Tool positions use 1-indexed lines and columns.
- The MCP inspects Lean code; use file-editing tools to change it.

### Work in one file at a time

The language server for a file relies on compiled imports. Changes checked
in another file's server may not be visible until those imports are rebuilt.

1. Choose a coherent unit of work in one file.
2. Iterate using that file's LSP diagnostics and proof states.
3. Finish the unit and check the whole file before switching.
4. When switching development to another file, run `lake build` to refresh
   compiled dependencies. Ensure the build includes the modules just changed.
5. Refresh the receiving language server if it still shows stale imports.
   The MCP's `lean_build` tool combines a Lake build with an LSP restart.

Batch related work to make these transitions infrequent. Do not run a
repository build after every proof edit or merely to read another file.

Plan edits in dependency order: finish foundational definitions and lemmas,
build, then work on their consumers. This is a scheduling preference, not a
reason to combine unrelated modules into one large file.

### Interpret diagnostics carefully

- Partial diagnostics or `still_elaborating` mean Lean is still working.
  Wait and query again; do not treat them as success or a failed server.
- An empty result from a failed tool call is not a clean diagnostic report.
- A completed goal at one position does not establish that the whole file
  checks.
- Resolve errors and unfinished proofs before moving on. Address warnings
  introduced by the change; do not disable linters globally to hide them.
- If the MCP is unavailable, use `lake env lean <file>` after building its
  imports, and report the fallback.
- Fetch dependency caches only when needed. Do not routinely clean builds,
  delete caches, or update dependencies during proof iteration.

## Code organization and style

Organize modules by mathematical or implementation responsibility, with
clear namespaces and an acyclic dependency structure.

- Use descriptive names consistent with Lean and Mathlib conventions.
- Give each module a short module docstring describing its purpose.
- Document public definitions, important theorems, and non-obvious
  algorithms. Explain assumptions, invariants, and mathematical meaning.
- Use comments to explain reasoning and design choices, rather than
  narrating each tactic.
- Keep imports focused. Reuse Mathlib and Hex results where appropriate.
- Keep the mathematical foundation independent of tactics and widgets.
- Keep reusable proofs in library modules and demonstrations in separate
  test or example modules.

Prefer refactoring the existing abstraction over adding another wrapper,
alternate implementation, or special-purpose variant. Update callers and
remove obsolete code as part of the refactor.

Wrappers are appropriate when they establish a meaningful abstraction
boundary or provide a useful theorem interface. Do not add wrappers merely
to avoid fixing an unsuitable underlying API.

Extract helpers when they express a reusable fact or clarify a substantial
proof. Avoid speculative generality, duplicate formulas, synonym APIs, and
large collections of trivial forwarding lemmas.

Remove abandoned experiments, temporary diagnostics, and stale comments
before completing a checkpoint.

## Mathematical integrity

Audit definitions before investing heavily in downstream proofs.

- Put essential validity and nondegeneracy conditions in the mathematical
  rules or types, not only in the tactic or GUI.
- Check coincident points, coincident or parallel lines, zero denominators,
  degenerate polynomial equations, and multiple solutions where relevant.
- Ensure geometric statements respect the chosen representation, including
  equivalence of line coefficients under nonzero scaling.
- Distinguish an algebraic number's representation from evidence that it is
  obtainable by permitted origami constructions.
- Keep approximate visualization separate from exact proof evidence.
  Displayed choices must correspond to the exact objects being certified.
- State the connection between executable computations and their
  mathematical interpretation explicitly.

Completed library code, tests, and demos must contain no `sorry`, `admit`,
or unproved project axioms. Temporary proof holes during local development
must be removed before a checkpoint is complete.

Use kernel-checkable proofs for certification. Do not use `native_decide`,
unsafe execution, or external numerical results as substitutes for proof.
Computational search may propose candidates, provided their correctness is
subsequently proved.

Use `lean_verify` or `#print axioms` on key soundness and end-to-end theorems.
Check transitive axiom dependencies; a source scan alone is insufficient.
The ordinary Mathlib foundations are acceptable.

## Tests and demonstrations

Keep tests and runnable examples in separate files that import the public
library API. Production library modules must not import test modules.

Tests should be small, readable, and representative. Their purpose is to
show how the API works and catch specification or integration mistakes,
rather than repeat properties already established by general theorems.

For each new capability, include as appropriate:

- A simple successful example demonstrating its intended use.
- A nontrivial example exercising its distinctive behavior.
- A relevant boundary case or rejection of invalid input.
- A regression example for any bug fixed.

Prioritize examples that can become project demos. Document what each
example constructs or verifies and what a reader should learn from it.
Check exact mathematical conclusions, not merely that a command runs.

For executable components, test behavior not covered by proofs, such as
input handling, serialization, tactic errors, and widget integration.
Keep end-to-end proof examples replayable without interactive GUI state.

Do not place tests permanently inside implementation files for development
convenience. Batch test-file work after the implementation has stabilized
and its imports have been built.

## Build configuration

Use discretion to keep the development build fast.

- The Lake configuration may include or exclude tests from default targets
  as appropriate for the current development stage.
- Prefer explicit test/example targets over repeatedly editing configuration
  simply to toggle tests.
- Ensure every maintained source, test, and demo belongs to a documented
  build or validation path.
- Keep explicit commands for validating everything, even when the default
  build checks only the library.
- CI and phase-completion checks must cover all maintained tests and demos,
  including those omitted from default targets.
- Do not report a passing default build as full validation when relevant
  targets were excluded.

Keep toolchain and dependency versions reproducible. Make dependency changes
deliberately and validate their affected consumers.

## Checkpoint audits

Audit work at the end of each PLAN.md phase, after substantial changes to
foundational definitions or public interfaces, and before declaring a major
feature complete. Break long phases into smaller auditable checkpoints.

At each checkpoint:

1. Compare the implementation against the phase's actual acceptance
   criteria. Identify missing behavior or weakened claims.
2. Review definitions and theorem statements for mathematical fidelity,
   missing assumptions, and unintended triviality.
3. Check organization, names, documentation, duplication, and whether a
   refactor should replace accumulated wrappers or special cases.
4. Validate the library and all relevant separate tests and demos.
5. Inspect proof holes and the axiom dependencies of key results.
6. Review the diff for unrelated edits, dead code, stale documentation, and
   unnecessary build or dependency changes.

Fix issues within the agreed scope before marking the checkpoint complete.
Record a concise audit outcome with the milestone: criteria satisfied,
validation performed, and any remaining limitations. Clearly distinguish
verified results from expectations or untested claims.

Audits are part of normal implementation work and do not themselves require
a user approval round.

## Repository preservation and handoff

Preserve existing user changes. Before the planned repository reset, ensure
the complete previous state is committed, pushed to an archive branch or
tag, and verified against the remote. A cached remote-tracking reference is
not sufficient verification.

Keep progress and handoffs concise: state what works, what was checked, and
what remains. Update the approved plan's progress when appropriate, without
silently changing its scope.
