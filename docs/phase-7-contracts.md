# Phase 7 checkpoint 2 audit

Status: checkpoint 2 complete (2026-10-13); Phase 7 remains open.

## Scope and design

The six arithmetic operations use signed points on the x-axis and an explicit
standard coordinate frame. Addition, subtraction, negation, and multiplication
accept zero/equal operands. Reciprocal and division require a nonzero divisor.
No new geometric construction rule or hidden seed was added.

`ArithmeticRecipe.Computes` proves execution of the existing binary programs
and identifies their actual selected result. `ArithmeticOperation.computes`
extends this to unary operations by supplying the origin or unit point to the
same binary programs. `arithmeticTemplate_steps` and `arithmeticTemplate_output`
connect the GUI templates to those programs for every valid input.

`RecipeContract` separates soundness of a checked completion from existence of
a successful completion on every input in its stated domain. Conditions are
exact formulas, not descriptive strings. The arithmetic contract proves both
claims, and its requirements/timed checks accept the proved witness programs.
The domain is the explicitly stated standard frame with signed axis operands.
A completion also requires the declared input count and point/line kinds.

Branch handling keeps all exact choices that satisfy the currently checkable
conditions. It automatically selects only a singleton; otherwise the user
chooses. Later conditions remain continuation checks, with rejection and
reselection through the existing session snapshots. Arithmetic's only ambiguous
step is its diagonal construction; the policy uniquely specifies `x = y`.
The generic filter has soundness/completeness and singleton theorems, and the
arithmetic diagonal theorem identifies its geometric meaning. The focused
Scalar example connects this policy to complete fold discovery.

The specification badge is associated with the complete serialized library
template, not its name. All six arithmetic operations have contracts. Ordinary
user-authored recipes and the pre-existing midpoint template remain unbadged;
authoring arbitrary universal contract proofs in the GUI is not this milestone.
Changing a current workspace's selected default output hides its badge until
that actual template/output has been recognized again.

Named outputs refer to existing objects. Nested groups, source serialization,
undo, replay, final point selection, and history highlighting retain those
references. The default single output remains available. Existing five-field
history tuples accept plain numeric outputs; new history can additionally
carry names, without rewriting old saved proofs. Rendering data keeps the same
numeric `output` plus an `outputs` array.

## Validation record

- Complete LSP diagnostics passed for the new arithmetic execution proofs,
  six-operation library, arithmetic template contracts, and recipe API.
- The focused arithmetic theorem axiom reports contained only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Browser component regressions passed, including named-output RPCs, multiple
  output highlighting, and removal of a stale specification badge after
  selecting a different output.
- A focused kernel test found the old positional history constructor would
  break when extended with another field. The history result representation
  was revised to preserve that constructor; its regression now passes. The
  deliberately incorrect contract is rejected, and the saved arithmetic proof
  replays with kernel-checkable evidence.
- Targeted widget compilation passed, including a final editor-triggered
  refresh after the contract input-validation change.
- Live VS Code checks passed for the signed product (-1) × 2 = -2, zero-input
  sample replay, exact requirements, the six menu entries and division
  specification, adding a named line beside the point output, and saving and
  reopening both names. Altering the output/template removed the old badge.
  The temporary saved source is archived at `.lake/phase7/Checkpoint2Live.lean`.
- The complete `RecipeContracts.lean` and `ArithmeticRecipes.lean` LSP reports
  passed with no errors or warnings. Native examples cover all six operations,
  signed/zero/equal/irrational inputs, nested arithmetic and undo, invalid
  divisors, stale-badge rejection, named-output grouping/replay, JSON and Lean
  source round-trips, and duplicate-name rejection. The Scalar solver/policy
  proof establishes the exact singleton choice without an enumeration index.
- Nested field inference made the first version of the integration test slow.
  Explicit result types and straightforward reference bindings fixed it.
  No full integrated phase suite has been run.

## Review points

No dependency versions, Hex code, CI configuration, or construction axioms
were changed. The normal saved proof still certifies the expanded primitive
program with kernel-checkable evidence. Native recipe checks remain feedback,
not proof terms. The full phase suite and the remaining coordinate/root/angle
features are reserved for checkpoints 3 and 4.

As in the existing editor, calls with no primitive steps do not create a
history span; their selected existing-object result is still usable. Named
history outputs are attached to calls with actual construction steps.
