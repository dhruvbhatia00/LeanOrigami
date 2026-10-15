import LeanOrigami.Construction.Checker
import LeanOrigami.Construction.RootGeometry
import Lean.Elab.Tactic

/-!
# Certificates for the ordinary executable checker

`origami_check` proves `Program.accepts ... = true` one instruction at a time.
It resolves the saved references and proves the actual checker's guards. It
never replaces the program by an unrelated construction proof. The optional
`using` tactic supplies algebraic facts when the default arithmetic is inadequate.
-/

namespace LeanOrigami.Text
open Lean Meta Elab Tactic

/-- Elementary symbolic certificates for saved geometric choices. -/
macro "origami_geometry" : tactic => `(tactic|
  (try rw [FoldInput.axiom3_iff_two_points]
   norm_num [FoldInput.FiniteCondition, FoldInput.Satisfies,
     FoldInput.axiom6FreeDirection, FoldInput.axiom6Polynomial, Univariate.Cubic.IsZero,
     Line.Contains, Line.Perpendicular, Line.perpendicularAlignmentDot,
     Line.reflect, Line.residual, Line.normalSq, Line.chart, Line.horizontal,
     Line.determinant, Line.intersection, Line.pointAt, Line.perpendicularThrough,
     Line.normalize, Coordinate.get, Prod.ext_iff]
   all_goals try first | assumption | positivity | (solve | ring)))

-- Expose list constructors while leaving the contents of each object symbolic.
private partial def listElements (value : Expr) : MetaM (List Expr) := do
  let value ← whnf value
  if value.isAppOf ``List.nil then return []
  unless value.isAppOf ``List.cons do
    throwError "construction did not reduce to a finite list"
  let args := value.getAppArgs
  return (← whnf args[1]!) :: (← listElements args[2]!)

-- Evaluate recipe assembly from the inside out. Reducing a nested state
-- program only at its head duplicates earlier states. Skip scalar values,
-- geometry, types, and proofs: this pass evaluates structure, not Hex arithmetic.
private def normalizeStructure (scalar value : Expr) : MetaM Expr :=
  Prod.fst <$> Meta.transformWithCache value {} (skipInstances := true) (skipConstInApp := true)
    (pre := fun e => do
      if ← isType e then return .done e
      let type ← whnf (← inferType e)
      if type == scalar || type.isAppOf ``Line ||
          (type.isAppOf ``Prod && type.getAppArgs[0]! == scalar) || (← isProp type) then
        return .done e
      return .continue)
    (post := fun e => do
      let result ← whnf e
      return if result == e then .done e else .visit result)

/-- Normalize a named recipe builder throughout the goal, including output
references and the claimed final state. Scalar values and geometry stay opaque;
the kernel checks the resulting definitional conversion. -/
syntax (name := normalizeRecipe) "origami_normalize " ident : tactic

@[tactic normalizeRecipe] def elaborateNormalizeRecipe : Tactic := fun stx => do
  let `(tactic| origami_normalize $builder:ident) := stx | throwUnsupportedSyntax
  let name ← realizeGlobalConstNoOverloadWithInfo builder
  withMainContext do
    let goal ← getMainGoal
    let target ← Meta.transform (← goal.getType) (pre := fun e => do
      if !e.isAppOf name then return .continue
      let args := e.getAppArgs
      if args.isEmpty then throwError "expected a recipe builder with a scalar type argument"
      return .done (← normalizeStructure args[0]! e))
      (post := fun e => pure (.done e.consumeMData))
    replaceMainGoal [← goal.replaceTargetDefEq target]

-- Reduce the lookup itself, without simplifying every geometric object in the
-- state. A resolved constructor can then instantiate the expected input directly.
private def checkReferences : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let some (_, lhs, rhs) := (← goal.getType).consumeMData.eq?
    | throwError "expected reference-resolution equality"
  let result ← whnf lhs
  replaceMainGoal [← goal.replaceTargetDefEq (← mkEq result rhs)]
  evalTactic (← `(tactic| rfl))

private def checkStep (geometry : TSyntax ``Parser.Tactic.tacticSeq) : TacticM Unit := do
  let some (_, lhs, _) := (← (← getMainGoal).getType).consumeMData.eq?
    | throwError "expected instruction equality"
  let instruction ← withMainContext <| whnf lhs.getAppArgs.back!
  if instruction.isAppOf ``Instruction.fold then
    evalTactic (← `(tactic| apply Program.step_fold_eq))
    focusAndDone checkReferences
  else
    evalTactic (← `(tactic| apply Program.step_intersect_eq))
    focusAndDone checkReferences
    focusAndDone checkReferences
  evalTactic (← `(tactic| all_goals ($geometry)))
  let remaining ← getUnsolvedGoals
  unless remaining.isEmpty do
    let details ← (← addMessageContext
      (MessageData.joinSep (remaining.map MessageData.ofGoal) m!"\n")).toString
    throwError "could not certify the saved choice:\n{details}"

/-- Certify one saved primitive choice using the same checker as a full program.
Compositional certificates use this at primitive nodes and fallback leaves. -/
syntax (name := origamiStep) "origami_step" (" using " tacticSeq)? : tactic

@[tactic origamiStep] def elaborateStep : Tactic := fun stx => do
  let `(tactic| origami_step $[using $geometry:tacticSeq]?) := stx | throwUnsupportedSyntax
  focusAndDone (checkStep (geometry.getD (← `(tacticSeq| origami_geometry))))

-- Flatten only the runtime object list. Keeping an ever-growing nest of
-- append expressions makes each later lookup repeat work done by earlier ones.
private def normalizeState (state : Expr) : MetaM Expr := do
  let objects ← listElements state
  let type ← whnf (← inferType state)
  mkListLit type.getAppArgs.back! objects

private partial def checkExecution (geometry : TSyntax ``Parser.Tactic.tacticSeq) (index : Nat) : TacticM Unit := do
  let original ← getMainGoal
  -- Name bounded batches of certificates. Each helper is kernel-checked before
  -- its parent uses it; the kernel need not retain one enormous nested proof.
  let separate := index % 32 == 0
  let goal ← if separate then original.withContext do
      let proof ← mkFreshExprSyntheticOpaqueMVar (← original.getType)
      replaceMainGoal [proof.mvarId!]
      pure proof.mvarId!
    else pure original
  let target ← goal.getType
  let some (_, lhs, rhs) := target.consumeMData.eq? | throwError "expected execution equality"
  let program ← withMainContext do
    let args := lhs.getAppArgs
    let program ← whnf args.back!
    let args := args.set! (args.size-2) (← normalizeState args[args.size-2]!)
    let args := args.set! (args.size-1) program
    replaceMainGoal [← goal.change (← mkEq (mkAppN lhs.getAppFn args) rhs)]
    pure program
  if program.isAppOf ``List.nil then
    evalTactic (← `(tactic| (simp only [Program.execute]; rfl)))
  else if program.isAppOf ``List.cons then
    evalTactic (← `(tactic| apply Program.execute_cons_eq))
    try focusAndDone (checkStep geometry)
    catch error => throwError "Origami instruction {index+1}: {error.toMessageData}"
    checkExecution geometry (index+1)
  else throwError "construction program did not reduce to a finite instruction list"
  if separate then original.withContext do
    let proof ← instantiateMVars (mkMVar goal)
    if proof.hasExprMVar then throwError "primitive certificate contains an unresolved proof obligation"
    let certificate ← mkAuxTheorem (← instantiateMVars target) proof
      (kind? := some `origamiReplay) (cache := false)
    original.assign certificate

/-- Certify a primitive execution from explicitly supplied objects. This is
useful for universal recipe specifications, whose operands are parameters
rather than constructions from the two fixed seeds. The resulting equality
is about the same checker used by concrete submissions. -/
syntax (name := executeCheck) "origami_execute" (" using " tacticSeq)? : tactic

@[tactic executeCheck] def elaborateExecuteCheck : Tactic := fun stx => focus do
  let `(tactic| origami_execute $[using $custom]?) := stx | throwUnsupportedSyntax
  let geometry ← match custom with
    | some tactic => pure tactic
    | none => `(tacticSeq| origami_geometry)
  withMainContext do
    let original ← getMainGoal
    let some (_, lhs, rhs) := (← original.getType).consumeMData.eq?
      | throwError "expected Program.execute ... = .ok ..."
    let lhs := lhs.consumeMData
    unless lhs.isAppOf ``Program.execute do
      throwError "expected Program.execute ... = .ok ..."
    let args := lhs.getAppArgs
    let args := args.set! (args.size-1) (← normalizeStructure args[0]! args.back!)
    replaceMainGoal [← original.replaceTargetDefEq (← mkEq (mkAppN lhs.getAppFn args) rhs)]
  checkExecution geometry 0

/-- Certify the saved program, then its selected coordinate. The same acceptance
proof can be passed directly to `Program.accepts_sound`. -/
syntax (name := check) "origami_check" (" using " tacticSeq)? : tactic

@[tactic check] def elaborateCheck : Tactic := fun stx => focus do
  let `(tactic| origami_check $[using $custom]?) := stx | throwUnsupportedSyntax
  let geometry ← match custom with
    | some tactic => pure tactic
    | none => `(tacticSeq| origami_geometry)
  let original ← getMainGoal
  let saved ← saveState
  let oldMessages := (← Core.getMessageLog).toArray.size
  try Term.withoutErrToSorry <| withoutRecover do
    withMainContext do
      let type ← instantiateMVars (← original.getType)
      let some (_, lhs, rhs) := type.consumeMData.eq?
        | throwError "expected Program.accepts ... = true"
      let lhs := lhs.consumeMData
      unless lhs.isAppOf ``Program.accepts do throwError "expected Program.accepts ... = true"
      let args := lhs.getAppArgs
      let args := args.set! (args.size-4) (← normalizeStructure args[0]! args[args.size-4]!)
      let args := args.set! (args.size-3) (← normalizeStructure args[0]! args[args.size-3]!)
      -- These are definitional reductions; the kernel checks their conversion
      -- with the original goal as part of checking the resulting proof term.
      replaceMainGoal [← original.replaceTargetDefEq (← mkEq (mkAppN lhs.getAppFn args) rhs)]
    evalTactic (← `(tactic| apply Program.accepts_of_run))
    focusAndDone do
      evalTactic (← `(tactic| unfold Program.run))
      checkExecution geometry 0
    try
      focusAndDone checkReferences
      unless (← getUnsolvedGoals).isEmpty do
        focusAndDone <| evalTactic (← `(tactic| ($geometry)))
    catch error => throwError "Origami submission: {error.toMessageData}"
    let proof ← instantiateMVars (mkMVar original)
    if proof.hasSorry || proof.hasMVar then throwError "unfinished construction certificate"
    for constant in proof.getUsedConstants do
      for dependency in (← collectAxioms constant) do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
          throwError "construction certificate depends on unsupported axiom {dependency}"
  catch error =>
    let messages := (← Core.getMessageLog).toArray
    let detail := match (messages.extract oldMessages messages.size).find?
        (fun message => message.severity == .error) with
      | some message => m!"{error.toMessageData}\n{message.data}"
      | none => error.toMessageData
    let detail ← detail.toString
    saved.restore
    throwError "{detail}"

end LeanOrigami.Text
