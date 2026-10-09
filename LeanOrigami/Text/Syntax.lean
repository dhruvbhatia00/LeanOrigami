import LeanOrigami.Text.Certified
import Lean.Elab.Tactic

/-!
# Named, proof-producing construction commands

`origami` elaborates each saved choice through the proof-bearing API. Names
are local Lean bindings: forward references and wrong object kinds are rejected.
An optional `proving (by ...)` supplies symbolic certificates for difficult
choices. `finish` returns a reusable certified object; `submit` checks a target.
-/

namespace LeanOrigami.Text
open Lean Elab Tactic

/-- Expose saved values without evaluating noncomputable real arithmetic. -/
macro "origami_values" : tactic => `(tactic|
  dsimp (config := { zetaDelta := true, failIfUnchanged := false })
    [Text.origin, Text.unit, Text.fold, Text.fold1, Text.fold2, Text.fold3,
    Text.fold4, Text.fold5, Text.fold6, Text.fold7, Text.intersect, Text.x, Text.y,
    Text.pair, Text.add, Text.sub, Text.mul, Text.div, Text.sqrt, Text.quadratic, Text.cubic])

/-- Default certificate search. Its output is an ordinary kernel-checked proof;
it does not invoke native evaluation or treat solver output as evidence. -/
macro "origami_check" : tactic => `(tactic|
  (origami_values
   all_goals
     try rw [FoldInput.Legal, ← FoldInput.finiteCondition_iff]
     try rw [FoldInput.axiom3_iff_two_points]
     norm_num [FoldInput.FiniteCondition, FoldInput.Satisfies,
       FoldInput.axiom6FreeDirection, FoldInput.axiom6Polynomial, Univariate.Cubic.IsZero,
       LeanOrigami.Line.Contains, LeanOrigami.Line.Perpendicular,
       LeanOrigami.Line.perpendicularAlignmentDot, LeanOrigami.Line.reflect,
       LeanOrigami.Line.residual, LeanOrigami.Line.normalSq, LeanOrigami.Line.chart,
       LeanOrigami.Line.horizontal, LeanOrigami.Line.determinant,
       LeanOrigami.Line.pointAt, Prod.ext_iff]
     all_goals first | positivity | ring | (field_simp; ring) | assumption))

declare_syntax_cat origamiStep
syntax "point " ident " := " ident (ppSpace ident)* (" choose " term)? (" proving " term)? : origamiStep
syntax "line " ident " := " ident (ppSpace ident)* (" choose " term)? (" proving " term)? : origamiStep
syntax "number " ident " := " ident (ppSpace ident)* (" choose " term)? (" proving " term)? : origamiStep
syntax "point " ident " := " "use " term : origamiStep
syntax "line " ident " := " "use " term : origamiStep
syntax "number " ident " := " "use " term : origamiStep
syntax "submit " ident (" proving " term)? : origamiStep
syntax "finish " ident : origamiStep
syntax (name := origami) "origami" ppLine (colGt origamiStep)* : tactic

private def certificate (proof : Option (TSyntax `term)) : TacticM (TSyntax `term) :=
  match proof with
  | some proof => pure proof
  | none => `(by origami_check)

-- Check every instruction, including unused results. A failed nested `by` block
-- can log an error and leave a placeholder instead of throwing an exception.
private def checkEvidence (value : Expr) : MetaM Unit := do
  let value ← instantiateMVars value
  if value.hasSorry || value.hasMVar then
    throwError "instruction has an unfinished certificate"
  for constant in value.getUsedConstants do
    for dependency in (← collectAxioms constant) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "instruction depends on unsupported axiom {dependency}"

private def bind (name : TSyntax `ident) (type value : TSyntax `term) : TacticM Unit := do
  withMainContext do
    if (← getLCtx).findFromUserName? name.getId |>.isSome then
      throwErrorAt name "Origami name '{name.getId}' is already in use"
  evalTactic (← `(tactic| let $name : $type := $value))
  withMainContext do
    let some declaration := (← getLCtx).findFromUserName? name.getId
      | throwError "missing construction binding"
    let some value := declaration.value? | throwError "missing construction value"
    checkEvidence value

-- Operation names are identifiers, not globally reserved Lean keywords. In
-- particular, importing this language must not reserve ordinary names x and y.
private def operation (kind : String) (name op : TSyntax `ident)
    (arguments : Array (TSyntax `ident)) (selected proof : Option (TSyntax `term)) :
    TacticM Unit := do
  let spec : Name × Name × Nat × Bool × Bool ← match kind, op.getId.toString with
    | "point", "origin" => pure (``Text.Point, ``Text.origin, 0, false, false)
    | "point", "unit" => pure (``Text.Point, ``Text.unit, 0, false, false)
    | "point", "pair" => pure (``Text.Point, ``Text.pair, 2, false, false)
    | "point", "intersect" => pure (``Text.Point, ``Text.intersect, 2, true, true)
    | "line", "fold1" => pure (``Text.Line, ``Text.fold1, 2, true, true)
    | "line", "fold2" => pure (``Text.Line, ``Text.fold2, 2, true, true)
    | "line", "fold3" => pure (``Text.Line, ``Text.fold3, 2, true, true)
    | "line", "fold4" => pure (``Text.Line, ``Text.fold4, 2, true, true)
    | "line", "fold5" => pure (``Text.Line, ``Text.fold5, 3, true, true)
    | "line", "fold6" => pure (``Text.Line, ``Text.fold6, 4, true, true)
    | "line", "fold7" => pure (``Text.Line, ``Text.fold7, 3, true, true)
    | "number", "x" => pure (``Text.Number, ``Text.x, 1, false, false)
    | "number", "y" => pure (``Text.Number, ``Text.y, 1, false, false)
    | "number", "add" => pure (``Text.Number, ``Text.add, 2, false, false)
    | "number", "sub" => pure (``Text.Number, ``Text.sub, 2, false, false)
    | "number", "mul" => pure (``Text.Number, ``Text.mul, 2, false, false)
    | "number", "div" => pure (``Text.Number, ``Text.div, 2, false, true)
    | "number", "sqrt" => pure (``Text.Number, ``Text.sqrt, 1, true, true)
    | "number", "quadratic" => pure (``Text.Number, ``Text.quadratic, 3, true, true)
    | "number", "cubic" => pure (``Text.Number, ``Text.cubic, 4, true, true)
    | _, _ => throwErrorAt op "unknown {kind} operation '{op.getId}'"
  let (type, function, arity, needsChoice, needsProof) := spec
  unless arguments.size == arity do
    throwErrorAt op "'{op.getId}' expects {arity} object arguments, received {arguments.size}"
  unless selected.isSome == needsChoice do
    throwErrorAt op (if needsChoice then "missing exact 'choose' value" else "unexpected 'choose' value")
  if proof.isSome && !needsProof then throwErrorAt op "this operation has no proof obligation"
  let mut args : TSyntaxArray `term := arguments.map (fun arg => ⟨arg.raw⟩)
  if let some value := selected then args := args.push value
  if needsProof then args := args.push (← certificate proof)
  bind name ⟨mkCIdent type⟩ (Syntax.mkCApp function args)

private def step (stx : TSyntax `origamiStep) : TacticM Bool := do
  match stx with
  | `(origamiStep| point $n := use $v) => bind n (← `(Text.Point)) v
  | `(origamiStep| line $n := use $v) => bind n (← `(Text.Line)) v
  | `(origamiStep| number $n := use $v) => bind n (← `(Text.Number)) v
  | `(origamiStep| point $n := $op $args* $[choose $v]? $[proving $p]?) =>
    operation "point" n op args v p
  | `(origamiStep| line $n := $op $args* $[choose $v]? $[proving $p]?) =>
    operation "line" n op args v p
  | `(origamiStep| number $n := $op $args* $[choose $v]? $[proving $p]?) =>
    operation "number" n op args v p
  | `(origamiStep| submit $n $[proving $p]?) =>
    evalTactic (← `(tactic| exact Text.submit $n _ $(← certificate p)))
    return true
  | `(origamiStep| finish $n) =>
    evalTactic (← `(tactic| exact $n))
    return true
  | _ => throwUnsupportedSyntax
  return false

/-- Errors retain their instruction number and source location. -/
@[tactic origami] def elaborate : Tactic := fun stx => do
  let instructions := stx[1].getArgs
  for h : i in [:instructions.size] do
    let instruction := instructions[i]
    withRef instruction do
      let saved ← saveState
      let previousMessages := (← Core.getMessageLog).toArray.size
      let goal ← getMainGoal
      try
        let finished ← Term.withoutErrToSorry (withoutRecover (step ⟨instruction⟩))
        if finished then
          goal.withContext <| checkEvidence (mkMVar goal)
        if finished && i+1 != instructions.size then
          throwError "submission or finish must be the final instruction"
        if !finished && i+1 == instructions.size then
          throwError "construction needs a final submit or finish"
      catch error =>
        let messages := (← Core.getMessageLog).toArray
        let detail := match (messages.extract previousMessages messages.size).find?
            (fun message => message.severity == .error) with
          | some message => message.data
          | none => error.toMessageData
        saved.restore
        throwError "Origami instruction {i+1}: {detail}"
  if instructions.isEmpty then throwError "empty origami construction"

end LeanOrigami.Text
