import LeanOrigami.Construction.AngleCondition

/-!
# Recipe requirement data and authoring

A requirement records the primitive-step boundary at which its references are
available. Input requirements have boundary zero; flattening nested calls shifts
both the boundary and references. Descriptions are generated from the formula,
never trusted as a substitute for its meaning.
-/

namespace LeanOrigami.Widget

/-- A condition checked before a particular primitive step (zero-based).
The final boundary is also allowed, so output contracts can later use this data. -/
structure RecipeRequirement where
  before : Nat := 0
  /-- Start of the owning call; undo removes its checks together. -/
  owner : Nat := 0
  condition : Condition
  deriving Repr

/-- Ordinary Lean source, including exact integer/fraction constants. -/
def conditionExprSource : ConditionExpr → String
  | .constant n d => s!"(.constant ({n}) {d})"
  | .component i field => s!"(.component {i} .{match field with | .x => "x" | .y => "y" | .a => "a" | .b => "b" | .c => "c"})"
  | .add a b => s!"(.add {conditionExprSource a} {conditionExprSource b})"
  | .mul a b => s!"(.mul {conditionExprSource a} {conditionExprSource b})"
  | .neg a => s!"(.neg {conditionExprSource a})"

/-- Serialize only the existing condition language, never arbitrary Lean input. -/
def conditionSource : Condition → String
  | .eq a b => s!"(.eq {conditionExprSource a} {conditionExprSource b})"
  | .le a b => s!"(.le {conditionExprSource a} {conditionExprSource b})"
  | .lt a b => s!"(.lt {conditionExprSource a} {conditionExprSource b})"
  | .and a b => s!"(.and {conditionSource a} {conditionSource b})"
  | .or a b => s!"(.or {conditionSource a} {conditionSource b})"
  | .not a => s!"(.not {conditionSource a})"

private def expressionDescription (name : Nat → String) : ConditionExpr → String
  | .constant n d => if d == 1 then toString n else s!"{n}/{d}"
  | .component i field => s!"{name i}.{match field with | .x => "x" | .y => "y" | .a => "a" | .b => "b" | .c => "c"}"
  | .add a b => s!"({expressionDescription name a} + {expressionDescription name b})"
  | .mul a b => s!"({expressionDescription name a} × {expressionDescription name b})"
  | .neg a => s!"−({expressionDescription name a})"

/-- A faithful readable formula, with caller-provided object names. -/
def conditionDescription (name : Nat → String) : Condition → String
  | .eq a b => s!"{expressionDescription name a} = {expressionDescription name b}"
  | .le a b => s!"{expressionDescription name a} ≤ {expressionDescription name b}"
  | .lt a b => s!"{expressionDescription name a} < {expressionDescription name b}"
  | .and a b => s!"({conditionDescription name a}) and ({conditionDescription name b})"
  | .or a b => s!"({conditionDescription name a}) or ({conditionDescription name b})"
  | .not a => s!"not ({conditionDescription name a})"

/-- Parse exact integer/fraction input shared by samples and requirements. -/
def sampleRational (text : String) : Except String Rat := do
  if text.length > 128 then throw "Use a shorter integer or fraction."
  let pieces := (text.trimAscii.toString.splitOn "/").map (·.trimAscii.toString)
  let parse (s : String) : Except String Int :=
    match s.toInt? with
    | some n => .ok n
    | none => .error "Enter an integer or fraction, such as -2 or 1/3."
  match pieces with
  | [n] => return (← parse n : Int)
  | [n, d] =>
    let numerator ← parse n
    let denominator ← parse d
    if denominator == 0 then throw "A fraction cannot have denominator zero."
    return (numerator : Rat) / (denominator : Rat)
  | _ => throw "Enter an integer or fraction, such as -2 or 1/3."

/-- A small form submission. References in Boolean combinations select existing
requirements; all other references select sample parameters. -/
structure RequirementInput where
  family : String := "distinctPoints"
  references : Array Nat := #[]
  values : Array String := #[]
  deriving Lean.ToJson, Lean.FromJson

/-- Build supported conditions without asking authors for Lean code or decision
instances. Polynomial coefficients are in increasing degree, with rational
constants only; coordinate selectors are `x` or `y`. -/
def RequirementInput.condition (input : RequirementInput) (existing : Array Condition) :
    Except String Condition := do
  let ref (i : Nat) : Except String Nat :=
    match input.references[i]? with
    | some n => .ok n | none => .error "Select every required input."
  let text (i : Nat) : Except String String :=
    match input.values[i]? with
    | some s => .ok s | none => .error "Fill in the required value."
  let rational (i : Nat) : Except String ConditionExpr := do
    let q ← sampleRational (← text i)
    return .constant q.num q.den
  let component : Except String ConditionExpr := do
    let field ← match ← text 0 with
      | "x" => pure Component.x | "y" => pure Component.y
      | _ => throw "Choose the x or y coordinate."
    return .component (← ref 0) field
  let angle : Except String NamedAngle := do
    match ← text 0 with
    | "30" => pure .thirty
    | "45" => pure .fortyFive
    | "60" => pure .sixty
    | _ => throw "Choose a supported exact angle: 30°, 45°, or 60°."
  let old (i : Nat) : Except String Condition := do
    let index ← ref i
    match existing[index]? with
    | some condition => return condition | none => throw "This requirement no longer exists."
  match input.family with
  | "samePoints" => return .samePoint (← ref 0) (← ref 1)
  | "distinctPoints" => return .not (.samePoint (← ref 0) (← ref 1))
  | "sameLines" => return .sameLine (← ref 0) (← ref 1)
  | "distinctLines" => return .not (.sameLine (← ref 0) (← ref 1))
  | "onLine" => return .onLine (← ref 0) (← ref 1)
  | "onXAxis" => return .onXAxis (← ref 0)
  | "onYAxis" => return .onYAxis (← ref 0)
  | "collinear" => return .collinear (← ref 0) (← ref 1) (← ref 2)
  | "parallel" => return .parallel (← ref 0) (← ref 1)
  | "perpendicular" => return .perpendicular (← ref 0) (← ref 1)
  | "lineAngle" => return .lineAngle (← angle) (← ref 0) (← ref 1)
  | "rayAngle" => return .rayAngle (← angle) (← ref 0) (← ref 1) (← ref 2)
  | "coordinateEq" => return .eq (← component) (← rational 1)
  | "coordinateLe" => return .le (← component) (← rational 1)
  | "coordinateLt" => return .lt (← component) (← rational 1)
  | "coordinateGe" => return .le (← rational 1) (← component)
  | "coordinateGt" => return .lt (← rational 1) (← component)
  | "polynomialEq" | "polynomialLe" | "polynomialLt" =>
    let argument ← component
    let coefficients ← ((← text 1).splitOn ",").mapM sampleRational
    if coefficients.length > 32 then throw "Use at most 32 polynomial coefficients."
    let expression := coefficients.foldr (fun q rest =>
      ConditionExpr.add (.constant q.num q.den) (.mul argument rest)) (.constant 0 1)
    let zero := ConditionExpr.constant 0 1
    return if input.family == "polynomialEq" then .eq expression zero
      else if input.family == "polynomialLe" then .le expression zero else .lt expression zero
  | "and" => return .and (← old 0) (← old 1)
  | "or" => return .or (← old 0) (← old 1)
  | "not" => return .not (← old 0)
  | _ => throw "Unknown requirement family."

end LeanOrigami.Widget
