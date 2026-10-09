import LeanOrigami.Text.Replay
import Lean.Data.Json.FromToJson

/-!
# Persistent, independently replayable proof source

An artifact stores the exact Lean source prefix, including imports, helper
constructions, exact chosen expressions, and their certificates. Capturing the
prefix preserves namespace and notation context without serializing floats or
solver indices. Decoding is data handling, not proof checking: replay the source
with Lean before trusting a loaded artifact. The format is versioned.
-/

namespace LeanOrigami.Text
open Lean Elab Command

/-- A saved construction proof and everything preceding it in its source file. -/
structure Artifact where
  version : Nat
  declaration : String
  source : String
  deriving Repr, BEq, ToJson, FromJson

/-- JSON preserves the source text and exact mathematical expressions verbatim. -/
def Artifact.encode (artifact : Artifact) : String := (toJson artifact).compress

/-- Reject unsupported versions and missing content before handing source to Lean.
Successful decoding does not certify the declaration or its mathematical claims. -/
def Artifact.decode (text : String) : Except String Artifact := do
  let artifact : Artifact ← fromJson? (← Json.parse text)
  if artifact.version != 1 then throw s!"unsupported origami artifact version {artifact.version}"
  if artifact.declaration.isEmpty then throw "missing artifact declaration"
  if artifact.source.isEmpty then throw "missing artifact source"
  return artifact

/-- Save the portable data; no Lean code is executed by this operation. -/
def Artifact.save (artifact : Artifact) (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path artifact.encode

/-- Read data without treating it as a trusted proof. -/
def Artifact.load (path : System.FilePath) : IO Artifact := do
  match Artifact.decode (← IO.FS.readFile path) with
  | .ok artifact => return artifact
  | .error message => throw (IO.userError message)

/-- Write a standalone Lean source file for ordinary kernel-checked replay. -/
def Artifact.writeLean (artifact : Artifact) (path : System.FilePath) : IO Unit := do
  let some nameLiteral := (quote artifact.declaration : TSyntax `term).raw.reprint
    | throw (IO.userError "cannot print artifact declaration")
  IO.FS.writeFile path (artifact.source ++ "\n#origami_verify " ++ nameLiteral ++ "\n")

private def checkDeclaration (declaration : TSyntax `ident) : CommandElabM Name := do
  let name ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo declaration
  let info ← getConstInfo name
  unless info.type.isAppOf ``ConstructibleNumber do
    throwErrorAt declaration "expected a closed ConstructibleNumber theorem"
  let axioms ← liftCoreM <| collectAxioms name
  for dependency in axioms do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
      throwErrorAt declaration "artifact depends on unsupported axiom {dependency}"
  return name

/-- A fresh replay checks that the named result exists, has the promised kind,
and has no unapproved axiom dependency. A decoded JSON record alone proves none
of these facts. The name is parsed as an identifier, never as executable code. -/
elab "#origami_verify " name:str : command => do
  let declaration ← match Parser.runParserCategory (← getEnv) `term name.getString with
    | .ok stx => if stx.isIdent then pure stx else throwError "expected a declaration name"
    | .error message => throwError "invalid declaration name: {message}"
  let _ ← checkDeclaration ⟨declaration⟩

/-- Capture only after closing namespaces and sections, so the source prefix
is a complete file. The declaration must be a closed constructibility theorem
whose transitive axioms are the ordinary Mathlib foundations. -/
private def capture (declaration : TSyntax `ident) (command : Syntax) : CommandElabM Artifact := do
  unless (← getScopes).length == 1 do
    throwError "export at file scope after closing namespaces and sections"
  let name ← checkDeclaration declaration
  let some position := command.getPos? | throwError "artifact needs a source location"
  let source := String.Pos.Raw.extract (← getFileMap).source ⟨0⟩ position
  return ⟨1, name.toString, source⟩

/-- Create a persistent artifact value after its proof has been checked. Saving
and loading use the ordinary `Artifact` IO API and do not require editor state. -/
syntax (name := artifactCommand) "origami_artifact " ident " as " ident : command

@[command_elab artifactCommand] def elaborateArtifact : CommandElab := fun stx => do
  let `(origami_artifact $declaration as $name) := stx | throwUnsupportedSyntax
  let artifact ← capture declaration stx
  elabCommand (← `(def $name : LeanOrigami.Text.Artifact :=
    ⟨1, $(quote artifact.declaration), $(quote artifact.source)⟩))

end LeanOrigami.Text
