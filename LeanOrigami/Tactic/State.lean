import Lean
import LeanOrigami.ConstructibleLemmas

/-!
# Meta-level paper state

These structures are bookkeeping for the tactic.  They are not part of the
mathematical kernel; they record the Lean expressions and proof terms that the
DSL has introduced so far.
-/

open Lean

structure PaperPoint where
  name : Name
  expr : Expr
  proof : Expr
  facts : Array (Name × Expr) := #[]

structure PaperLine where
  name : Name
  expr : Expr
  proof : Expr
  validProof : Expr
  facts : Array (Name × Expr) := #[]

structure PaperState where
  points : NameMap PaperPoint
  lines : NameMap PaperLine
  facts : Array (Name × Expr) := #[]

namespace PaperState

def empty : PaperState :=
  { points := {}, lines := {}, facts := #[] }

def insertPoint (st : PaperState) (p : PaperPoint) : PaperState :=
  { st with points := st.points.insert p.name p }

def insertLine (st : PaperState) (l : PaperLine) : PaperState :=
  { st with lines := st.lines.insert l.name l }

def findPoint? (st : PaperState) (n : Name) : Option PaperPoint :=
  NameMap.find? st.points n

def findLine? (st : PaperState) (n : Name) : Option PaperLine :=
  NameMap.find? st.lines n

def insertFact (st : PaperState) (n : Name) (e : Expr) : PaperState :=
  { st with facts := st.facts.push (n, e) }

end PaperState

