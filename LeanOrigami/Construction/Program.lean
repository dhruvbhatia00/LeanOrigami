import LeanOrigami.Construction.History

/-!
# Replayable construction data

References are zero-based positions in one append-only object list: seeds
occupy positions 0 and 1, and each instruction appends one object. Point and
line reference types distinguish input roles; the checker still checks the
referenced object's actual kind. All seven fold requests are represented.
-/

namespace LeanOrigami

/-- Reference to an earlier point in the common object list. -/
structure PointRef where
  index : Nat
  deriving DecidableEq, Repr

/-- Reference to an earlier line in the common object list. -/
structure LineRef where
  index : Nat
  deriving DecidableEq, Repr

/-- User-selected fold operation with references, independent of its output. -/
inductive FoldRequest where
  | axiom1 (first second : PointRef)
  | axiom2 (source target : PointRef)
  | axiom3 (source target : LineRef)
  | axiom4 (point : PointRef) (perpendicularTo : LineRef)
  | axiom5 (source fixedPoint : PointRef) (target : LineRef)
  | axiom6 (first second : PointRef) (firstTarget secondTarget : LineRef)
  | axiom7 (source : PointRef) (target perpendicularTo : LineRef)
  deriving DecidableEq, Repr

/-- A saved instruction retains the exact selected result, not a branch index. -/
inductive Instruction (K : Type*) [Zero K] [One K] where
  | fold (request : FoldRequest) (selected : Line K)
  | intersect (left right : LineRef) (selected : Point K)

/-- Finite construction instructions, to be replayed from the two fixed seeds. -/
abbrev Program (K : Type*) [Zero K] [One K] := List (Instruction K)

/-- Coordinate chosen from a final constructed point. -/
inductive Coordinate where
  | x | y
  deriving DecidableEq, Repr

/-- Read the selected coordinate without any approximation. -/
def Coordinate.get {K : Type*} (coordinate : Coordinate) (p : Point K) : K :=
  match coordinate with | .x => p.1 | .y => p.2

/-- Geometric rejection and malformed-program errors. Resource exhaustion is
reported by the execution host, never interpreted as one of these conclusions. -/
inductive ConstructionError where
  | missingReference (index : Nat)
  | expectedPoint (index : Nat)
  | expectedLine (index : Nat)
  | unsupportedFold (rule : Nat)
  | coincidentPoints
  | parallelLines
  | coincidentLines
  | incorrectOutput
  | targetMismatch
  deriving DecidableEq, Repr

namespace Object
/-- Interpret coordinates through a field embedding. -/
def map {K L : Type*} [Field K] [Field L] (f : K →+* L) : Object K → Object L
  | .point p => .point (f p.1, f p.2)
  | .line l => .line (l.map f)
end Object

end LeanOrigami
