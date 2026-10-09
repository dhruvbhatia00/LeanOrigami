import LeanOrigami.Construction.Roots
import LeanOrigami.Solvers.Candidates

/-!
# Proof-bearing objects for text construction

Each operation checks its particular saved output. These objects carry the
same geometric histories as program replay, but accept symbolic proofs instead
of reducing Hex computations in the kernel. Only the two seed points are free.
-/

namespace LeanOrigami.Text

/-- A named point carries its construction from the original seeds. -/
structure Point where
  value : LeanOrigami.Point ℝ
  constructed : Constructible (.point value)

/-- A named crease carries its construction from the original seeds. -/
structure Line where
  value : LeanOrigami.Line ℝ
  constructed : Constructible (.line value)

/-- A coordinate with construction evidence, reusable as a coefficient. -/
structure Number where
  value : ℝ
  constructed : ConstructibleNumber value

/-- The origin seed. -/
def origin : Point := ⟨(0, 0), .origin⟩

/-- The horizontal unit seed. -/
def unit : Point := ⟨(1, 0), .unit⟩

/-- Proof arguments for a fold retain the references' geometric values. -/
def fold (input : FoldInput ℝ) (available : input.Available Constructible)
    (selected : LeanOrigami.Line ℝ) (legal : input.Legal selected) : Line :=
  ⟨selected, .fold input selected available legal⟩

/-- Rule 1 on the two supplied constructed points. -/
def fold1 (p q : Point) (selected : LeanOrigami.Line ℝ)
    (legal : (FoldInput.axiom1 p.value q.value).Legal selected) : Line :=
  fold _ (by simpa [FoldInput.Available, FoldInput.objects] using
    And.intro p.constructed q.constructed) selected legal

/-- Rule 2 reflects the first constructed point onto the second. -/
def fold2 (p q : Point) (selected : LeanOrigami.Line ℝ)
    (legal : (FoldInput.axiom2 p.value q.value).Legal selected) : Line :=
  fold _ (by simpa [FoldInput.Available, FoldInput.objects] using
    And.intro p.constructed q.constructed) selected legal

/-- Rule 3 selects one of the finite bisectors of two constructed lines. -/
def fold3 (l m : Line) (selected : LeanOrigami.Line ℝ)
    (legal : (FoldInput.axiom3 l.value m.value).Legal selected) : Line :=
  fold _ (by simpa [FoldInput.Available, FoldInput.objects] using
    And.intro l.constructed m.constructed) selected legal

/-- Rule 4 constructs a perpendicular through the supplied point. -/
def fold4 (p : Point) (l : Line) (selected : LeanOrigami.Line ℝ)
    (legal : (FoldInput.axiom4 p.value l.value).Legal selected) : Line :=
  fold _ (by simpa [FoldInput.Available, FoldInput.objects] using
    And.intro p.constructed l.constructed) selected legal

/-- Rule 5 checks the saved crease for the selected landing branch. -/
def fold5 (p q : Point) (l : Line) (selected : LeanOrigami.Line ℝ)
    (legal : (FoldInput.axiom5 p.value q.value l.value).Legal selected) : Line :=
  fold _ (by simpa [FoldInput.Available, FoldInput.objects] using
    And.intro p.constructed (And.intro q.constructed l.constructed)) selected legal

/-- Rule 6 checks both alignments, including finite-choice admissibility. -/
def fold6 (p q : Point) (l m : Line) (selected : LeanOrigami.Line ℝ)
    (legal : (FoldInput.axiom6 p.value q.value l.value m.value).Legal selected) : Line :=
  fold _ (by simpa [FoldInput.Available, FoldInput.objects] using
    And.intro p.constructed (And.intro q.constructed
      (And.intro l.constructed m.constructed))) selected legal

/-- Rule 7 checks its alignment and perpendicularity on the saved crease. -/
def fold7 (p : Point) (l m : Line) (selected : LeanOrigami.Line ℝ)
    (legal : (FoldInput.axiom7 p.value l.value m.value).Legal selected) : Line :=
  fold _ (by simpa [FoldInput.Available, FoldInput.objects] using
    And.intro p.constructed (And.intro l.constructed m.constructed)) selected legal

/-- A saved intersection must lie on both lines, with nonzero determinant. -/
def intersect (l m : Line) (selected : LeanOrigami.Point ℝ)
    (valid : l.value.determinant m.value ≠ 0 ∧
      l.value.Contains selected ∧ m.value.Contains selected) : Point :=
  ⟨selected, Constructible.of_intersection l.constructed m.constructed
    valid.1 valid.2.1 valid.2.2⟩

/-- Select the first coordinate without losing provenance. -/
def x (p : Point) : Number := ⟨p.value.1, ConstructibleNumber.of_x p.constructed⟩

/-- Select the second coordinate without losing provenance. -/
def y (p : Point) : Number := ⟨p.value.2, ConstructibleNumber.of_y p.constructed⟩

/-- Recombine two constructed coordinates. -/
def pair (a b : Number) : Point := ⟨(a.value, b.value),
  ConstructibleNumber.point a.constructed b.constructed⟩

/-- Reusable addition construction. -/
def add (a b : Number) : Number := ⟨a.value+b.value, a.constructed.add b.constructed⟩

/-- Reusable subtraction construction. -/
def sub (a b : Number) : Number := ⟨a.value-b.value, a.constructed.sub b.constructed⟩

/-- Reusable multiplication construction. -/
def mul (a b : Number) : Number := ⟨a.value*b.value, a.constructed.mul b.constructed⟩

/-- Division checks the actual constructed divisor. -/
noncomputable def div (a b : Number) (hne : b.value ≠ 0) : Number :=
  ⟨a.value/b.value, a.constructed.div b.constructed hne⟩

/-- The selected square root includes its sign, not just a polynomial equation. -/
def sqrt (a : Number) (selected : ℝ)
    (valid : 0 ≤ selected ∧ selected^2 = a.value) : Number :=
  ⟨selected, ConstructibleNumber.quadratic_root ConstructibleNumber.one
    ConstructibleNumber.zero a.constructed.neg one_ne_zero (by nlinarith [valid.2])⟩

/-- A selected quadratic root must solve the original equation. -/
def quadratic (a b c : Number) (selected : ℝ)
    (valid : a.value ≠ 0 ∧ a.value*selected^2+b.value*selected+c.value = 0) : Number :=
  ⟨selected, ConstructibleNumber.quadratic_root a.constructed b.constructed c.constructed
    valid.1 valid.2⟩

/-- Every selected real cubic root is constructed from the coefficient histories. -/
def cubic (a b c d : Number) (selected : ℝ)
    (valid : a.value ≠ 0 ∧
      a.value*selected^3+b.value*selected^2+c.value*selected+d.value = 0) : Number :=
  ⟨selected, ConstructibleNumber.cubic_root a.constructed b.constructed c.constructed
    d.constructed valid.1 valid.2⟩

/-- Submission checks the particular saved coordinate against the final target. -/
theorem submit (a : Number) (target : ℝ) (equal : a.value = target) :
    ConstructibleNumber target := equal ▸ a.constructed

end LeanOrigami.Text
