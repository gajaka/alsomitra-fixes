import RegionNormalization

set_option autoImplicit false
namespace Contribution.RegionCompiler

def atomCheck {ι K : Type*} [LinearOrder K] (a : Atom ι K) (x : ι → K) : Bool :=
  match a.cmp with
  | .le => decide (x a.axis ≤ a.cut)
  | .lt => decide (x a.axis < a.cut)
  | .ge => decide (a.cut ≤ x a.axis)
  | .gt => decide (a.cut < x a.axis)

theorem atomCheck_correct {ι K : Type*} [LinearOrder K] (a : Atom ι K) (x : ι → K) :
    atomCheck a x = true ↔ a.holds x := by
  cases a with | mk i cmp cut => cases cmp <;> simp [atomCheck,Atom.holds,Comparison.holds]

def checkRegion {ι K : Type*} [LinearOrder K] (r : Region ι K) (x : ι → K) : Bool :=
  r.any fun c => c.all fun a => atomCheck a x

theorem checkRegion_correct {ι K : Type*} [LinearOrder K] (r : Region ι K) (x : ι → K) :
    checkRegion r x = true ↔ regionHolds r x := by
  simp [checkRegion,regionHolds,cellHolds,atomCheck_correct]

variable {ι K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def checkNormalized (n : AffineCoordinates ι K) (s : PhysicalSpec ι K)
    (z : Normalized ι K) : Bool := checkRegion (compile (normalizeSpec n s).formula) z.val

theorem checkNormalized_correct (n : AffineCoordinates ι K) (s : PhysicalSpec ι K)
    (z : Normalized ι K) :
    checkNormalized n s z = true ↔ s.formula.holds (denormalizePoint n z).val := by
  rw [checkNormalized,checkRegion_correct,pipeline_correct]

/-- A gate for proposed points, not a claim about sampling distribution. -/
def acceptCandidate (n : AffineCoordinates ι K) (s : PhysicalSpec ι K)
    (z : Normalized ι K) : Option (Normalized ι K) :=
  if checkNormalized n s z then some z else none

theorem accept_iff (n : AffineCoordinates ι K) (s : PhysicalSpec ι K)
    (z : Normalized ι K) :
    acceptCandidate n s z = some z ↔ s.formula.holds (denormalizePoint n z).val := by
  simp [acceptCandidate,checkNormalized_correct]

/-- Whole-domain verification over compiled normalized cells is equivalent
to the physical contract for ANY output function and predicate. Neither
side assumes that the neural network satisfies its postcondition. -/
theorem universal_transport {Y : Type*} (n : AffineCoordinates ι K)
    (s : PhysicalSpec ι K) (f : Normalized ι K → Y) (post : Physical ι K → Y → Prop) :
    (∀ z, checkNormalized n s z = true → post (denormalizePoint n z) (f z)) ↔
    (∀ x, s.formula.holds x.val → post x (f (normalizePoint n x))) := by
  constructor
  · intro h x hx
    have hh := h (normalizePoint n x)
      ((checkNormalized_correct n s _).mpr (by simpa [point_roundtrip] using hx))
    simpa only [point_roundtrip] using hh
  · intro h z hz
    have hh := h (denormalizePoint n z) ((checkNormalized_correct n s z).mp hz)
    simpa only [normalized_roundtrip] using hh

/-- Same property for relational/nondeterministic execution, without choosing
an inference backend or assuming determinism. -/
theorem execution_transport {Y : Type*} (n : AffineCoordinates ι K)
    (s : PhysicalSpec ι K) (exec : Normalized ι K → Y → Prop)
    (post : Physical ι K → Y → Prop) :
    (∀ z y, checkNormalized n s z = true → exec z y → post (denormalizePoint n z) y) ↔
    (∀ x y, s.formula.holds x.val → exec (normalizePoint n x) y → post x y) := by
  constructor
  · intro h x y hx he
    have hh := h (normalizePoint n x) y
      ((checkNormalized_correct n s _).mpr (by simpa only [point_roundtrip] using hx)) he
    simpa only [point_roundtrip] using hh
  · intro h z y hz he
    have hh := h (denormalizePoint n z) y ((checkNormalized_correct n s z).mp hz)
      (by simpa only [normalized_roundtrip] using he)
    simpa only [normalized_roundtrip] using hh

end Contribution.RegionCompiler
