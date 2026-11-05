import RegionCheck
import RegionLoss

set_option autoImplicit false
namespace Contribution.RegionCompiler.Examples

def disconnected : PhysicalSpec Unit ℚ := ⟨.disj
  (.conj (.atom ⟨(),.ge,10⟩) (.atom ⟨(),.le,12⟩))
  (.conj (.neg (.atom ⟨(),.le,18⟩)) (.atom ⟨(),.le,20⟩))⟩

def units : AffineCoordinates Unit ℚ := ⟨fun _ => 10,fun _ => 10,by intro i; norm_num⟩
def point (v : ℚ) : Normalized Unit ℚ := ⟨fun _ => v⟩

theorem retains_second_component : checkNormalized units disconnected (point (9/10)) = true := by
  decide +kernel

theorem excludes_open_boundary : checkNormalized units disconnected (point (4/5)) = false := by
  decide +kernel

theorem excludes_gap : checkNormalized units disconnected (point (1/2)) = false := by
  decide +kernel

theorem includes_closed_boundaries :
    checkNormalized units disconnected (point 0) = true ∧
    checkNormalized units disconnected (point (1/5)) = true ∧
    checkNormalized units disconnected (point 1) = true := by decide +kernel

def enclosingHull : PhysicalSpec Unit ℚ :=
  ⟨.conj (.atom ⟨(),.ge,10⟩) (.atom ⟨(),.le,20⟩)⟩

/-- Deliberate mutant: bounding hull overapproximates the requested region.
This is a soundness control, not an allegation against an existing library. -/
theorem hull_changes_membership :
    checkNormalized units enclosingHull (point (1/2)) = true ∧
    checkNormalized units disconnected (point (1/2)) = false := by decide +kernel

def closedMutant : PhysicalSpec Unit ℚ := ⟨.disj
  (.conj (.atom ⟨(),.ge,10⟩) (.atom ⟨(),.le,12⟩))
  (.conj (.atom ⟨(),.ge,18⟩) (.atom ⟨(),.le,20⟩))⟩

theorem closing_boundary_changes_membership :
    checkNormalized units closedMutant (point (4/5)) = true ∧
    checkNormalized units disconnected (point (4/5)) = false := by decide +kernel

/-- Explicitly rewrapping a normalized specification circumvents the units
type distinction. Ordinary normalizeSpec cannot be applied twice directly. -/
def doubleNormalized : PhysicalSpec Unit ℚ :=
  ⟨(normalizeSpec units disconnected).formula⟩

theorem double_normalization_changes_membership :
    checkNormalized units disconnected (point (1/10)) = true ∧
    checkNormalized units doubleNormalized (point (1/10)) = false := by decide +kernel

theorem dropping_component_changes_membership :
    checkRegion ((compile (normalizeSpec units disconnected).formula).take 1) (point (9/10)).val = false ∧
    checkNormalized units disconnected (point (9/10)) = true := by decide +kernel

def emptySpec : PhysicalSpec Unit ℚ :=
  ⟨.conj (.atom ⟨(),.ge,2⟩) (.atom ⟨(),.le,1⟩)⟩

theorem empty_region_rejects_all (z : Normalized Unit ℚ) :
    checkNormalized units emptySpec z = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hh := (checkNormalized_correct units emptySpec z).mp h
  simp only [emptySpec,Formula.holds,Atom.holds,Comparison.holds] at hh
  linarith [hh.1,hh.2]

theorem strict_hinge_is_not_exact : max (0 : ℚ) (0-0) = 0 ∧ ¬ ((0 : ℚ) < 0) := by norm_num

end Contribution.RegionCompiler.Examples
