import RegionCheck

/-! ACAS Xu input-region example from arXiv:2505.00466v2, Section 3.2,
Equations (7) and (8). The five coordinates follow the vector printed there.
The finite outer box and affine coordinates below are explicit demonstration
choices; they are not asserted to be a deployed ACAS network's normalization.
No network weights, advisories, or training results are verified here. -/
set_option autoImplicit false

namespace Contribution.RegionCompiler.Acas

inductive Coord where
  | rho | theta | psi | ownSpeed | intruderSpeed
  deriving DecidableEq, Repr

abbrev State := Coord → ℚ

theorem forall_coord (p : Coord → Prop) :
    (∀ i, p i) ↔ p .rho ∧ p .theta ∧ p .psi ∧ p .ownSpeed ∧ p .intruderSpeed := by
  constructor
  · intro h; exact ⟨h _, h _, h _, h _, h _⟩
  · rintro ⟨hr, ht, hp, ho, hi⟩ i
    cases i <;> assumption

def within (lo hi : State) (x : State) : Prop := ∀ i, lo i ≤ x i ∧ x i ≤ hi i

def boxCell (lo hi : State) : Cell Coord ℚ := [
  ⟨.rho, .ge, lo .rho⟩, ⟨.rho, .le, hi .rho⟩,
  ⟨.theta, .ge, lo .theta⟩, ⟨.theta, .le, hi .theta⟩,
  ⟨.psi, .ge, lo .psi⟩, ⟨.psi, .le, hi .psi⟩,
  ⟨.ownSpeed, .ge, lo .ownSpeed⟩, ⟨.ownSpeed, .le, hi .ownSpeed⟩,
  ⟨.intruderSpeed, .ge, lo .intruderSpeed⟩,
  ⟨.intruderSpeed, .le, hi .intruderSpeed⟩]

theorem box_cell_correct (lo hi x : State) :
    cellHolds (boxCell lo hi) x ↔ within lo hi x := by
  simp [boxCell, cellHolds, Atom.holds, Comparison.holds, within, forall_coord]
  tauto

def conjunction (atoms : Cell Coord ℚ) : Formula Coord ℚ :=
  atoms.foldr (fun a rest => .conj (.atom a) rest) .top

theorem conjunction_correct (atoms : Cell Coord ℚ) (x : State) :
    (conjunction atoms).holds x ↔ cellHolds atoms x := by
  induction atoms with
  | nil => simp [conjunction, Formula.holds, cellHolds]
  | cons a rest ih =>
    simp [conjunction, Formula.holds, cellHolds] at ih ⊢
    intro _
    exact ih

/-- Exact rational spelling of 55,947.691 feet in Equation (7). -/
def distanceThreshold : ℚ := 55947691 / 1000

def lower : State
  | .theta | .psi => -1
  | _ => 0

def upper : State
  | .rho => 60000
  | .theta | .psi => 1
  | .ownSpeed | .intruderSpeed => 1200

def domain (x : State) : Prop := within lower upper x

/-- Independent statement of the input condition in Equation (7), within D. -/
def equation7 (x : State) : Prop :=
  domain x ∧ distanceThreshold ≤ x .rho ∧
    1145 ≤ x .ownSpeed ∧ x .intruderSpeed ≤ 60

def source : PhysicalSpec Coord ℚ := ⟨.conj (conjunction (boxCell lower upper))
  (.conj (.atom ⟨.rho, .ge, distanceThreshold⟩)
    (.conj (.atom ⟨.ownSpeed, .ge, 1145⟩)
      (.atom ⟨.intruderSpeed, .le, 60⟩)))⟩

theorem source_correct (x : State) : source.formula.holds x ↔ equation7 x := by
  simp [source, Formula.holds, conjunction_correct, box_cell_correct,
    equation7, domain, Atom.holds, Comparison.holds]

/-- Equation (8) literally puts the intruder's threshold in the lower vector. -/
def printedLower : State
  | .rho => max (lower .rho) distanceThreshold
  | .ownSpeed => max (lower .ownSpeed) 1145
  | .intruderSpeed => max (lower .intruderSpeed) 60
  | i => lower i

def printedRegion : Region Coord ℚ := [boxCell printedLower upper]

def printedPredicate (x : State) : Prop :=
  domain x ∧ distanceThreshold ≤ x .rho ∧
    1145 ≤ x .ownSpeed ∧ 60 ≤ x .intruderSpeed

theorem printed_region_correct (x : State) :
    regionHolds printedRegion x ↔ printedPredicate x := by
  simp only [printedRegion, regionHolds, List.mem_singleton, exists_eq_left,
    box_cell_correct, printedPredicate, domain, within, forall_coord,
    printedLower, max_le_iff]
  tauto

/-- Preserve the intruder's default lower bound and restrict its upper bound. -/
def correctedLower : State
  | .rho => max (lower .rho) distanceThreshold
  | .ownSpeed => max (lower .ownSpeed) 1145
  | i => lower i

def correctedUpper : State
  | .intruderSpeed => min (upper .intruderSpeed) 60
  | i => upper i

def correctedRegion : Region Coord ℚ := [boxCell correctedLower correctedUpper]

theorem corrected_region_correct (x : State) :
    regionHolds correctedRegion x ↔ equation7 x := by
  simp only [correctedRegion, regionHolds, List.mem_singleton, exists_eq_left,
    box_cell_correct, equation7, domain, within, forall_coord,
    correctedLower, correctedUpper, max_le_iff, le_min_iff]
  tauto

def units : AffineCoordinates Coord ℚ :=
  ⟨lower, fun i => upper i - lower i, by intro i; cases i <;> norm_num [upper, lower]⟩

def referenceCheck (n : AffineCoordinates Coord ℚ) (z : Normalized Coord ℚ) : Bool :=
  checkNormalized n source z

def printedCheck (n : AffineCoordinates Coord ℚ) (z : Normalized Coord ℚ) : Bool :=
  checkRegion (normalizeRegion n printedRegion) z.val

def correctedCheck (n : AffineCoordinates Coord ℚ) (z : Normalized Coord ℚ) : Bool :=
  checkRegion (normalizeRegion n correctedRegion) z.val

theorem reference_check_correct (n : AffineCoordinates Coord ℚ) (z : Normalized Coord ℚ) :
    referenceCheck n z = true ↔ equation7 (denormalizePoint n z).val :=
  (checkNormalized_correct n source z).trans (source_correct _)

theorem printed_check_correct (n : AffineCoordinates Coord ℚ) (z : Normalized Coord ℚ) :
    printedCheck n z = true ↔ printedPredicate (denormalizePoint n z).val := by
  rw [printedCheck, checkRegion_correct, normalized_region, printed_region_correct]

theorem corrected_check_correct (n : AffineCoordinates Coord ℚ) (z : Normalized Coord ℚ) :
    correctedCheck n z = true ↔ equation7 (denormalizePoint n z).val := by
  rw [correctedCheck, checkRegion_correct, normalized_region, corrected_region_correct]

/-- The corrected box agrees with the source for every normalized rational
point and every positive affine coordinate transformation, not just the probes. -/
theorem corrected_agrees_everywhere (n : AffineCoordinates Coord ℚ)
    (z : Normalized Coord ℚ) : correctedCheck n z = referenceCheck n z := by
  have h := (corrected_check_correct n z).trans (reference_check_correct n z).symm
  cases hc : correctedCheck n z <;> cases hr : referenceCheck n z <;> simp_all

def point (rho theta psi own intruder : ℚ) : Physical Coord ℚ := ⟨fun
  | .rho => rho
  | .theta => theta
  | .psi => psi
  | .ownSpeed => own
  | .intruderSpeed => intruder⟩

def flight (intruder : ℚ) : Physical Coord ℚ := point 60000 0 0 1200 intruder

theorem loses_valid_input :
    referenceCheck units (normalizePoint units (flight 50)) = true ∧
    printedCheck units (normalizePoint units (flight 50)) = false := by decide +kernel

theorem admits_invalid_input :
    referenceCheck units (normalizePoint units (flight 100)) = false ∧
    printedCheck units (normalizePoint units (flight 100)) = true := by decide +kernel

theorem boundary_agrees :
    referenceCheck units (normalizePoint units (flight 60)) = true ∧
    printedCheck units (normalizePoint units (flight 60)) = true ∧
    correctedCheck units (normalizePoint units (flight 60)) = true := by decide +kernel

theorem outer_domain_retained :
    referenceCheck units (normalizePoint units (flight (-1))) = false ∧
    printedCheck units (normalizePoint units (flight (-1))) = false ∧
    correctedCheck units (normalizePoint units (flight (-1))) = false ∧
    referenceCheck units (normalizePoint units (flight 1201)) = false ∧
    printedCheck units (normalizePoint units (flight 1201)) = false ∧
    correctedCheck units (normalizePoint units (flight 1201)) = false := by decide +kernel

theorem printed_not_equivalent :
    ¬ (∀ z, printedCheck units z = referenceCheck units z) := by
  intro h
  have hx := h (normalizePoint units (flight 50))
  rw [loses_valid_input.1, loses_valid_input.2] at hx
  contradiction

end Contribution.RegionCompiler.Acas
