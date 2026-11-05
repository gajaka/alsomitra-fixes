import RegionCheck
import Property2

set_option autoImplicit false
namespace Contribution.RegionCompiler.Alsomitra
open Contribution.Property2 (Coord Spec Normalizer)

def coords : List Coord := [.vx,.vy,.omega,.theta,.x,.y]

def conjunction {ι K : Type*} (ps : List (Formula ι K)) : Formula ι K :=
  ps.foldr Formula.conj .top

theorem conjunction_correct {ι K : Type*} [LinearOrder K] (ps : List (Formula ι K)) (x : ι → K) :
    (conjunction ps).holds x ↔ ∀ p ∈ ps, p.holds x := by
  induction ps with
  | nil => simp [conjunction,Formula.holds]
  | cons p ps ih =>
    simp [conjunction,Formula.holds] at ih ⊢
    intro _
    exact ih

def domainFormula : Formula Coord ℚ := conjunction (coords.map fun c =>
  .conj (.atom ⟨c,.ge,Contribution.Property2.domainLo c⟩)
        (.atom ⟨c,.le,Contribution.Property2.domainHi c⟩))

theorem domain_correct (x : Coord → ℚ) :
    domainFormula.holds x ↔ Contribution.Property2.InDomain ⟨x⟩ := by
  rw [domainFormula,conjunction_correct]
  simp only [List.forall_mem_map,Formula.holds,Atom.holds,Comparison.holds]
  constructor
  · intro h c
    exact h c (by cases c <;> simp [coords])
  · intro h c _
    exact h c

def propertyFormula (s : Spec) : PhysicalSpec Coord ℚ := ⟨.conj domainFormula
  (.conj (.atom ⟨.y,.ge,-s.anchorX⟩)
    (.conj (.atom ⟨.y,.le,s.bandUpper-s.anchorX⟩)
      (.conj (.atom ⟨.vy,.le,s.velocityUpper⟩) (.atom ⟨.omega,.le,s.angularUpper⟩))))⟩

theorem property_formula_correct (s : Spec) (x : Coord → ℚ) :
    (propertyFormula s).formula.holds x ↔ Contribution.Property2.Pre s ⟨x⟩ := by
  simp only [propertyFormula,Formula.holds,domain_correct,Atom.holds,Comparison.holds,
    Contribution.Property2.Pre]
  constructor
  · rintro ⟨hd,hl,hu,hv,hw⟩
    exact ⟨hd,by linarith,by linarith,hv,hw⟩
  · rintro ⟨hd,hl,hu,hv,hw⟩
    exact ⟨hd,by linarith,by linarith,hv,hw⟩

def coordinates (n : Normalizer) : AffineCoordinates Coord ℚ :=
  ⟨n.offset,n.scale,n.positive⟩

/-- All Property2 anchors and thresholds, all positive input normalizers,
and all rational normalized points, including infeasible specifications. -/
theorem property2_pipeline (s : Spec) (n : Normalizer) (z : Contribution.Property2.Normalized) :
    checkNormalized (coordinates n) (propertyFormula s) ⟨z.val⟩ = true ↔
      Contribution.Property2.Pre s (Contribution.Property2.denormalize n z) := by
  rw [checkNormalized_correct,property_formula_correct]
  rfl

theorem agrees_with_existing_compiler (s : Spec) (n : Normalizer)
    (z : Contribution.Property2.Normalized) :
    checkNormalized (coordinates n) (propertyFormula s) ⟨z.val⟩ = true ↔
      (Contribution.Property2.normalizeBox n (Contribution.Property2.compile s)).Mem z := by
  rw [property2_pipeline,Contribution.Property2.normalized_compile_correct]

end Contribution.RegionCompiler.Alsomitra
