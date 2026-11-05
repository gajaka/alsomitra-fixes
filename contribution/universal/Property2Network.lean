import FrozenCertificate

set_option autoImplicit false
namespace Contribution.Frozen
open Contribution.Universal Contribution.Property2

/-- Real interpretation of the six normalized rational coordinates. -/
def realInput (z : Normalized) : List ℝ :=
  [z.val .vx,z.val .vy,z.val .omega,z.val .theta,z.val .x,z.val .y]

theorem pre_in_exactBox (z : Normalized) (hp : Pre spec (denormalize normalizer z)) :
    InBox exactBox (realInput z) := by
  have h := (normalized_compile_correct spec normalizer z).mpr hp
  have hh (c : Coord) :
      Interval.Mem ⟨(normalizeBox normalizer (compile spec)).lo.val c,
        (normalizeBox normalizer (compile spec)).hi.val c⟩ (z.val c : ℝ) := by
    constructor
    · exact_mod_cast (h c).1
    · exact_mod_cast (h c).2
  exact .cons (hh .vx) (.cons (hh .vy) (.cons (hh .omega)
    (.cons (hh .theta) (.cons (hh .x) (.cons (hh .y) .nil)))))

/-- Universal Property2 for the fixed real affine/ReLU interpretation of the
captured float32 parameters, in physical output units. -/
theorem property2_exact (z : Normalized) (hp : Pre spec (denormalize normalizer z)) :
    ∀ y ∈ network.eval (realInput z), (181/1000 : ℝ) + (12/1000)*y ≤ 187/1000 := by
  intro y hy
  have h := all_exact_inputs _ (pre_in_exactBox z hp) y hy
  linarith

/-- Robust universal result. A separate implementation refinement must justify
this explicit per-neuron error hypothesis for a chosen execution backend. -/
theorem property2_approximate (z : Normalized) (ys : List ℝ)
    (hp : Pre spec (denormalize normalizer z)) (ht : Trace network epsilon (realInput z) ys) :
    ∀ y ∈ ys, (181/1000 : ℝ) + (12/1000)*y ≤ 187/1000 := by
  intro y hy
  have h := all_approximate_inputs _ _ (pre_in_exactBox z hp) ht y hy
  linarith

/-- Connection back to the existing binary32 monitor, conditional on the
stated execution trace relation. No PyTorch trace axiom is introduced. -/
theorem observed_satisfied (bits : Coord → Nat) (out : Nat) (z : Normalized) (y : ℚ)
    (hz : Contribution.Float32.decodePoint bits = some z)
    (hy : Contribution.Float32.decode out = some y)
    (hp : Pre spec (denormalize normalizer z))
    (ht : Trace network epsilon (realInput z) [(y : ℝ)]) :
    Contribution.Float32.observe spec normalizer bits out = some .satisfied := by
  apply (Contribution.Float32.observe_satisfied_iff spec normalizer bits out).mpr
  refine ⟨z,y,hz,hy,hp,?_⟩
  apply (output_threshold_correct y).mpr
  have h := all_approximate_inputs _ _ (pre_in_exactBox z hp) ht (y : ℝ) (List.mem_singleton_self _)
  have hc : ((1/2 : ℚ) : ℝ) = (1/2 : ℝ) := by norm_num
  have hh : (y : ℝ) ≤ ((1/2 : ℚ) : ℝ) := by simpa only [hc] using h
  exact Rat.cast_le.mp hh

theorem property2_region_nonempty : ∃ z, Pre spec (denormalize normalizer z) :=
  ⟨center,center_admissible⟩

end Contribution.Frozen
