import KernelBounds
import Property2Network
import ReductionExistence

set_option autoImplicit false
namespace Contribution.Frozen
open Contribution.Universal Contribution.Binary32 Contribution.KernelBounds Contribution.Property2

/-- Derives the previous trace hypothesis from primitive nearest rounding and
the specified reduction semantics; there is no assumed per-neuron error. -/
theorem rounded_execution_trace (r : ℝ → ℝ) (hr : CorrectRounding r)
    (xs ys : List ℝ) (hx : InBox exactBox xs) (he : RoundedNetwork r network xs ys) :
    Trace network epsilon xs ys := by
  obtain ⟨a,b,ha,hb,hy⟩ := he
  have hroot := enclosed rootBox exactBox xs root_encloses hx
  have h1 := rounded_layer_trace r hr first rootBox xs a hroot first_safe ha
  have haBox := relu_sound _ _ (layer_sound _ _ _ _ _ _ hroot first_range h1)
  have h2 := rounded_layer_trace r hr second (reluBox firstRange) (a.map relu) b haBox second_safe hb
  have hbBox := relu_sound _ _ (layer_sound _ _ _ _ _ _ haBox second_range h2)
  have h3 := rounded_layer_trace r hr third (reluBox secondRange) (b.map relu) ys hbBox third_safe hy
  have heps : epsilon = (1/1024 : ℚ) := by norm_num [epsilon]
  rw [heps]
  exact ⟨a,b,h1,h2,h3⟩

theorem rounded_all_inputs (r : ℝ → ℝ) (hr : CorrectRounding r)
    (xs ys : List ℝ) (hx : InBox exactBox xs) (he : RoundedNetwork r network xs ys) :
    ∀ y ∈ ys, y ≤ (cap : ℝ) :=
  all_approximate_bound xs ys hx (rounded_execution_trace r hr xs ys hx he)

theorem property2_rounded (r : ℝ → ℝ) (hr : CorrectRounding r)
    (z : Normalized) (ys : List ℝ) (hp : Pre spec (denormalize normalizer z))
    (he : RoundedNetwork r network (realInput z) ys) :
    ∀ y ∈ ys, (181/1000 : ℝ)+(12/1000)*y ≤ 187/1000 :=
  property2_approximate z ys hp
    (rounded_execution_trace r hr _ _ (pre_in_exactBox z hp) he)

theorem rounded_observed_satisfied (r : ℝ → ℝ) (hr : CorrectRounding r)
    (bits : Coord → Nat) (out : Nat) (z : Normalized) (y : ℚ)
    (hz : Contribution.Float32.decodePoint bits = some z)
    (hy : Contribution.Float32.decode out = some y)
    (hp : Pre spec (denormalize normalizer z))
    (he : RoundedNetwork r network (realInput z) [(y : ℝ)]) :
    Contribution.Float32.observe spec normalizer bits out = some .satisfied :=
  observed_satisfied bits out z y hz hy hp
    (rounded_execution_trace r hr _ _ (pre_in_exactBox z hp) he)

theorem rounded_output_length (r : ℝ → ℝ) (xs ys : List ℝ)
    (he : RoundedNetwork r network xs ys) : ys.length = 1 := by
  obtain ⟨a,b,ha,hb,hy⟩ := he
  exact hy.length_eq.symm.trans network_shape.2.2.1

/-- A sanity witness for the semantics and the precondition. This is not a
claim that nearestChoice executes as the installed PyTorch library. -/
theorem rounded_property_nonvacuous :
    ∃ (r : ℝ → ℝ) (z : Normalized) (ys : List ℝ),
      CorrectRounding r ∧ Pre spec (denormalize normalizer z) ∧
      RoundedNetwork r network (realInput z) ys ∧ ys.length = 1 ∧
      ∀ y ∈ ys, (181/1000 : ℝ)+(12/1000)*y ≤ 187/1000 := by
  obtain ⟨ys,he⟩ := network_execution_exists true nearestChoice (realInput center)
    (by simp [realInput])
  exact ⟨nearestChoice,center,ys,nearestChoice_correct,center_admissible,he,
    rounded_output_length _ _ _ he,
    property2_rounded _ nearestChoice_correct center ys center_admissible he⟩

end Contribution.Frozen
