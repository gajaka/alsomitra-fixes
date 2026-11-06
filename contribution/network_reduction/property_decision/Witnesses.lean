import ExactEvaluation

/-! Exact interior counterexamples at margin 2 for the two concrete
Vehicle requirements, on both original trained checkpoints and reductions. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Contribution.Reduction.PropertyDecision
open Contribution.Universal PropertyTransfer

def belowQ : List ℚ := [1/4,1/4,1/4,1/4,1/4,1/4]
def baselineAboveQ : List ℚ := [1/4,1/2,1/2,1/4,1/4,3/4]
def adversarialAboveQ : List ℚ := [1/8,1/8,7/8,1/8,1/8,7/8]

def belowInput : Input := ⟨belowQ.map (fun q : ℚ => (q : ℝ)), by
  norm_num [belowQ, Adversarial.domain, InBox, Interval.Mem,
    List.replicate_succ, List.forall₂_cons]⟩
def baselineAboveInput : Input := ⟨baselineAboveQ.map (fun q : ℚ => (q : ℝ)), by
  norm_num [baselineAboveQ, Adversarial.domain, InBox, Interval.Mem,
    List.replicate_succ, List.forall₂_cons]⟩
def adversarialAboveInput : Input := ⟨adversarialAboveQ.map (fun q : ℚ => (q : ℝ)), by
  norm_num [adversarialAboveQ, Adversarial.domain, InBox, Interval.Mem,
    List.replicate_succ, List.forall₂_cons]⟩

theorem below_interior : ∀ y ∈ belowInput.val, (0 : ℝ) < y ∧ y < 1 := by
  norm_num [belowInput, belowQ]
theorem baseline_above_interior : ∀ y ∈ baselineAboveInput.val, (0 : ℝ) < y ∧ y < 1 := by
  norm_num [baselineAboveInput, baselineAboveQ]
theorem adversarial_above_interior : ∀ y ∈ adversarialAboveInput.val, (0 : ℝ) < y ∧ y < 1 := by
  norm_num [adversarialAboveInput, adversarialAboveQ]

theorem below_displacement : physicalX belowInput + physicalY belowInput =
    (-310740011735873/16000000000000 : ℝ) := by
  norm_num [physicalX, physicalY, belowInput, belowQ]
theorem baseline_above_displacement : physicalX baselineAboveInput + physicalY baselineAboveInput =
    (1407227465521889/400000000000000 : ℝ) := by
  norm_num [physicalX, physicalY, baselineAboveInput, baselineAboveQ]
theorem adversarial_above_displacement : physicalX adversarialAboveInput + physicalY adversarialAboveInput =
    (16395445941148373/4000000000000000 : ℝ) := by
  norm_num [physicalX, physicalY, adversarialAboveInput, adversarialAboveQ]

theorem below_pre : (farBelow 2).pre belowInput := by
  change physicalY belowInput ≤ -physicalX belowInput - 2
  linarith [below_displacement]
theorem baseline_above_pre : (farAbove 2).pre baselineAboveInput := by
  change physicalY baselineAboveInput ≥ -physicalX baselineAboveInput + 2
  linarith [baseline_above_displacement]
theorem adversarial_above_pre : (farAbove 2).pre adversarialAboveInput := by
  change physicalY adversarialAboveInput ≥ -physicalX adversarialAboveInput + 2
  linarith [adversarial_above_displacement]

theorem baseline_below_computed : evalQ Baseline.original belowQ =
    [14786350527961685237583/18889465931478580854784] := by decide +kernel
theorem baseline_above_computed : evalQ Baseline.original baselineAboveQ =
    [7539692050513325688975/18889465931478580854784] := by decide +kernel
theorem adversarial_below_computed : evalQ Adversarial.original belowQ =
    [5436513554077876856478061/4835703278458516698824704] := by decide +kernel
theorem adversarial_above_computed : evalQ Adversarial.original adversarialAboveQ =
    [2662054634994919894468397/9671406556917033397649408] := by decide +kernel

theorem baseline_below_output : output Baseline.original belowInput =
    (14786350527961685237583/18889465931478580854784 : ℝ) := by
  have h := exact_output _ belowInput belowQ _ rfl baseline_below_computed
  norm_num at h ⊢
  exact h
theorem baseline_above_output : output Baseline.original baselineAboveInput =
    (7539692050513325688975/18889465931478580854784 : ℝ) := by
  have h := exact_output _ baselineAboveInput baselineAboveQ _ rfl baseline_above_computed
  norm_num at h ⊢
  exact h
theorem adversarial_below_output : output Adversarial.original belowInput =
    (5436513554077876856478061/4835703278458516698824704 : ℝ) := by
  have h := exact_output _ belowInput belowQ _ rfl adversarial_below_computed
  norm_num at h ⊢
  exact h
theorem adversarial_above_output : output Adversarial.original adversarialAboveInput =
    (2662054634994919894468397/9671406556917033397649408 : ℝ) := by
  have h := exact_output _ adversarialAboveInput adversarialAboveQ _ rfl adversarial_above_computed
  norm_num at h ⊢
  exact h

theorem baseline_below_violation : ViolatesAt (farBelow 2) (output Baseline.original) belowInput := by
  refine ⟨below_pre, ?_⟩
  change ¬ output Baseline.original belowInput ≤ (1/2 : ℝ)
  rw [baseline_below_output]
  norm_num
theorem baseline_above_violation : ViolatesAt (farAbove 2) (output Baseline.original) baselineAboveInput := by
  refine ⟨baseline_above_pre, ?_⟩
  change ¬ (1/2 : ℝ) ≤ output Baseline.original baselineAboveInput
  rw [baseline_above_output]
  norm_num
theorem adversarial_below_violation : ViolatesAt (farBelow 2) (output Adversarial.original) belowInput := by
  refine ⟨below_pre, ?_⟩
  change ¬ output Adversarial.original belowInput ≤ (1/2 : ℝ)
  rw [adversarial_below_output]
  norm_num
theorem adversarial_above_violation : ViolatesAt (farAbove 2) (output Adversarial.original) adversarialAboveInput := by
  refine ⟨adversarial_above_pre, ?_⟩
  change ¬ (1/2 : ℝ) ≤ output Adversarial.original adversarialAboveInput
  rw [adversarial_above_output]
  norm_num

theorem baseline_below_reduced_violation : ViolatesAt (farBelow 2) (output Baseline.reduced) belowInput :=
  (baseline_counterexample _ _).mpr baseline_below_violation
theorem baseline_above_reduced_violation : ViolatesAt (farAbove 2) (output Baseline.reduced) baselineAboveInput :=
  (baseline_counterexample _ _).mpr baseline_above_violation
theorem adversarial_below_reduced_violation : ViolatesAt (farBelow 2) (output Adversarial.reduced) belowInput :=
  (adversarial_counterexample _ _).mpr adversarial_below_violation
theorem adversarial_above_reduced_violation : ViolatesAt (farAbove 2) (output Adversarial.reduced) adversarialAboveInput :=
  (adversarial_counterexample _ _).mpr adversarial_above_violation

theorem baseline_below_refuted : ¬ Satisfies (farBelow 2) (output Baseline.original) :=
  refutes baseline_below_violation
theorem baseline_above_refuted : ¬ Satisfies (farAbove 2) (output Baseline.original) :=
  refutes baseline_above_violation
theorem adversarial_below_refuted : ¬ Satisfies (farBelow 2) (output Adversarial.original) :=
  refutes adversarial_below_violation
theorem adversarial_above_refuted : ¬ Satisfies (farAbove 2) (output Adversarial.original) :=
  refutes adversarial_above_violation

theorem baseline_below_reduced_refuted : ¬ Satisfies (farBelow 2) (output Baseline.reduced) :=
  refutes baseline_below_reduced_violation
theorem baseline_above_reduced_refuted : ¬ Satisfies (farAbove 2) (output Baseline.reduced) :=
  refutes baseline_above_reduced_violation
theorem adversarial_below_reduced_refuted : ¬ Satisfies (farBelow 2) (output Adversarial.reduced) :=
  refutes adversarial_below_reduced_violation
theorem adversarial_above_reduced_refuted : ¬ Satisfies (farAbove 2) (output Adversarial.reduced) :=
  refutes adversarial_above_reduced_violation

end Contribution.Reduction.PropertyDecision
