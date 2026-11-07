import RepairReference

/-! Universal directional satisfaction and exact reference quality are
separate components of the same frozen repaired controller. -/
set_option autoImplicit false
namespace Contribution.DirectedRepair
open Contribution.Universal Contribution.Reduction PropertyTransfer

theorem repaired_real_mse_bound :
    mseR (repairedR smallCore) referenceRows ≤ 1476/1000000 := by
  rw [← mse_cast (repairedQ smallCore) (repairedR smallCore) (repaired_cast smallCore)]
  have h : (mseQ (repairedQ smallCore) referenceRows : ℝ) ≤ ((1476/1000000 : ℚ) : ℝ) :=
    Rat.cast_mono repaired_mse_bound
  push_cast at h
  exact h

theorem original_real_mse_bound : (1532/1000000 : ℝ) ≤
    mseR (rawR Adversarial.original) referenceRows := by
  rw [← mse_cast (rawQ Adversarial.original) (rawR Adversarial.original) (raw_cast _)]
  have h : ((1532/1000000 : ℚ) : ℝ) ≤ (mseQ (rawQ Adversarial.original) referenceRows : ℝ) :=
    Rat.cast_mono original_mse_bound
  push_cast at h
  exact h

theorem constant_real_mse_bound : (109/1000 : ℝ) ≤
    mseR (fun _ => 1/2) referenceRows := by
  have h : ∀ xs : List ℚ, ((1/2 : ℚ) : ℝ) = (fun _ : List ℝ => (1/2 : ℝ))
      (xs.map (fun q : ℚ => (q : ℝ))) := by intro xs; norm_num
  rw [← mse_cast (fun _ => 1/2) (fun _ => 1/2) h]
  have h' : ((109/1000 : ℚ) : ℝ) ≤ (mseQ (fun _ => 1/2) referenceRows : ℝ) :=
    Rat.cast_mono constant_mse_bound
  push_cast at h'
  exact h'

theorem reference_quality :
    mseR (repairedR smallCore) referenceRows ≤ mseR (rawR Adversarial.original) referenceRows ∧
    mseR (repairedR smallCore) referenceRows < mseR (fun _ => 1/2) referenceRows := by
  constructor
  · linarith [repaired_real_mse_bound, original_real_mse_bound]
  · linarith [repaired_real_mse_bound, constant_real_mse_bound]

theorem repaired_controller_contract :
    Satisfies (farAbove 2) (fun x => repairedR smallCore x.val) ∧
    Satisfies (farBelow 2) (fun x => repairedR smallCore x.val) ∧
    mseR (repairedR smallCore) referenceRows ≤ mseR (rawR Adversarial.original) referenceRows ∧
    mseR (repairedR smallCore) referenceRows < mseR (fun _ => 1/2) referenceRows :=
  ⟨repaired_above _, repaired_below _, reference_quality⟩

end Contribution.DirectedRepair
