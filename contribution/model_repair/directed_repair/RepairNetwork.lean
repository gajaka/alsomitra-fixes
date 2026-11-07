import RepairedCore

/-! Connection to the existing checkpoint semantics and directional predicates. -/
set_option autoImplicit false
namespace Contribution.DirectedRepair
open Contribution.Universal Contribution.Reduction PropertyTransfer PropertyDecision

def displacementQ (xs : List ℚ) : ℚ :=
  (41232296222734604/1000000000000000 : ℚ)*xs.getD 4 0 +
  482420778264618/1000000000000000 +
  (45878638794593570/1000000000000000 : ℚ)*xs.getD 5 0 -
  41681405266088724/1000000000000000

noncomputable def displacementR (xs : List ℝ) : ℝ :=
  (41232296222734604/1000000000000000 : ℝ)*xs.getD 4 0 +
  482420778264618/1000000000000000 +
  (45878638794593570/1000000000000000 : ℝ)*xs.getD 5 0 -
  41681405266088724/1000000000000000

def rawQ (net : Network) (xs : List ℚ) : ℚ := (evalQ net xs).headD 0
noncomputable def rawR (net : Network) (xs : List ℝ) : ℝ := (eval net xs).headD 0
def repairedQ (net : Network) (xs : List ℚ) : ℚ :=
  projectQ 64 (displacementQ xs) (rawQ net xs)
noncomputable def repairedR (net : Network) (xs : List ℝ) : ℝ :=
  project 64 (displacementR xs) (rawR net xs)

theorem displacement_cast (xs : List ℚ) :
    (displacementQ xs : ℝ) = displacementR (xs.map (fun q : ℚ => (q : ℝ))) := by
  have hg (i : ℕ) : (xs.getD i 0 : ℝ) = (xs.map (fun q : ℚ => (q : ℝ))).getD i 0 := by
    simpa only [Rat.cast_zero] using
      (List.getD_map (l := xs) (d := (0 : ℚ)) (n := i) (fun q : ℚ => (q : ℝ))).symm
  unfold displacementQ displacementR
  push_cast
  rw [hg 4, hg 5]

theorem raw_cast (net : Network) (xs : List ℚ) :
    (rawQ net xs : ℝ) = rawR net (xs.map (fun q : ℚ => (q : ℝ))) := by
  unfold rawQ rawR
  rw [← evalQ_cast]
  cases evalQ net xs <;> simp

theorem repaired_cast (net : Network) (xs : List ℚ) :
    (repairedQ net xs : ℝ) = repairedR net (xs.map (fun q : ℚ => (q : ℝ))) := by
  unfold repairedQ repairedR
  rw [project_cast, displacement_cast, raw_cast]
  norm_num

theorem displacement_physical (x : Input) : displacementR x.val = physicalX x+physicalY x := by
  unfold displacementR physicalX physicalY
  ring

theorem repaired_above (net : Network) :
    Satisfies (farAbove 2) (fun x => repairedR net x.val) := by
  intro x hx
  change (1/2 : ℝ) ≤ project 64 (displacementR x.val) (rawR net x.val)
  apply project_above _ _ _ (by norm_num)
  rw [displacement_physical]
  change physicalY x ≥ -physicalX x+2 at hx
  linarith

theorem repaired_below (net : Network) :
    Satisfies (farBelow 2) (fun x => repairedR net x.val) := by
  intro x hx
  change project 64 (displacementR x.val) (rawR net x.val) ≤ (1/2 : ℝ)
  apply project_below _ _ _ (by norm_num)
  rw [displacement_physical]
  change physicalY x ≤ -physicalX x-2 at hx
  linarith

theorem smaller_repair_equal (xs : List ℝ) (hx : InBox Adversarial.domain xs) :
    repairedR smallCore xs = repairedR fullCore xs := by
  unfold repairedR rawR
  rw [core_equal xs hx]

theorem repaired_relu_program (net : Network) (xs : List ℝ) :
    reluBlock 64 (displacementR xs) (rawR net xs) = repairedR net xs :=
  reluBlock_eq_project _ _ _

def mseQ (f : List ℚ → ℚ) (rows : List (List ℚ × ℚ)) : ℚ :=
  (rows.map (fun row => (f row.1-row.2)^2)).sum / rows.length

noncomputable def mseR (f : List ℝ → ℝ) (rows : List (List ℚ × ℚ)) : ℝ :=
  (rows.map (fun row => (f (row.1.map (fun q : ℚ => (q : ℝ)))-(row.2 : ℝ))^2)).sum /
  rows.length

theorem mse_cast (f : List ℚ → ℚ) (g : List ℝ → ℝ)
    (h : ∀ xs, (f xs : ℝ) = g (xs.map (fun q : ℚ => (q : ℝ))))
    (rows : List (List ℚ × ℚ)) : (mseQ f rows : ℝ) = mseR g rows := by
  simp [mseQ, mseR, List.map_map, Function.comp_def, h]

end Contribution.DirectedRepair
