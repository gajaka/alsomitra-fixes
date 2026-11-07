import Mathlib

/-! A continuous directional repair block. Its guarantee is independent of
the core's training procedure. The added architecture is explicit. -/
set_option autoImplicit false
namespace Contribution.DirectedRepair

def lowerQ (k d : ℚ) : ℚ := min (1/2) (max 0 (1/2+k*(d-2)))
def upperQ (k d : ℚ) : ℚ := max (1/2) (min 1 (1/2+k*(d+2)))
def projectQ (k d z : ℚ) : ℚ := max (lowerQ k d) (min (upperQ k d) z)

noncomputable def lower (k d : ℝ) : ℝ := min (1/2) (max 0 (1/2+k*(d-2)))
noncomputable def upper (k d : ℝ) : ℝ := max (1/2) (min 1 (1/2+k*(d+2)))
noncomputable def project (k d z : ℝ) : ℝ := max (lower k d) (min (upper k d) z)

theorem lower_nonneg (k d : ℝ) : 0 ≤ lower k d :=
  le_min (by norm_num) (le_max_left _ _)

theorem lower_le_half (k d : ℝ) : lower k d ≤ 1/2 := min_le_left _ _
theorem half_le_upper (k d : ℝ) : 1/2 ≤ upper k d := le_max_left _ _
theorem upper_le_one (k d : ℝ) : upper k d ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)

theorem interval_valid (k d : ℝ) : lower k d ≤ upper k d :=
  (lower_le_half k d).trans (half_le_upper k d)

theorem project_in_interval (k d z : ℝ) :
    lower k d ≤ project k d z ∧ project k d z ≤ upper k d := by
  exact ⟨le_max_left _ _, max_le (interval_valid k d) (min_le_left _ _)⟩

theorem project_in_unit_interval (k d z : ℝ) :
    0 ≤ project k d z ∧ project k d z ≤ 1 :=
  ⟨(lower_nonneg k d).trans (project_in_interval k d z).1,
   (project_in_interval k d z).2.trans (upper_le_one k d)⟩

theorem above_lower (k d : ℝ) (hk : 0 ≤ k) (hd : 2 ≤ d) : lower k d = 1/2 := by
  apply min_eq_left
  have h : 0 ≤ k*(d-2) := mul_nonneg hk (sub_nonneg.mpr hd)
  exact (by linarith : (1/2 : ℝ) ≤ 1/2+k*(d-2)).trans (le_max_right _ _)

theorem below_upper (k d : ℝ) (hk : 0 ≤ k) (hd : d ≤ -2) : upper k d = 1/2 := by
  apply max_eq_left
  have h : k*(d+2) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk (by linarith)
  exact (min_le_right _ _).trans (by linarith : (1/2 : ℝ)+k*(d+2) ≤ 1/2)

theorem project_above (k d z : ℝ) (hk : 0 ≤ k) (hd : 2 ≤ d) :
    1/2 ≤ project k d z := by
  have h := (project_in_interval k d z).1
  rwa [above_lower k d hk hd] at h

theorem project_below (k d z : ℝ) (hk : 0 ≤ k) (hd : d ≤ -2) :
    project k d z ≤ 1/2 := by
  have h := (project_in_interval k d z).2
  rwa [below_upper k d hk hd] at h

theorem project_unchanged (k d z : ℝ) (hl : lower k d ≤ z) (hu : z ≤ upper k d) :
    project k d z = z := by
  simp only [project, min_eq_right hu, max_eq_right hl]

theorem project_idempotent (k d z : ℝ) : project k d (project k d z) = project k d z :=
  project_unchanged _ _ _ (project_in_interval k d z).1 (project_in_interval k d z).2

noncomputable def rmax (a b : ℝ) : ℝ := a + max 0 (b-a)
noncomputable def rmin (a b : ℝ) : ℝ := a - max 0 (a-b)

theorem rmax_eq (a b : ℝ) : rmax a b = max a b := by
  by_cases h : a ≤ b
  · simp only [rmax, max_eq_right (sub_nonneg.mpr h), max_eq_right h]
    ring
  · have h' : b ≤ a := le_of_not_ge h
    simp only [rmax, max_eq_left (sub_nonpos.mpr h'), max_eq_left h', add_zero]

theorem rmin_eq (a b : ℝ) : rmin a b = min a b := by
  by_cases h : a ≤ b
  · simp only [rmin, max_eq_left (sub_nonpos.mpr h), min_eq_left h, sub_zero]
  · have h' : b ≤ a := le_of_not_ge h
    simp only [rmin, max_eq_right (sub_nonneg.mpr h'), min_eq_right h']
    ring

/-- Six ReLU operations, with affine operations and shared intermediate values. -/
noncomputable def reluBlock (k d z : ℝ) : ℝ :=
  let lo := rmin (1/2) (max 0 (1/2+k*(d-2)))
  let hi := rmax (1/2) (rmin 1 (1/2+k*(d+2)))
  rmax lo (rmin hi z)

theorem reluBlock_eq_project (k d z : ℝ) : reluBlock k d z = project k d z := by
  simp only [reluBlock, rmax_eq, rmin_eq, project, lower, upper]

theorem project_cast (k d z : ℚ) :
    (projectQ k d z : ℝ) = project k d z := by
  unfold projectQ lowerQ upperQ project lower upper
  push_cast
  rfl

end Contribution.DirectedRepair
