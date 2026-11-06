import MomentumQuotient

/-! A precise boundary: aggregate second moments do not implement RMSProp.
The witnesses have nonnegative histories but need not arise from zero initialization. -/
set_option autoImplicit false
namespace Contribution.Reduction.AdaptiveBoundary

abbrev State := Fin 10 → ℝ
abbrev View := Fin 8 → ℝ

def view (x : State) : View := ![x 0,x 1+x 3,x 2,x 4,x 5,x 6+x 8,x 7,x 9]

/-- Squared score loss with features (0,0,z2,0,1), target zero,
plus one-half (a0+a1+a3)^2. -/
def gradient (z2 : ℝ) (x : State) : Fin 5 → ℝ :=
  let e := x 2*z2+x 4
  let g := x 0+x 1+x 3
  ![g,g,e*z2,g,e]

noncomputable def variance (z2 : ℝ) (x : State) : Fin 5 → ℝ :=
  let g := gradient z2 x
  ![(x 5+(g 0)^2)/2,(x 6+(g 1)^2)/2,(x 7+(g 2)^2)/2,
    (x 8+(g 3)^2)/2,(x 9+(g 4)^2)/2]

/-- RMSProp with decay 1/2, rate 1 and epsilon 1, no centering or momentum. -/
noncomputable def step (z2 : ℝ) (x : State) : State :=
  let g := gradient z2 x
  let v := variance z2 x
  ![x 0-g 0/(Real.sqrt (v 0)+1),x 1-g 1/(Real.sqrt (v 1)+1),
    x 2-g 2/(Real.sqrt (v 2)+1),x 3-g 3/(Real.sqrt (v 3)+1),
    x 4-g 4/(Real.sqrt (v 4)+1),v 0,v 1,v 2,v 3,v 4]

def left : State := ![1,0,0,0,0,0,1,0,97,0]
def right : State := ![1,0,0,0,0,0,49,0,49,0]

def Valid (x : State) : Prop := 0 ≤ x 5 ∧ 0 ≤ x 6 ∧ 0 ≤ x 7 ∧ 0 ≤ x 8 ∧ 0 ≤ x 9

theorem left_valid : Valid left := by norm_num [Valid,left]
theorem right_valid : Valid right := by norm_num [Valid,right]

theorem same_view : view left = view right := by
  funext i; fin_cases i <;> norm_num [view,left,right]

theorem left_next_sum (z2 : ℝ) : view (step z2 left) 1 = -(5/8 : ℝ) := by
  norm_num [view,step,variance,gradient,left]

theorem right_next_sum (z2 : ℝ) : view (step z2 right) 1 = -(1/3 : ℝ) := by
  norm_num [view,step,variance,gradient,right]

theorem next_views_differ (z2 : ℝ) : view (step z2 left) ≠ view (step z2 right) := by
  intro h
  have h1 := congrFun h 1
  rw [left_next_sum,right_next_sum] at h1
  norm_num at h1

theorem no_reduced_step (z2 : ℝ) :
    ¬ ∃ small : View → View, ∀ x, Valid x → view (step z2 x) = small (view x) := by
  rintro ⟨small,h⟩
  apply next_views_differ z2
  rw [h left left_valid,h right right_valid,same_view]

end Contribution.Reduction.AdaptiveBoundary
