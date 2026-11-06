import AdaptiveBoundary

/-! Exact RMSProp reduction on the invariant equal-history state space.
This imports the original full step and leaves its all-state obstruction intact.
The parameter values and loss are exactly those of AdaptiveBoundary. -/
set_option autoImplicit false
namespace Contribution.Reduction.SymmetricRMSProp
open AdaptiveBoundary

def Symmetric (x : State) : Prop := x 6 = x 8

def initState (a : Fin 5 → ℝ) : State :=
  ![a 0,a 1,a 2,a 3,a 4,0,0,0,0,0]

theorem initialize_symmetric (a : Fin 5 → ℝ) : Symmetric (initState a) := rfl

theorem initialize_valid (a : Fin 5 → ℝ) : Valid (initState a) := by
  norm_num [Valid, initState]

theorem gradient_pair (z : ℝ) (x : State) : gradient z x 1 = gradient z x 3 := rfl

theorem history_difference (z : ℝ) (x : State) :
    step z x 6 - step z x 8 = (x 6 - x 8) / 2 := by
  dsimp [step, variance, AdaptiveBoundary.gradient]
  ring

theorem symmetric_step (z : ℝ) {x : State} (h : Symmetric x) :
    Symmetric (step z x) := by
  change step z x 6 = step z x 8
  have hd := history_difference z x
  change x 6 = x 8 at h
  rw [h] at hd
  linarith

theorem valid_step (z : ℝ) {x : State} (h : Valid x) : Valid (step z x) := by
  rcases h with ⟨h0,h1,h2,h3,h4⟩
  dsimp [Valid, step, variance]
  exact ⟨by positivity,by positivity,by positivity,by positivity,
    by positivity⟩

/-- Four retained moments: r0, r1+r3, r2, rb. -/
noncomputable def smallVariance (z : ℝ) (y : View) : Fin 4 → ℝ :=
  let e := y 2*z+y 3
  let g := y 0+y 1
  ![(y 4+g^2)/2,(y 5+2*g^2)/2,(y 6+(e*z)^2)/2,(y 7+e^2)/2]

/-- The aggregate history must be halved inside the square root. -/
noncomputable def smallStep (z : ℝ) (y : View) : View :=
  let e := y 2*z+y 3
  let g := y 0+y 1
  let v := smallVariance z y
  ![y 0-g/(Real.sqrt (v 0)+1),y 1-2*g/(Real.sqrt (v 1/2)+1),
    y 2-e*z/(Real.sqrt (v 2)+1),y 3-e/(Real.sqrt (v 3)+1),
    v 0,v 1,v 2,v 3]

theorem step_factors (z : ℝ) {x : State} (h : Symmetric x) :
    view (step z x) = smallStep z (view x) := by
  change x 6 = x 8 at h
  funext i
  fin_cases i <;>
    dsimp [view, step, smallStep, smallVariance, variance, AdaptiveBoundary.gradient] <;>
    (try simp only [h]) <;> ring_nf

def ViewValid (y : View) : Prop := 0 ≤ y 4 ∧ 0 ≤ y 5 ∧ 0 ≤ y 6 ∧ 0 ≤ y 7

theorem view_valid {x : State} (h : Valid x) : ViewValid (view x) :=
  ⟨h.1,add_nonneg h.2.1 h.2.2.2.1,h.2.2.1,h.2.2.2.2⟩

/-- One representative: split the history equally and place the weight sum in a1. -/
noncomputable def lift (y : View) : State :=
  ![y 0,y 1,y 2,0,y 3,y 4,y 5/2,y 6,y 5/2,y 7]

theorem lift_symmetric (y : View) : Symmetric (lift y) := rfl

theorem lift_valid {y : View} (h : ViewValid y) : Valid (lift y) := by
  rcases h with ⟨h0,h1,h2,h3⟩
  exact ⟨h0,by dsimp [lift]; positivity,h2,by dsimp [lift]; positivity,h3⟩

theorem view_lift (y : View) : view (lift y) = y := by
  funext i
  fin_cases i <;> dsimp [view,lift] <;> ring

theorem smallStep_valid (z : ℝ) {y : View} (h : ViewValid y) : ViewValid (smallStep z y) := by
  have hv := view_valid (valid_step z (lift_valid h))
  rw [step_factors z (lift_symmetric y),view_lift] at hv
  exact hv

noncomputable def run : List ℝ → State → State
  | [], x => x
  | z :: rest, x => run rest (step z x)

noncomputable def smallRun : List ℝ → View → View
  | [], y => y
  | z :: rest, y => smallRun rest (smallStep z y)

theorem symmetric_run (word : List ℝ) {x : State} (h : Symmetric x) :
    Symmetric (run word x) := by
  induction word generalizing x with
  | nil => exact h
  | cons z rest ih => exact ih (symmetric_step z h)

theorem valid_run (word : List ℝ) {x : State} (h : Valid x) :
    Valid (run word x) := by
  induction word generalizing x with
  | nil => exact h
  | cons z rest ih => exact ih (valid_step z h)

theorem run_factors (word : List ℝ) {x : State} (h : Symmetric x) :
    view (run word x) = smallRun word (view x) := by
  induction word generalizing x with
  | nil => rfl
  | cons z rest ih =>
    simpa only [run, smallRun, step_factors z h] using ih (symmetric_step z h)

theorem initialized_run_factors (word : List ℝ) (a : Fin 5 → ℝ) :
    view (run word (initState a)) = smallRun word (view (initState a)) :=
  run_factors word (initialize_symmetric a)

theorem smallRun_valid (word : List ℝ) {y : View} (h : ViewValid y) :
    ViewValid (smallRun word y) := by
  induction word generalizing y with
  | nil => exact h
  | cons z rest ih => exact ih (smallStep_valid z h)

theorem left_not_symmetric : ¬ Symmetric left := by
  norm_num [Symmetric, left]

theorem right_symmetric : Symmetric right := by
  norm_num [Symmetric, right]

theorem left_unreachable_from_initialization (word : List ℝ) (a : Fin 5 → ℝ) :
    run word (initState a) ≠ left := by
  intro h
  have hs := symmetric_run word (initialize_symmetric a)
  rw [h] at hs
  exact left_not_symmetric hs

/-- The state type exposes both physical validity and the needed invariant. -/
abbrev GoodState := {x : State // Valid x ∧ Symmetric x}

def restrictedView (x : GoodState) : View := view x.val

noncomputable def restrictedRun (word : List ℝ) (x : GoodState) : GoodState :=
  ⟨run word x.val,valid_run word x.property.1,symmetric_run word x.property.2⟩

theorem restricted_run_factors (word : List ℝ) (x : GoodState) :
    restrictedView (restrictedRun word x) = smallRun word (restrictedView x) :=
  run_factors word x.property.2

def RR (x y : GoodState) : Prop := restrictedView x = restrictedView y

def stateSetoid : Setoid GoodState where
  r := RR
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

theorem RR_preserved (word : List ℝ) {x y : GoodState} (h : RR x y) :
    RR (restrictedRun word x) (restrictedRun word y) := by
  change restrictedView (restrictedRun word x) = restrictedView (restrictedRun word y)
  rw [restricted_run_factors, restricted_run_factors, h]

def observableAlgebra : Subalgebra ℝ (GoodState → ℝ) :=
  (OutputUpdates.pullback restrictedView).range

theorem algebra_stable (word : List ℝ) :
    AffineRetention.Stable (restrictedRun word) observableAlgebra := by
  rintro f ⟨g,rfl⟩
  refine ⟨g ∘ smallRun word, ?_⟩
  funext x
  exact congrArg g (restricted_run_factors word x).symm

def zeroState : GoodState :=
  ⟨initState (fun _ => 0),initialize_valid _,initialize_symmetric _⟩

def hiddenDifference : GoodState :=
  ⟨initState ![0,1,0,-1,0],initialize_valid _,initialize_symmetric _⟩

theorem hidden_difference_invisible : restrictedView zeroState = restrictedView hiddenDifference := by
  funext i
  fin_cases i <;> norm_num [restrictedView,view,zeroState,hiddenDifference,initState]

theorem hidden_coordinate_not_observable :
    (fun x : GoodState => x.val 1) ∉ observableAlgebra := by
  rintro ⟨g,hg⟩
  have h0 := congrFun hg zeroState
  have h1 := congrFun hg hiddenDifference
  change g (restrictedView zeroState) = zeroState.val 1 at h0
  change g (restrictedView hiddenDifference) = hiddenDifference.val 1 at h1
  rw [hidden_difference_invisible] at h0
  norm_num [zeroState,hiddenDifference,initState] at h0 h1
  linarith

theorem algebra_proper : observableAlgebra ≠ ⊤ := by
  intro h
  apply hidden_coordinate_not_observable
  rw [h]
  trivial

end Contribution.Reduction.SymmetricRMSProp
