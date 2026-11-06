import NetworkRetention

/-! A symbolic quotient of coupled output-head momentum updates.
All parameters are rational; equality is exact, with fixed hidden layers. -/
set_option autoImplicit false
namespace Contribution.Reduction.MomentumQuotient
open AffineRetention

structure Config where
  z0 : ℚ
  z2 : ℚ
  target : ℚ
  rate : ℚ
  momentum : ℚ
  penalty : ℚ

def gradient (c : Config) (x : Vector 10) : Vector 5 :=
  let e := x 0 * c.z0 + x 2 * c.z2 + x 4 - c.target
  let g := c.penalty * (x 0 + x 1 + x 3)
  ![e*c.z0 + g, g, e*c.z2, g, e]

def velocity (c : Config) (x : Vector 10) : Vector 5 :=
  ![c.momentum*x 5 + gradient c x 0,
    c.momentum*x 6 + gradient c x 1,
    c.momentum*x 7 + gradient c x 2,
    c.momentum*x 8 + gradient c x 3,
    c.momentum*x 9 + gradient c x 4]

def step (c : Config) (x : Vector 10) : Vector 10 :=
  let v := velocity c x
  ![x 0-c.rate*v 0, x 1-c.rate*v 1, x 2-c.rate*v 2, x 3-c.rate*v 3,
    x 4-c.rate*v 4, v 0, v 1, v 2, v 3, v 4]

def view (x : Vector 10) : Vector 8 := ![x 0, x 1+x 3, x 2, x 4, x 5, x 6+x 8, x 7, x 9]

def smallVelocity (c : Config) (x : Vector 8) : Vector 4 :=
  let e := x 0*c.z0 + x 2*c.z2 + x 3 - c.target
  let g := c.penalty*(x 0+x 1)
  ![c.momentum*x 4 + e*c.z0+g, c.momentum*x 5+2*g,
    c.momentum*x 6+e*c.z2, c.momentum*x 7+e]

def smallStep (c : Config) (x : Vector 8) : Vector 8 :=
  let v := smallVelocity c x
  ![x 0-c.rate*v 0, x 1-c.rate*v 1, x 2-c.rate*v 2, x 3-c.rate*v 3,
    v 0, v 1, v 2, v 3]

theorem step_factors (c : Config) (x : Vector 10) : view (step c x) = smallStep c (view x) := by
  funext i
  fin_cases i <;> dsimp [view, step, smallStep, velocity, smallVelocity, gradient] <;> ring

def run : List Config → Vector 10 → Vector 10
  | [], x => x
  | c :: cs, x => run cs (step c x)

def smallRun : List Config → Vector 8 → Vector 8
  | [], x => x
  | c :: cs, x => smallRun cs (smallStep c x)

theorem run_factors (word : List Config) (x : Vector 10) :
    view (run word x) = smallRun word (view x) := by
  induction word generalizing x with
  | nil => rfl
  | cons c cs ih => simp only [run, smallRun, ih, step_factors]

def head (x : Vector 10) : OutputUpdates.FullHead := ⟨x 0,x 1,x 2,x 3,x 4⟩
def output (input : OutputUpdates.Input) (x : Vector 10) : ℝ :=
  OutputUpdates.fullOutput (input,head x)
def smallOutput (input : OutputUpdates.Input) (x : Vector 8) : ℝ :=
  OutputUpdates.reducedOutput (input,⟨x 0,x 2,x 3⟩)

theorem output_factors (input : OutputUpdates.Input) (x : Vector 10) :
    output input x = smallOutput input (view x) := OutputUpdates.output_factors (input,head x)

theorem network_sequence (input : OutputUpdates.Input) (word : List Config) (x : Vector 10) :
    output input (run word x) = smallOutput input (smallRun word (view x)) := by
  rw [output_factors, run_factors]

theorem certificate_sequence (word : List Config) (x : Vector 10) :
    Check (OutputUpdates.fullNetwork (head (run word x)))
      Adversarial.domain Adversarial.certificate := OutputUpdates.head_certificate _

def RR (x y : Vector 10) : Prop := view x = view y
def stateSetoid : Setoid (Vector 10) where
  r := RR
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

theorem RR_preserved (word : List Config) {x y : Vector 10} (h : RR x y) :
    RR (run word x) (run word y) := by
  change view (run word x) = view (run word y)
  rw [run_factors, run_factors, h]

def observableAlgebra : Subalgebra ℝ (Vector 10 → ℝ) := (OutputUpdates.pullback view).range

theorem algebra_stable (word : List Config) : Stable (run word) observableAlgebra := by
  rintro f ⟨g,rfl⟩
  refine ⟨g ∘ smallRun word, ?_⟩
  funext x
  exact congrArg g (run_factors word x).symm

theorem output_in_algebra (input : OutputUpdates.Input) : output input ∈ observableAlgebra := by
  refine ⟨smallOutput input, ?_⟩
  funext x
  exact (output_factors input x).symm

def zeroState : Vector 10 := fun _ => 0
def hiddenDifference : Vector 10 := ![0,1,0,-1,0,0,0,0,0,0]

theorem hidden_difference_invisible : view zeroState = view hiddenDifference := by
  funext i; fin_cases i <;> norm_num [view,zeroState,hiddenDifference]

theorem hidden_coordinate_not_observable :
    (fun x : Vector 10 => (x 1 : ℝ)) ∉ observableAlgebra := by
  rintro ⟨g,hg⟩
  have h0 := congrFun hg zeroState
  have h1 := congrFun hg hiddenDifference
  change g (view zeroState) = (zeroState 1 : ℝ) at h0
  change g (view hiddenDifference) = (hiddenDifference 1 : ℝ) at h1
  rw [hidden_difference_invisible] at h0
  norm_num [zeroState,hiddenDifference] at h0 h1
  linarith

theorem algebra_proper : observableAlgebra ≠ ⊤ := by
  intro h
  apply hidden_coordinate_not_observable
  rw [h]
  trivial

end Contribution.Reduction.MomentumQuotient
