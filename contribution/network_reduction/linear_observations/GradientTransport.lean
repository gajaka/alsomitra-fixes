import MomentumQuotient

/-! Transport of momentum through linear observations requires a Gram factor.
The theorem accepts arbitrary factored gradient functions, not only affine ones. -/
set_option autoImplicit false
namespace Contribution.Reduction.GradientTransport
open AffineRetention
open scoped Matrix

abbrev State (n : ℕ) := Vector n × Vector n

def project {n r : ℕ} (b : Matrix (Fin r) (Fin n) ℚ) (s : State n) : State r :=
  (b *ᵥ s.1, b *ᵥ s.2)

def step {n : ℕ} (g : Vector n → Vector n) (rate momentum : ℚ) (s : State n) : State n :=
  let v := momentum • s.2 + g s.1
  (s.1-rate • v,v)

def smallStep {n r : ℕ} (b : Matrix (Fin r) (Fin n) ℚ)
    (g : Vector r → Vector r) (rate momentum : ℚ) (s : State r) : State r :=
  let v := momentum • s.2 + (b*b.transpose) *ᵥ g s.1
  (s.1-rate • v,v)

theorem momentum_factors {n r : ℕ} (b : Matrix (Fin r) (Fin n) ℚ)
    (fullGradient : Vector n → Vector n) (smallGradient : Vector r → Vector r)
    (hf : ∀ x, fullGradient x = b.transpose *ᵥ smallGradient (b *ᵥ x))
    (rate momentum : ℚ) (s : State n) :
    project b (step fullGradient rate momentum s) =
      smallStep b smallGradient rate momentum (project b s) := by
  have hv : b *ᵥ (momentum • s.2 + fullGradient s.1) =
      momentum • (b *ᵥ s.2) + (b*b.transpose) *ᵥ smallGradient (b *ᵥ s.1) := by
    rw [Matrix.mulVec_add,Matrix.mulVec_smul,hf,Matrix.mulVec_mulVec]
  unfold project step smallStep
  dsimp
  rw [Matrix.mulVec_sub,Matrix.mulVec_smul,hv]

theorem sequence_factors {I : Type} {n r : ℕ} (b : Matrix (Fin r) (Fin n) ℚ)
    (fullGradient : I → Vector n → Vector n) (smallGradient : I → Vector r → Vector r)
    (hf : ∀ k x, fullGradient k x = b.transpose *ᵥ smallGradient k (b *ᵥ x))
    (rate momentum : I → ℚ) (word : List I) (s : State n) :
    project b (OutputUpdates.runWith (fun k => step (fullGradient k) (rate k) (momentum k)) word s) =
    OutputUpdates.runWith (fun k => smallStep b (smallGradient k) (rate k) (momentum k)) word (project b s) := by
  induction word generalizing s with
  | nil => rfl
  | cons k ks ih =>
    simp only [OutputUpdates.runWith,ih,momentum_factors b (fullGradient k) (smallGradient k) (hf k)]

def headProjection : Matrix (Fin 4) (Fin 5) ℚ :=
  Matrix.of ![![1,0,0,0,0],![0,1,0,1,0],![0,0,1,0,0],![0,0,0,0,1]]

theorem head_gram : headProjection*headProjection.transpose =
    Matrix.diagonal (![1,2,1,1] : Vector 4) := by decide +kernel

def withZeroMemory (x : Vector 5) : Vector 10 := ![x 0,x 1,x 2,x 3,x 4,0,0,0,0,0]
def smallGradient (c : MomentumQuotient.Config) (x : Vector 4) : Vector 4 :=
  let e := x 0*c.z0+x 2*c.z2+x 3-c.target
  let g := c.penalty*(x 0+x 1)
  ![e*c.z0+g,g,e*c.z2,e]

theorem checkpoint_head_gradient_factors (c : MomentumQuotient.Config) (x : Vector 5) :
    MomentumQuotient.gradient c (withZeroMemory x) =
      headProjection.transpose *ᵥ smallGradient c (headProjection *ᵥ x) := by
  funext i
  fin_cases i <;>
    dsimp [MomentumQuotient.gradient,withZeroMemory,smallGradient,headProjection,
      Matrix.mulVec,Matrix.transpose_apply,dotProduct]
  all_goals norm_num [Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp

def sumProjection : Matrix (Fin 1) (Fin 2) ℚ := Matrix.of ![![1,1]]
def exampleGradient (x : Vector 1) : Vector 1 := fun _ => 1+x 0
def liftedGradient (x : Vector 2) : Vector 2 := sumProjection.transpose *ᵥ exampleGradient (sumProjection *ᵥ x)
def start : State 2 := (fun _ => 0,fun _ => 0)

theorem naive_gradient_fails :
    project sumProjection (step liftedGradient 1 0 start) ≠
      step exampleGradient 1 0 (project sumProjection start) := by
  intro h
  have h0 := congrFun (congrArg Prod.fst h) 0
  norm_num [project,step,liftedGradient,exampleGradient,sumProjection,start,
    Matrix.mulVec,Matrix.transpose_apply,dotProduct,Fin.sum_univ_succ] at h0
  change (2 : ℚ) = 1 + 0 at h0
  norm_num at h0

theorem corrected_gradient_agrees :
    project sumProjection (step liftedGradient 1 0 start) =
      smallStep sumProjection exampleGradient 1 0 (project sumProjection start) :=
  momentum_factors sumProjection liftedGradient exampleGradient (fun _ => rfl) 1 0 start

end Contribution.Reduction.GradientTransport
