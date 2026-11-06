import AffineRetention

/-! The synthesized state operates on the actual certified adversarial network.
Extra retained output weights are update memory, not restored hidden neurons. -/
set_option autoImplicit false
namespace Contribution.Reduction.NetworkRetention
open AffineRetention

def seed : Finset (Fin 5) := {0, 2, 4}
def head (x : Vector 5) : OutputUpdates.FullHead := ⟨x 0, x 1, x 2, x 3, x 4⟩
def reducedHead {keep : Finset (Fin 5)} (x : Reduced keep) : OutputUpdates.ReducedHead :=
  ⟨extend keep x 0, extend keep x 2, extend keep x 4⟩

def output (input : OutputUpdates.Input) (x : Vector 5) : ℝ :=
  OutputUpdates.fullOutput (input, head x)
def reducedOutput (input : OutputUpdates.Input) {keep : Finset (Fin 5)}
    (x : Reduced keep) : ℝ := OutputUpdates.reducedOutput (input, reducedHead x)

theorem head_certificate (x : Vector 5) :
    Check (OutputUpdates.fullNetwork (head x)) Adversarial.domain Adversarial.certificate :=
  OutputUpdates.head_certificate (head x)

theorem output_factors (keep : Finset (Fin 5)) (hs : seed ⊆ keep)
    (input : OutputUpdates.Input) (x : Vector 5) :
    output input x = reducedOutput input (project keep x) := by
  have h0 : (0 : Fin 5) ∈ keep := hs (by decide)
  have h2 : (2 : Fin 5) ∈ keep := hs (by decide)
  have h4 : (4 : Fin 5) ∈ keep := hs (by decide)
  have hh : reducedHead (project keep x) = OutputUpdates.projectHead (head x) := by
    simp [reducedHead, extend, project, head, OutputUpdates.projectHead, h0, h2, h4]
  unfold output reducedOutput
  rw [hh]
  exact OutputUpdates.output_factors (input, head x)

theorem output_in_algebra (keep : Finset (Fin 5)) (hs : seed ⊆ keep)
    (input : OutputUpdates.Input) : output input ∈ observableAlgebra keep := by
  refine ⟨reducedOutput input, ?_⟩
  funext x
  exact (output_factors keep hs input x).symm

theorem sequence_agreement {m : ℕ} (ops : Fin m → Affine 5)
    (input : OutputUpdates.Input) (word : List (Fin m)) (x : Vector 5) :
    output input (run ops word x) = reducedOutput input
      (reducedRun ops (synthesize ops seed) word (project (synthesize ops seed) x)) := by
  rw [output_factors _ (synthesize_spec ops seed).1,
    run_factors ops _ (synthesize_spec ops seed).2.1]

theorem sequence_certificate {m : ℕ} (ops : Fin m → Affine 5)
    (word : List (Fin m)) (x : Vector 5) :
    Check (OutputUpdates.fullNetwork (head (run ops word x)))
      Adversarial.domain Adversarial.certificate := head_certificate _

def identity : Affine 5 := ⟨fun i j => if i = j then 1 else 0, fun _ => 0⟩

def addFrom (dst src : Fin 5) : Affine 5 :=
  ⟨fun i j => (if i = j then 1 else 0) + (if i = dst ∧ j = src then 1 else 0), fun _ => 0⟩

def shifts : Fin 1 → Affine 5 := fun _ => {identity with offset := fun _ => 1}
def coupling : Fin 1 → Affine 5 := fun _ => addFrom 0 1
def chain : Fin 2 → Affine 5 := ![addFrom 0 1, addFrom 1 3]

theorem shifts_mask : synthesize shifts seed = {0, 2, 4} := by decide +kernel
theorem coupling_mask : synthesize coupling seed = {0, 1, 2, 4} := by decide +kernel
theorem chain_mask : synthesize chain seed = Finset.univ := by decide +kernel
theorem coupling_rejects_seed : ¬ Closed coupling seed := by decide +kernel
theorem chain_rejects_one_round : ¬ Closed chain (grow chain seed) := by decide +kernel

theorem coupling_no_seed_implementation :
    ¬ ∃ red : Fin 1 → Reduced seed → Reduced seed,
      ∀ k x, project seed ((coupling k).apply x) = red k (project seed x) := by
  rw [factorization_iff_closed]
  exact coupling_rejects_seed

/-- One online delta-rule calibration step for a linear score before final ReLU.
The hidden features are frozen; this is not the upstream training objective. -/
def calibrate (features : Vector 5) (target rate : ℚ) : Affine 5 :=
  ⟨fun i j => (if i = j then 1 else 0) - rate * features i * features j,
    fun i => rate * target * features i⟩

theorem calibration_rule (features : Vector 5) (target rate : ℚ) (x : Vector 5) (i : Fin 5) :
    (calibrate features target rate).apply x i =
      x i + rate * (target - ∑ j, x j * features j) * features i := by
  simp only [calibrate, Affine.apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hs : (∑ j, rate * features i * features j * x j) =
      rate * (∑ j, x j * features j) * features i := by
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs]
  ring

theorem calibration_closed (features : Vector 5) (target rate : ℚ)
    (h1 : features 1 = 0) (h3 : features 3 = 0) :
    Closed (fun _ : Fin 1 => calibrate features target rate) seed := by
  intro k i hi j hn
  fin_cases j <;> simp_all [seed, calibrate]

theorem calibration_mask (features : Vector 5) (target rate : ℚ)
    (h1 : features 1 = 0) (h3 : features 3 = 0) :
    synthesize (fun _ : Fin 1 => calibrate features target rate) seed = seed := by
  apply Finset.Subset.antisymm
  · exact (synthesize_spec _ seed).2.2 seed (Finset.Subset.refl _) (calibration_closed _ _ _ h1 h3)
  · exact (synthesize_spec _ seed).1

end Contribution.Reduction.NetworkRetention
