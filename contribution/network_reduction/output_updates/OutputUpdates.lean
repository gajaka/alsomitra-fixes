import Adversarial

/-! A typed update contract for the certified adversarial network reduction.
The hidden layers and their certificate stay fixed. The state type restricts
inputs to the raw certified cube. Parameters and updates are rational, while
network evaluation and observable algebras use real arithmetic. -/
set_option autoImplicit false
namespace Contribution.Reduction.OutputUpdates
open Contribution.Universal

abbrev Input := {xs : List ℝ // InBox Adversarial.domain xs}

structure FullHead where
  a0 : ℚ
  a1 : ℚ
  a2 : ℚ
  a3 : ℚ
  bias : ℚ
  deriving Repr, DecidableEq

structure ReducedHead where
  a0 : ℚ
  a2 : ℚ
  bias : ℚ
  deriving Repr, DecidableEq

abbrev State := Input × FullHead
abbrev View := Input × ReducedHead

def projectHead (a : FullHead) : ReducedHead := ⟨a.a0, a.a2, a.bias⟩
def view (s : State) : View := (s.1, projectHead s.2)
def RR (s t : State) : Prop := view s = view t

def stateSetoid : Setoid State where
  r := RR
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

def zeroInput : Input := ⟨[0,0,0,0,0,0], Adversarial.domain_nonempty⟩

theorem input_nonempty : Nonempty Input := ⟨zeroInput⟩

def FullHead.neuron (a : FullHead) : Neuron :=
  ⟨[a.a0, a.a1, a.a2, a.a3], a.bias⟩

def ReducedHead.neuron (a : ReducedHead) : Neuron :=
  ⟨[a.a0, a.a2], a.bias⟩

def withHead (net : Network) (head : List Neuron) : Network :=
  {net with third := head}

theorem check_with_head_iff (net : Network) (head : List Neuron)
    (domain : List Interval) (certificate : Certificate) :
    Check (withHead net head) domain certificate ↔ Check net domain certificate := Iff.rfl

theorem prune_with_head (net : Network) (head : List Neuron) (k₁ k₂ : List Bool) :
    prune (withHead net head) k₁ k₂ =
      withHead (prune net k₁ k₂) (head.map (trimInputs k₂)) := rfl

def fullNetwork (head : FullHead) : Network :=
  withHead Adversarial.original [head.neuron]

def reducedNetwork (head : ReducedHead) : Network :=
  withHead Adversarial.reduced [head.neuron]

theorem head_certificate (head : FullHead) :
    Check (fullNetwork head) Adversarial.domain Adversarial.certificate :=
  (check_with_head_iff _ _ _ _).mpr Adversarial.checked

theorem head_pruning (head : FullHead) :
    prune (fullNetwork head) Adversarial.certificate.firstKeep
      Adversarial.certificate.secondKeep = reducedNetwork (projectHead head) := by
  unfold fullNetwork reducedNetwork
  rw [prune_with_head, Adversarial.export_matches_prune]
  rfl

theorem all_output_heads (head : FullHead) (x : Input) :
    eval (reducedNetwork (projectHead head)) x.val = eval (fullNetwork head) x.val := by
  rw [← head_pruning]
  exact certified_prune _ _ _ (head_certificate head) x.val x.property

def fullOutput (s : State) : ℝ := (eval (fullNetwork s.2) s.1.val).headD 0
def reducedOutput (v : View) : ℝ := (eval (reducedNetwork v.2) v.1.val).headD 0

theorem output_factors (s : State) : fullOutput s = reducedOutput (view s) := by
  exact (congrArg (fun ys : List ℝ => ys.headD 0) (all_output_heads s.2 s.1)).symm

inductive Operation where
  | addA0 : ℚ → Operation
  | addA1 : ℚ → Operation
  | addA2 : ℚ → Operation
  | addA3 : ℚ → Operation
  | addBias : ℚ → Operation
  deriving Repr, DecidableEq

def step (op : Operation) (s : State) : State :=
  (s.1, match op with
    | .addA0 d => {s.2 with a0 := s.2.a0 + d}
    | .addA1 d => {s.2 with a1 := s.2.a1 + d}
    | .addA2 d => {s.2 with a2 := s.2.a2 + d}
    | .addA3 d => {s.2 with a3 := s.2.a3 + d}
    | .addBias d => {s.2 with bias := s.2.bias + d})

def reducedStep (op : Operation) (v : View) : View :=
  (v.1, match op with
    | .addA0 d => {v.2 with a0 := v.2.a0 + d}
    | .addA1 _ => v.2
    | .addA2 d => {v.2 with a2 := v.2.a2 + d}
    | .addA3 _ => v.2
    | .addBias d => {v.2 with bias := v.2.bias + d})

theorem operation_factors (op : Operation) (s : State) :
    view (step op s) = reducedStep op (view s) := by
  cases op <;> rfl

def runWith {I S : Type*} (ops : I → S → S) : List I → S → S
  | [], s => s
  | op :: rest, s => runWith ops rest (ops op s)

theorem compatible_run_factors {I : Type*} (ops : I → State → State)
    (reducedOps : I → View → View)
    (h : ∀ op s, view (ops op s) = reducedOps op (view s))
    (word : List I) (s : State) :
    view (runWith ops word s) = runWith reducedOps word (view s) := by
  induction word generalizing s with
  | nil => rfl
  | cons op rest ih => simp only [runWith, ih, h]

def run := runWith step
def reducedRun := runWith reducedStep

theorem run_factors (word : List Operation) (s : State) :
    view (run word s) = reducedRun word (view s) :=
  compatible_run_factors step reducedStep operation_factors word s

theorem RR_preserved (word : List Operation) {s t : State} (h : RR s t) :
    RR (run word s) (run word t) := by
  change view (run word s) = view (run word t)
  rw [run_factors, run_factors, h]

theorem compatible_sequence_agreement {I : Type*} (ops : I → State → State)
    (reducedOps : I → View → View)
    (h : ∀ op s, view (ops op s) = reducedOps op (view s))
    (word : List I) (s : State) :
    fullOutput (runWith ops word s) = reducedOutput (runWith reducedOps word (view s)) := by
  rw [output_factors, compatible_run_factors ops reducedOps h]

theorem sequence_agreement (word : List Operation) (s : State) :
    fullOutput (run word s) = reducedOutput (reducedRun word (view s)) :=
  compatible_sequence_agreement step reducedStep operation_factors word s

/-- Composition is an algebra homomorphism for pointwise real observables. -/
def pullback {S T : Type*} (q : S → T) : (T → ℝ) →ₐ[ℝ] (S → ℝ) where
  toFun f := f ∘ q
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

def viewAlgebra : Subalgebra ℝ (State → ℝ) := (pullback view).range

def Stable (op : State → State) (B : Subalgebra ℝ (State → ℝ)) : Prop :=
  ∀ f, f ∈ B → pullback op f ∈ B

def Fixed (op : State → State) (B : Subalgebra ℝ (State → ℝ)) : Prop :=
  ∀ f, f ∈ B → pullback op f = f

theorem members_agree {f : State → ℝ} (hf : f ∈ viewAlgebra)
    {s t : State} (h : RR s t) : f s = f t := by
  obtain ⟨g, rfl⟩ := hf
  exact congrArg g h

theorem compatible_stable (op : State → State) (reducedOp : View → View)
    (h : ∀ s, view (op s) = reducedOp (view s)) : Stable op viewAlgebra := by
  rintro f ⟨g, rfl⟩
  refine ⟨pullback reducedOp g, ?_⟩
  funext s
  exact congrArg g (h s).symm

theorem view_algebra_stable (op : Operation) : Stable (step op) viewAlgebra :=
  compatible_stable _ _ (operation_factors op)

theorem run_algebra_stable (word : List Operation) : Stable (run word) viewAlgebra :=
  compatible_stable _ _ (run_factors word)

theorem output_in_algebra : fullOutput ∈ viewAlgebra := by
  refine ⟨reducedOutput, ?_⟩
  funext s
  exact (output_factors s).symm

def erasedObservable (s : State) : ℝ := s.2.a1
def keptObservable (s : State) : ℝ := s.2.a0

theorem kept_in_algebra : keptObservable ∈ viewAlgebra :=
  ⟨fun v => (v.2.a0 : ℝ), rfl⟩

def witness0 : State := (zeroInput, ⟨0,0,0,0,0⟩)
def witness1 : State := (zeroInput, ⟨0,1,0,0,0⟩)

theorem witness_same_view : RR witness0 witness1 := rfl

theorem erased_not_in_algebra : erasedObservable ∉ viewAlgebra := by
  intro h
  have he := members_agree h witness_same_view
  norm_num [erasedObservable, witness0, witness1] at he

theorem view_algebra_proper : viewAlgebra ≠ ⊤ := by
  intro h
  apply erased_not_in_algebra
  rw [h]
  trivial

/-- The forbidden update reads a discarded coordinate to change a retained one. -/
def badStep (s : State) : State := (s.1, {s.2 with a0 := s.2.a0 + s.2.a1})

theorem bad_same_view : view witness0 = view witness1 := rfl

theorem bad_views_differ : view (badStep witness0) ≠ view (badStep witness1) := by
  intro h
  have he := congrArg (fun v : View => v.2.a0) h
  norm_num [view, projectHead, badStep, witness0, witness1] at he

theorem bad_no_reduced_step : ¬ ∃ reducedOp : View → View,
    ∀ s, view (badStep s) = reducedOp (view s) := by
  rintro ⟨reducedOp, h⟩
  apply bad_views_differ
  rw [h, h, bad_same_view]

theorem view_algebra_not_stable_bad : ¬ Stable badStep viewAlgebra := by
  intro h
  have he := members_agree (h keptObservable kept_in_algebra) witness_same_view
  change ((0 + 0 : ℚ) : ℝ) = ((0 + 1 : ℚ) : ℝ) at he
  norm_num at he

theorem view_algebra_not_fixed : ¬ Fixed (step (.addA0 1)) viewAlgebra := by
  intro h
  have he := congrFun (h keptObservable kept_in_algebra) witness0
  change ((0 + 1 : ℚ) : ℝ) = ((0 : ℚ) : ℝ) at he
  norm_num at he

theorem erased_updates_fixed (d : ℚ) :
    Fixed (step (.addA1 d)) viewAlgebra ∧ Fixed (step (.addA3 d)) viewAlgebra := by
  constructor <;> rintro f ⟨g, rfl⟩ <;> rfl

theorem bad_preserves_certificate (s : State) :
    Check (fullNetwork (badStep s).2) Adversarial.domain Adversarial.certificate :=
  head_certificate _

private theorem dot_zero_weights (n : Nat) (xs : List ℝ) :
    dot (List.replicate n 0) xs = 0 := by
  induction n generalizing xs with
  | zero => simp [dot]
  | succ n ih => cases xs <;> simp [List.replicate_succ, dot, ih]

theorem zero_head_output (b : ℚ) (x : Input) :
    fullOutput (x, ⟨0,0,0,0,b⟩) = relu (b : ℝ) := by
  change relu (dot [0,0,0,0] _ + (b : ℝ)) = _
  have hz : ∀ xs : List ℝ, dot [0,0,0,0] xs = 0 := by
    intro xs
    simpa [List.replicate_succ] using dot_zero_weights 4 xs
  rw [hz, zero_add]

theorem output_can_change :
    fullOutput witness0 = 0 ∧ fullOutput (step (.addBias 1) witness0) = 1 := by
  constructor
  · simpa [witness0, relu] using zero_head_output 0 zeroInput
  · simpa [step, witness0, relu] using zero_head_output 1 zeroInput

end Contribution.Reduction.OutputUpdates
