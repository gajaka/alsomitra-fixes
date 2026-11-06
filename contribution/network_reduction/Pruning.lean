import IntervalNetwork

/-! Deleting certified zero hidden activations preserves a network's function.
The semantics use real arithmetic and rational, checkpoint-derived parameters.
The output ReLU of the published SAIV controllers is included explicitly. -/
set_option autoImplicit false
namespace Contribution.Reduction
open Contribution.Universal

def select {α : Type*} : List Bool → List α → List α
  | true :: ks, x :: xs => x :: select ks xs
  | false :: ks, _ :: xs => select ks xs
  | _, _ => []

theorem select_map {α β : Type*} (f : α → β) (ks : List Bool) (xs : List α) :
    select ks (xs.map f) = (select ks xs).map f := by
  induction ks generalizing xs with
  | nil => simp [select]
  | cons k ks ih =>
    cases xs with
    | nil => simp [select]
    | cons x xs => cases k <;> simp [select, ih]

def ZeroOutside : List Bool → List ℝ → Prop
  | [], [] => True
  | k :: ks, x :: xs => (k = false → x = 0) ∧ ZeroOutside ks xs
  | _, _ => False

theorem dot_select (ks : List Bool) (xs : List ℝ) (ws : List ℚ)
    (hz : ZeroOutside ks xs) : dot (select ks ws) (select ks xs) = dot ws xs := by
  induction ks generalizing xs ws with
  | nil =>
    cases xs with
    | nil => cases ws <;> simp [select, dot]
    | cons x xs => exact False.elim hz
  | cons k ks ih =>
    cases xs with
    | nil => exact False.elim hz
    | cons x xs =>
      cases ws with
      | nil => simp [select, dot]
      | cons w ws =>
        rcases hz with ⟨hx, ht⟩
        cases k with
        | false => simp [select, dot, hx rfl, ih xs ws ht]
        | true => simp [select, dot, ih xs ws ht]

def trimInputs (ks : List Bool) (n : Neuron) : Neuron :=
  { n with weights := select ks n.weights }

theorem layer_trim (ks : List Bool) (ns : List Neuron) (xs : List ℝ)
    (hz : ZeroOutside ks xs) :
    evalLayer (ns.map (trimInputs ks)) (select ks xs) = evalLayer ns xs := by
  simp only [evalLayer, List.map_map]
  apply List.map_congr_left
  intro n _
  exact congrArg (fun z : ℝ => z + (n.bias : ℝ)) (dot_select ks xs n.weights hz)

def prune (net : Network) (firstKeep secondKeep : List Bool) : Network :=
  ⟨select firstKeep net.first,
   (select secondKeep net.second).map (trimInputs firstKeep),
   net.third.map (trimInputs secondKeep)⟩

def eval (net : Network) (xs : List ℝ) : List ℝ := (net.eval xs).map relu

theorem prune_exact (net : Network) (k₁ k₂ : List Bool) (xs : List ℝ)
    (h₁ : ZeroOutside k₁ ((evalLayer net.first xs).map relu))
    (h₂ : ZeroOutside k₂
      ((evalLayer net.second ((evalLayer net.first xs).map relu)).map relu)) :
    eval (prune net k₁ k₂) xs = eval net xs := by
  have first : (evalLayer (select k₁ net.first) xs).map relu =
      select k₁ ((evalLayer net.first xs).map relu) := by
    simp only [evalLayer, select_map]
  have second :
      (evalLayer ((select k₂ net.second).map (trimInputs k₁))
        ((evalLayer (select k₁ net.first) xs).map relu)).map relu =
      select k₂ ((evalLayer net.second ((evalLayer net.first xs).map relu)).map relu) := by
    rw [first, layer_trim k₁ _ _ h₁]
    simp only [evalLayer, select_map]
  unfold eval Network.eval
  change (evalLayer (net.third.map (trimInputs k₂))
    ((evalLayer ((select k₂ net.second).map (trimInputs k₁))
      ((evalLayer (select k₁ net.first) xs).map relu)).map relu)).map relu = _
  rw [second, layer_trim k₂ _ _ h₂]

def DropsNonpositive (ks : List Bool) (bs : List Interval) : Prop :=
  List.Forall₂ (fun k b => k = false → b.hi ≤ 0) ks bs

instance (ks : List Bool) (bs : List Interval) : Decidable (DropsNonpositive ks bs) :=
  inferInstanceAs (Decidable (List.Forall₂ _ _ _))

theorem zeros_of_bounds (ks : List Bool) (bs : List Interval) (xs : List ℝ)
    (hd : DropsNonpositive ks bs) (hx : InBox bs xs) :
    ZeroOutside ks (xs.map relu) := by
  induction hd generalizing xs with
  | nil => cases hx; trivial
  | @cons k b ks bs hk ht ih =>
    cases hx with
    | cons hb hxs =>
      constructor
      · intro he
        have hu : (b.hi : ℝ) ≤ 0 := by exact_mod_cast hk he
        exact max_eq_left (hb.2.trans hu)
      · exact ih _ hxs

structure Certificate where
  firstBounds : List Interval
  secondBounds : List Interval
  firstKeep : List Bool
  secondKeep : List Bool
  deriving Repr, DecidableEq

def Check (net : Network) (domain : List Interval) (c : Certificate) : Prop :=
  CheckLayer 0 net.first domain c.firstBounds ∧
  CheckLayer 0 net.second (reluBox c.firstBounds) c.secondBounds ∧
  DropsNonpositive c.firstKeep c.firstBounds ∧
  DropsNonpositive c.secondKeep c.secondBounds

instance (net : Network) (domain : List Interval) (c : Certificate) :
    Decidable (Check net domain c) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem certified_prune (net : Network) (domain : List Interval) (c : Certificate)
    (hc : Check net domain c) (xs : List ℝ) (hx : InBox domain xs) :
    eval (prune net c.firstKeep c.secondKeep) xs = eval net xs := by
  have first := layer_sound 0 net.first domain c.firstBounds xs _ hx hc.1
    (exact_layer_trace _ 0 (by norm_num) xs)
  have second := layer_sound 0 net.second (reluBox c.firstBounds) c.secondBounds
    _ _ (relu_sound _ _ first) hc.2.1 (exact_layer_trace _ 0 (by norm_num) _)
  exact prune_exact net c.firstKeep c.secondKeep xs
    (zeros_of_bounds _ _ _ hc.2.2.1 first) (zeros_of_bounds _ _ _ hc.2.2.2 second)

def EquivalentOn (domain : List Interval) (a b : Network) : Prop :=
  ∀ xs, InBox domain xs → eval a xs = eval b xs

def networkSetoid (domain : List Interval) : Setoid Network where
  r := EquivalentOn domain
  iseqv := ⟨fun _ _ _ => rfl,
            fun h xs hx => (h xs hx).symm,
            fun h₁ h₂ xs hx => (h₁ xs hx).trans (h₂ xs hx)⟩

theorem certified_equivalent (net : Network) (domain : List Interval) (c : Certificate)
    (hc : Check net domain c) : EquivalentOn domain (prune net c.firstKeep c.secondKeep) net :=
  certified_prune net domain c hc

theorem predicate_transfer (domain : List Interval) (a b : Network)
    (he : EquivalentOn domain a b) (P : List ℝ → Prop) (xs : List ℝ)
    (hx : InBox domain xs) : P (eval a xs) ↔ P (eval b xs) := by
  rw [he xs hx]

end Contribution.Reduction
