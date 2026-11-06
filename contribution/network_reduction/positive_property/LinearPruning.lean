import Lipschitz
import Pruning

/-! Reuse the existing hidden-neuron certificate for a linear output layer.
The earlier checkpoints have an output ReLU; the DL2/GD exports do not. -/
set_option autoImplicit false
namespace Contribution.PositiveProperty
open Contribution.Universal Contribution.Reduction

theorem linear_prune_exact (net : Network) (k₁ k₂ : List Bool) (xs : List ℝ)
    (h₁ : ZeroOutside k₁ ((evalLayer net.first xs).map relu))
    (h₂ : ZeroOutside k₂
      ((evalLayer net.second ((evalLayer net.first xs).map relu)).map relu)) :
    (prune net k₁ k₂).eval xs = net.eval xs := by
  have first : (evalLayer (select k₁ net.first) xs).map relu =
      select k₁ ((evalLayer net.first xs).map relu) := by
    simp only [evalLayer, select_map]
  have second :
      (evalLayer ((select k₂ net.second).map (trimInputs k₁))
        ((evalLayer (select k₁ net.first) xs).map relu)).map relu =
      select k₂ ((evalLayer net.second ((evalLayer net.first xs).map relu)).map relu) := by
    rw [first, layer_trim k₁ _ _ h₁]
    simp only [evalLayer, select_map]
  unfold Network.eval
  change evalLayer (net.third.map (trimInputs k₂))
    ((evalLayer ((select k₂ net.second).map (trimInputs k₁))
      ((evalLayer (select k₁ net.first) xs).map relu)).map relu) = _
  rw [second, layer_trim k₂ _ _ h₂]

theorem certified_linear_prune (net : Network) (domain : List Interval) (c : Certificate)
    (hc : Reduction.Check net domain c) (xs : List ℝ) (hx : InBox domain xs) :
    (prune net c.firstKeep c.secondKeep).eval xs = net.eval xs := by
  have first := layer_sound 0 net.first domain c.firstBounds xs _ hx hc.1
    (exact_layer_trace _ 0 (by norm_num) xs)
  have second := layer_sound 0 net.second (reluBox c.firstBounds) c.secondBounds
    _ _ (relu_sound _ _ first) hc.2.1 (exact_layer_trace _ 0 (by norm_num) _)
  exact linear_prune_exact net c.firstKeep c.secondKeep xs
    (zeros_of_bounds _ _ _ hc.2.2.1 first) (zeros_of_bounds _ _ _ hc.2.2.2 second)

def cube : List Interval := List.replicate 6 ⟨0, 1⟩

theorem valid_in_cube (x : Fin 6 → ℝ) (hx : ValidInput x) : InBox cube (inputs x) := by
  apply List.Forall₂.cons (by simpa [Interval.Mem] using hx 0)
  apply List.Forall₂.cons (by simpa [Interval.Mem] using hx 1)
  apply List.Forall₂.cons (by simpa [Interval.Mem] using hx 2)
  apply List.Forall₂.cons (by simpa [Interval.Mem] using hx 3)
  apply List.Forall₂.cons (by simpa [Interval.Mem] using hx 4)
  apply List.Forall₂.cons (by simpa [Interval.Mem] using hx 5)
  exact .nil

theorem pruned_output (net : Network) (c : Certificate)
    (hc : Reduction.Check net cube c) (x : Fin 6 → ℝ) (hx : ValidInput x) :
    output (prune net c.firstKeep c.secondKeep) x = output net x := by
  exact congrArg (fun ys : List ℝ => ys.headD 0)
    (certified_linear_prune net cube c hc (inputs x) (valid_in_cube x hx))

end Contribution.PositiveProperty
