import RoundedNetwork
import RoundingExistence
import FrozenModel

set_option autoImplicit false
noncomputable section
namespace Contribution.Binary32
open Contribution.Universal

def sequential (fused : Bool) (bias : ℝ) : List ℚ → List ℝ → Expr
  | w::ws, x::xs => if fused then .fma w x (sequential fused bias ws xs)
      else .add (.product w x) (sequential fused bias ws xs)
  | _, _ => .atom bias

theorem sequential_terms (fused : Bool) (bias : ℝ) (ws : List ℚ) (xs : List ℝ) :
    (sequential fused bias ws xs).terms = products ws xs ++ [bias] := by
  induction ws generalizing xs with
  | nil => simp [sequential, Expr.terms, products]
  | cons w ws ih =>
    cases xs with
    | nil => simp [sequential, Expr.terms, products]
    | cons x xs => cases fused <;> simp [sequential, Expr.terms, products, ih]

theorem sequential_reduction (fused : Bool) (r : ℝ → ℝ) (n : Neuron)
    (xs : List ℝ) (hlen : n.weights.length = xs.length) :
    Reduction r n xs ((sequential fused n.bias n.weights xs).run r) := by
  refine ⟨hlen,_,?_,rfl⟩
  rw [sequential_terms]
  exact List.perm_append_comm

def runLayer (fused : Bool) (r : ℝ → ℝ) (ns : List Neuron) (xs : List ℝ) : List ℝ :=
  ns.map fun n => (sequential fused n.bias n.weights xs).run r

theorem runLayer_trace (fused : Bool) (r : ℝ → ℝ) (ns : List Neuron)
    (xs : List ℝ) (hlen : ∀ n ∈ ns, n.weights.length = xs.length) :
    RoundedLayer r ns xs (runLayer fused r ns xs) := by
  induction ns with
  | nil => exact .nil
  | cons n ns ih =>
    exact .cons (sequential_reduction fused r n xs (hlen n List.mem_cons_self))
      (ih (fun n hn => hlen n (List.mem_cons_of_mem _ hn)))

theorem network_execution_exists (fused : Bool) (r : ℝ → ℝ) (xs : List ℝ)
    (hlen : xs.length = 6) : ∃ ys, RoundedNetwork r Contribution.Frozen.network xs ys := by
  open Contribution.Frozen in
  have h1 : ∀ n ∈ first, n.weights.length = xs.length := by
    intro n hn
    exact (network_shape.2.2.2.1 n hn).trans hlen.symm
  let a := runLayer fused r Contribution.Frozen.first xs
  let b := runLayer fused r Contribution.Frozen.second (a.map relu)
  let ys := runLayer fused r Contribution.Frozen.third (b.map relu)
  refine ⟨ys,a,b,runLayer_trace fused r _ _ h1,?_,?_⟩
  · apply runLayer_trace
    intro n hn
    simpa [a,runLayer,Contribution.Frozen.network_shape.1] using
      Contribution.Frozen.network_shape.2.2.2.2.1 n hn
  · apply runLayer_trace
    intro n hn
    simpa [b,runLayer,Contribution.Frozen.network_shape.2.1] using
      Contribution.Frozen.network_shape.2.2.2.2.2 n hn

end Contribution.Binary32
