import NetworkRetention

/-! Rational hidden features, tied to the existing real network semantics. -/
set_option autoImplicit false
namespace Contribution.Reduction.RationalFeatures
open Contribution.Universal AffineRetention

def dotQ : List ℚ → List ℚ → ℚ
  | w :: ws, x :: xs => w * x + dotQ ws xs
  | _, _ => 0

def layerQ (ns : List Neuron) (xs : List ℚ) : List ℚ :=
  ns.map fun n => max 0 (dotQ n.weights xs + n.bias)

theorem dot_cast (ws xs : List ℚ) :
    (dotQ ws xs : ℝ) = dot ws (xs.map fun (x : ℚ) => (x : ℝ)) := by
  induction ws generalizing xs with
  | nil => simp [dotQ, dot]
  | cons w ws ih => cases xs <;> simp [dotQ, dot, ih]

theorem layer_cast (ns : List Neuron) (xs : List ℚ) :
    (layerQ ns xs).map (fun (x : ℚ) => (x : ℝ)) =
      (evalLayer ns (xs.map fun (x : ℚ) => (x : ℝ))).map relu := by
  simp only [layerQ, evalLayer, List.map_map]
  apply List.map_congr_left
  intro n _
  simp [relu, Neuron.eval, ← dot_cast, Rat.cast_max]

def hidden (xs : List ℚ) : List ℚ :=
  layerQ Adversarial.original.second (layerQ Adversarial.original.first xs)

def features (xs : List ℚ) : Vector 5 :=
  ![(hidden xs).getD 0 0, (hidden xs).getD 1 0,
    (hidden xs).getD 2 0, (hidden xs).getD 3 0, 1]

theorem hidden_cast (xs : List ℚ) :
    (hidden xs).map (fun (x : ℚ) => (x : ℝ)) =
    (evalLayer Adversarial.original.second
      ((evalLayer Adversarial.original.first (xs.map fun (x : ℚ) => (x : ℝ))).map relu)).map relu := by
  unfold hidden
  rw [layer_cast, layer_cast]

def initialHead : Vector 5 :=
  let n := Adversarial.original.third.headD ⟨[], 0⟩
  ![n.weights.getD 0 0, n.weights.getD 1 0, n.weights.getD 2 0,
    n.weights.getD 3 0, n.bias]

def score (z x : Vector 5) : ℚ := ∑ j, x j * z j

end Contribution.Reduction.RationalFeatures
