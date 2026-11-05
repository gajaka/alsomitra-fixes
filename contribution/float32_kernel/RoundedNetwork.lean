import Rounding
import IntervalNetwork

/-! Reduction semantics for affine neurons. Each bias/product occurs exactly
once; addition trees and FMA placement may vary. No vendor implementation is
identified with this semantics by an axiom. -/
set_option autoImplicit false
noncomputable section
namespace Contribution.Binary32
open Contribution.Universal

def Expr.terms : Expr → List ℝ
  | .atom x => [x]
  | .product w x => [w*x]
  | .add a b => a.terms ++ b.terms
  | .fma w x a => w*x :: a.terms

theorem terms_exact (t : Expr) : t.terms.sum = t.exact := by
  induction t with
  | atom x => simp [Expr.terms, Expr.exact]
  | product w x => simp [Expr.terms, Expr.exact]
  | add a b ha hb => simp [Expr.terms, Expr.exact, ha, hb]
  | fma w x a ha => simp [Expr.terms, Expr.exact, ha]

theorem terms_mass (t : Expr) : (t.terms.map abs).sum = t.mass := by
  induction t with
  | atom x => simp [Expr.terms, Expr.mass]
  | product w x => simp [Expr.terms, Expr.mass]
  | add a b ha hb => simp [Expr.terms, Expr.mass, ha, hb]
  | fma w x a ha => simp [Expr.terms, Expr.mass, ha]

theorem terms_cost (t : Expr) : t.cost + 1 ≤ 2*t.terms.length := by
  induction t with
  | atom x => simp [Expr.cost, Expr.terms]
  | product w x => simp [Expr.cost, Expr.terms]
  | add a b ha hb => simp only [Expr.cost, Expr.terms, List.length_append]; omega
  | fma w x a ha => simp only [Expr.cost, Expr.terms, List.length_cons]; omega

def products (ws : List ℚ) (xs : List ℝ) : List ℝ :=
  List.zipWith (fun w x => (w : ℝ)*x) ws xs

theorem products_sum (ws : List ℚ) (xs : List ℝ) : (products ws xs).sum = dot ws xs := by
  induction ws generalizing xs with
  | nil => simp [products, dot]
  | cons w ws ih =>
    cases xs with
    | nil => simp [products, dot]
    | cons x xs => simpa [products, dot] using congrArg (fun y => (w:ℝ)*x+y) (ih xs)

def neuronTerms (n : Neuron) (xs : List ℝ) : List ℝ := (n.bias : ℝ)::products n.weights xs

def Reduction (r : ℝ → ℝ) (n : Neuron) (xs : List ℝ) (y : ℝ) : Prop :=
  n.weights.length = xs.length ∧
  ∃ t : Expr, t.terms.Perm (neuronTerms n xs) ∧ y = t.run r

def magnitude (b : Interval) : ℚ := max (|b.lo|) (|b.hi|)

theorem magnitude_bound (b : Interval) (x : ℝ) (h : b.Mem x) : |x| ≤ (magnitude b : ℝ) := by
  have hl : -(magnitude b : ℝ) ≤ (b.lo : ℝ) := by
    have hh : |(b.lo : ℝ)| ≤ (magnitude b : ℝ) := by
      exact_mod_cast (le_max_left (|b.lo|) (|b.hi|))
    exact (abs_le.mp hh).1
  have hu : (b.hi : ℝ) ≤ (magnitude b : ℝ) := by
    have hh : |(b.hi : ℝ)| ≤ (magnitude b : ℝ) := by
      exact_mod_cast (le_max_right (|b.lo|) (|b.hi|))
    exact (abs_le.mp hh).2
  exact abs_le.mpr ⟨hl.trans h.1,h.2.trans hu⟩

def massBound (n : Neuron) (bs : List Interval) : ℚ :=
  |n.bias| + (List.zipWith (fun w b => |w| * magnitude b) n.weights bs).sum

theorem products_mass_bound (ws : List ℚ) (bs : List Interval) (xs : List ℝ)
    (hx : InBox bs xs) :
    ((products ws xs).map abs).sum ≤ ((List.zipWith (fun w b => |w| * magnitude b) ws bs).sum : ℚ) := by
  induction ws generalizing bs xs with
  | nil => simp [products]
  | cons w ws ih =>
    cases hx with
    | nil => simp [products]
    | @cons b x bs xs hb ht =>
      have hi := ih bs xs ht
      have hh := mul_le_mul_of_nonneg_left (magnitude_bound b x hb) (abs_nonneg (w : ℝ))
      simpa [products, abs_mul] using add_le_add hh hi

theorem neuron_mass_bound (n : Neuron) (bs : List Interval) (xs : List ℝ)
    (hx : InBox bs xs) : ((neuronTerms n xs).map abs).sum ≤ (massBound n bs : ℝ) := by
  simpa [neuronTerms, massBound] using
    add_le_add (le_refl (|(n.bias : ℝ)|)) (products_mass_bound n.weights bs xs hx)

def SafeLayer (ns : List Neuron) (bs : List Interval) : Prop :=
  ∀ n ∈ ns, n.weights.length = bs.length ∧ n.weights.length ≤ 64 ∧ massBound n bs ≤ 16

instance (ns : List Neuron) (bs : List Interval) : Decidable (SafeLayer ns bs) :=
  inferInstanceAs (Decidable (∀ n ∈ ns, _ ∧ _ ∧ _))

theorem reduction_approx (r : ℝ → ℝ) (hr : CorrectRounding r) (n : Neuron)
    (bs : List Interval) (xs : List ℝ) (y : ℝ) (hx : InBox bs xs)
    (hm : massBound n bs ≤ 16) (hw : n.weights.length ≤ 64)
    (hy : Reduction r n xs y) : Approx (1/1024) n xs y := by
  rcases hy with ⟨hlen,t,hp,rfl⟩
  have he : t.exact = n.eval xs := by
    rw [← terms_exact, hp.sum_eq]
    simp [neuronTerms, Neuron.eval, products_sum, add_comm]
  have ht : t.mass ≤ 16 := by
    rw [← terms_mass, (hp.map abs).sum_eq]
    exact (neuron_mass_bound n bs xs hx).trans (by exact_mod_cast hm)
  have hc : t.cost ≤ 129 := by
    have hcost := terms_cost t
    have hlength := hp.length_eq
    simp only [neuronTerms, List.length_cons, products, List.length_zipWith] at hlength
    omega
  have hh := expression_within_neuron_budget r hr t ht hc
  rw [he, abs_le] at hh
  constructor <;> push_cast <;> linarith [hh.1,hh.2]

def RoundedLayer (r : ℝ → ℝ) (ns : List Neuron) (xs ys : List ℝ) : Prop :=
  List.Forall₂ (fun n y => Reduction r n xs y) ns ys

theorem rounded_layer_trace (r : ℝ → ℝ) (hr : CorrectRounding r) (ns : List Neuron)
    (bs : List Interval) (xs ys : List ℝ) (hx : InBox bs xs) (hs : SafeLayer ns bs)
    (hy : RoundedLayer r ns xs ys) : LayerTrace (1/1024) ns xs ys := by
  induction hy with
  | nil => exact .nil
  | @cons n y ns ys hn ht ih =>
    have hs' := hs n (List.mem_cons_self)
    exact .cons (reduction_approx r hr n bs xs y hx hs'.2.2 hs'.2.1 hn)
      (ih (fun n hn => hs n (List.mem_cons_of_mem _ hn)))

def RoundedNetwork (r : ℝ → ℝ) (net : Network) (xs ys : List ℝ) : Prop :=
  ∃ a b, RoundedLayer r net.first xs a ∧ RoundedLayer r net.second (a.map relu) b ∧
    RoundedLayer r net.third (b.map relu) ys

end Contribution.Binary32
