import IntervalNetwork

/-! Exact global sensitivity certificates for affine/ReLU networks.
The checker uses absolute path weights. It need not find the smallest bound.
No floating-point execution or training-convergence claim is made. -/
set_option autoImplicit false

namespace Contribution.PositiveProperty
open Contribution.Universal

inductive Within (d : ℝ) : List ℚ → List ℝ → List ℝ → Prop where
  | nil : Within d [] [] []
  | cons {b : ℚ} {bs : List ℚ} {x y : ℝ} {xs ys : List ℝ}
      (head : |x - y| ≤ (b : ℝ) * d) (tail : Within d bs xs ys) :
      Within d (b :: bs) (x :: xs) (y :: ys)

def weightedAbs : List ℚ → List ℚ → ℚ
  | w :: ws, b :: bs => |w| * b + weightedAbs ws bs
  | _, _ => 0

theorem dot_delta (ws bs : List ℚ) (xs ys : List ℝ) (d : ℝ)
    (h : Within d bs xs ys) :
    |dot ws xs - dot ws ys| ≤ (weightedAbs ws bs : ℝ) * d := by
  induction ws generalizing bs xs ys with
  | nil => simp [dot, weightedAbs]
  | cons w ws ih =>
    cases h with
    | nil => simp [dot, weightedAbs]
    | @cons b bs x y xs ys hh ht =>
      have tail := ih bs xs ys ht
      have head := mul_le_mul_of_nonneg_left hh (abs_nonneg (w : ℝ))
      calc
        |dot (w :: ws) (x :: xs) - dot (w :: ws) (y :: ys)| =
            |(w : ℝ) * (x - y) + (dot ws xs - dot ws ys)| := by
              congr 1; simp only [dot]; ring
        _ ≤ |(w : ℝ) * (x - y)| + |dot ws xs - dot ws ys| := abs_add_le _ _
        _ ≤ |(w : ℝ)| * ((b : ℝ) * d) + (weightedAbs ws bs : ℝ) * d := by
          rw [abs_mul]; exact add_le_add head tail
        _ = (weightedAbs (w :: ws) (b :: bs) : ℝ) * d := by
          simp only [weightedAbs, Rat.cast_add, Rat.cast_mul, Rat.cast_abs]; ring

theorem relu_delta (x y : ℝ) : |relu x - relu y| ≤ |x - y| := by
  have h1 := le_abs_self (x - y)
  have h2 := neg_abs_le (x - y)
  by_cases hx : 0 ≤ x <;> by_cases hy : 0 ≤ y
  · simp [relu, max_eq_right hx, max_eq_right hy]
  · rw [relu, relu, max_eq_right hx, max_eq_left (le_of_not_ge hy)]
    rw [sub_zero, abs_of_nonneg hx]; linarith
  · rw [relu, relu, max_eq_left (le_of_not_ge hx), max_eq_right hy]
    rw [zero_sub, abs_neg, abs_of_nonneg hy]; linarith
  · rw [relu, relu, max_eq_left (le_of_not_ge hx), max_eq_left (le_of_not_ge hy)]
    simp

theorem relu_within (d : ℝ) (bs : List ℚ) (xs ys : List ℝ)
    (h : Within d bs xs ys) : Within d bs (xs.map relu) (ys.map relu) := by
  induction h with
  | nil => exact .nil
  | cons hh _ ih => exact .cons ((relu_delta _ _).trans hh) ih

def layerCosts (ns : List Neuron) (bs : List ℚ) : List ℚ :=
  ns.map fun n => weightedAbs n.weights bs

theorem layer_within (ns : List Neuron) (bs : List ℚ) (xs ys : List ℝ) (d : ℝ)
    (h : Within d bs xs ys) :
    Within d (layerCosts ns bs) (evalLayer ns xs) (evalLayer ns ys) := by
  induction ns with
  | nil => exact .nil
  | cons n ns ih =>
    apply Within.cons _ ih
    simpa only [Neuron.eval, add_sub_add_right_eq_sub] using dot_delta n.weights bs xs ys d h

def costs (net : Network) (bs : List ℚ) : List ℚ :=
  layerCosts net.third (layerCosts net.second (layerCosts net.first bs))

theorem network_within (net : Network) (bs : List ℚ) (xs ys : List ℝ) (d : ℝ)
    (h : Within d bs xs ys) : Within d (costs net bs) (net.eval xs) (net.eval ys) := by
  exact layer_within _ _ _ _ d
    (relu_within _ _ _ _ (layer_within _ _ _ _ d
      (relu_within _ _ _ _ (layer_within _ _ _ _ d h))))

def Check (net : Network) (cap : ℚ) : Prop :=
  0 ≤ cap ∧ ∀ c ∈ costs net (List.replicate 6 1), c ≤ cap

instance (net : Network) (cap : ℚ) : Decidable (Check net cap) :=
  inferInstanceAs (Decidable (_ ∧ _))

def inputs (x : Fin 6 → ℝ) : List ℝ := [x 0, x 1, x 2, x 3, x 4, x 5]
noncomputable def output (net : Network) (x : Fin 6 → ℝ) : ℝ :=
  (net.eval (inputs x)).headD 0

theorem inputs_within (x y : Fin 6 → ℝ) (d : ℝ) (h : ∀ i, |x i - y i| ≤ d) :
    Within d (List.replicate 6 1) (inputs x) (inputs y) := by
  apply Within.cons (by simpa using h 0)
  apply Within.cons (by simpa using h 1)
  apply Within.cons (by simpa using h 2)
  apply Within.cons (by simpa using h 3)
  apply Within.cons (by simpa using h 4)
  apply Within.cons (by simpa using h 5)
  exact .nil

theorem head_delta (d : ℝ) (bs : List ℚ) (xs ys : List ℝ) (h : Within d bs xs ys)
    (cap : ℚ) (hc : 0 ≤ cap) (hd : 0 ≤ d) (hb : ∀ b ∈ bs, b ≤ cap) :
    |xs.headD 0 - ys.headD 0| ≤ (cap : ℝ) * d := by
  cases h with
  | nil => simpa using mul_nonneg (by exact_mod_cast hc : (0 : ℝ) ≤ cap) hd
  | @cons b bs x y xs ys hh ht =>
    exact hh.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hb b (List.mem_cons_self)) hd)

theorem checked_global (net : Network) (cap : ℚ) (hc : Check net cap)
    (x y : Fin 6 → ℝ) (d : ℝ) (hd : 0 ≤ d) (h : ∀ i, |x i - y i| ≤ d) :
    |output net x - output net y| ≤ (cap : ℝ) * d := by
  exact head_delta d _ _ _ (network_within net _ _ _ d (inputs_within x y d h))
    cap hc.1 hd hc.2

def ValidInput (x : Fin 6 → ℝ) : Prop := ∀ i, 0 ≤ x i ∧ x i ≤ 1

/-- Paper section 7.2 network-to-network output requirement, with explicit
all-anchor quantification. Lstar/epsilon is the published threshold; Lstar is
not the actual Lipschitz constant certified by Check. -/
def Property5 (net : Network) (epsilon Lstar : ℝ) : Prop :=
  ∀ x y, ValidInput x → ValidInput y → (∀ i, |x i - y i| ≤ epsilon) →
    |output net x - output net y| ≤ Lstar / epsilon

theorem property5_two_sided (net : Network) (eps Lstar : ℝ) :
    Property5 net eps Lstar ↔
      ∀ x y, ValidInput x → ValidInput y → (∀ i, |x i - y i| ≤ eps) →
        output net x - output net y ≤ Lstar / eps ∧
        output net y - output net x ≤ Lstar / eps := by
  constructor
  · intro h x y hx hy hd
    have hh := abs_le.mp (h x y hx hy hd)
    exact ⟨hh.2, by linarith [hh.1]⟩
  · intro h x y hx hy hd
    have hh := h x y hx hy hd
    exact abs_le.mpr ⟨by linarith [hh.2], hh.1⟩

theorem property5_of_check (net : Network) (cap : ℚ) (hc : Check net cap)
    (eps Lstar : ℝ) (he : 0 ≤ eps) (hb : (cap : ℝ) * eps ≤ Lstar / eps) :
    Property5 net eps Lstar := by
  intro x y _ _ h
  exact (checked_global net cap hc x y eps he h).trans hb

/-- The certified region contains distinct inputs with all six coordinates
strictly inside the cube; this does not claim physical reachability. -/
theorem nonvacuous :
    ∃ x y : Fin 6 → ℝ, ValidInput x ∧ ValidInput y ∧ x ≠ y ∧
      (∀ i, 0 < x i ∧ x i < 1 ∧ 0 < y i ∧ y i < 1) ∧
      (∀ i, |x i - y i| ≤ 1 / 1000) := by
  refine ⟨fun _ => 1 / 2, fun _ => 1001 / 2000, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; norm_num
  · intro i; norm_num
  · intro h; have hh := congrFun h 0; norm_num at hh
  · intro i; norm_num
  · intro i; norm_num

/-- Any exact reduction on the cube inherits this relational property. -/
theorem property5_transfer (full reduced : Network) (eps Lstar : ℝ)
    (he : ∀ x, ValidInput x → output reduced x = output full x)
    (hp : Property5 full eps Lstar) : Property5 reduced eps Lstar := by
  intro x y hx hy hd
  rw [he x hx, he y hy]
  exact hp x y hx hy hd

end Contribution.PositiveProperty
