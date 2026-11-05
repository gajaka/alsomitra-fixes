import Mathlib

/-! A checked interval certificate for real affine/ReLU networks with rational
parameters. Approximate executions may introduce a bounded error at each
neuron's affine result. No PyTorch kernel error bound is assumed here. -/
set_option autoImplicit false
namespace Contribution.Universal

structure Interval where
  lo : ℚ
  hi : ℚ
  deriving Repr, DecidableEq

def Interval.Mem (b : Interval) (x : ℝ) : Prop := (b.lo : ℝ) ≤ x ∧ x ≤ (b.hi : ℝ)
def InBox (bs : List Interval) (xs : List ℝ) : Prop := List.Forall₂ Interval.Mem bs xs

def Encloses (big small : List Interval) : Prop :=
  List.Forall₂ (fun b s => b.lo ≤ s.lo ∧ s.hi ≤ b.hi) big small

instance (big small : List Interval) : Decidable (Encloses big small) :=
  inferInstanceAs (Decidable (List.Forall₂ _ _ _))

theorem enclosed (big small : List Interval) (xs : List ℝ)
    (hb : Encloses big small) (hx : InBox small xs) : InBox big xs := by
  induction hb generalizing xs with
  | nil => cases hx; exact .nil
  | @cons b s big small h ht ih =>
    cases hx with
    | cons hx hxs =>
      apply List.Forall₂.cons _ (ih _ hxs)
      exact ⟨le_trans (by exact_mod_cast h.1) hx.1, le_trans hx.2 (by exact_mod_cast h.2)⟩

def dot : List ℚ → List ℝ → ℝ
  | w::ws, x::xs => (w : ℝ)*x + dot ws xs
  | _, _ => 0

def dotLo : List ℚ → List Interval → ℚ
  | w::ws, b::bs => w * (if 0 ≤ w then b.lo else b.hi) + dotLo ws bs
  | _, _ => 0

def dotHi : List ℚ → List Interval → ℚ
  | w::ws, b::bs => w * (if 0 ≤ w then b.hi else b.lo) + dotHi ws bs
  | _, _ => 0

theorem dot_bounds (ws : List ℚ) (bs : List Interval) (xs : List ℝ) (h : InBox bs xs) :
    (dotLo ws bs : ℝ) ≤ dot ws xs ∧ dot ws xs ≤ (dotHi ws bs : ℝ) := by
  induction ws generalizing bs xs with
  | nil => simp [dot, dotLo, dotHi]
  | cons w ws ih =>
    cases h with
    | nil => simp [dot, dotLo, dotHi]
    | @cons b x bs xs hx ht =>
      have tail := ih bs xs ht
      rcases hx with ⟨hl, hu⟩
      by_cases hw : 0 ≤ w
      · have hw' : (0 : ℝ) ≤ w := by exact_mod_cast hw
        simp only [dot, dotLo, dotHi, ite_eq_left hw, Rat.cast_add, Rat.cast_mul]
        constructor <;> nlinarith [mul_le_mul_of_nonneg_left hl hw', mul_le_mul_of_nonneg_left hu hw']
      · have hw' : (w : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hw)
        simp only [dot, dotLo, dotHi, ite_eq_right hw, Rat.cast_add, Rat.cast_mul]
        constructor <;> nlinarith [mul_le_mul_of_nonpos_left hl hw', mul_le_mul_of_nonpos_left hu hw']

structure Neuron where
  weights : List ℚ
  bias : ℚ
  deriving Repr, DecidableEq

def Neuron.eval (n : Neuron) (xs : List ℝ) : ℝ := dot n.weights xs + n.bias

def Approx (eps : ℚ) (n : Neuron) (xs : List ℝ) (y : ℝ) : Prop :=
  n.eval xs - eps ≤ y ∧ y ≤ n.eval xs + eps

def CheckNeuron (eps : ℚ) (n : Neuron) (bs : List Interval) (b : Interval) : Prop :=
  b.lo ≤ dotLo n.weights bs + n.bias - eps ∧
  dotHi n.weights bs + n.bias + eps ≤ b.hi

instance (eps : ℚ) (n : Neuron) (bs : List Interval) (b : Interval) : Decidable (CheckNeuron eps n bs b) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem neuron_sound (eps : ℚ) (n : Neuron) (bs : List Interval) (b : Interval)
    (xs : List ℝ) (y : ℝ) (hx : InBox bs xs) (hc : CheckNeuron eps n bs b)
    (he : Approx eps n xs y) : b.Mem y := by
  have hd := dot_bounds n.weights bs xs hx
  have hl : (b.lo : ℝ) ≤ (dotLo n.weights bs : ℝ) + (n.bias : ℝ) - eps := by exact_mod_cast hc.1
  have hu : (dotHi n.weights bs : ℝ) + (n.bias : ℝ) + eps ≤ (b.hi : ℝ) := by exact_mod_cast hc.2
  unfold Approx Neuron.eval at he
  constructor <;> linarith [he.1, he.2, hd.1, hd.2]

def CheckLayer (eps : ℚ) (ns : List Neuron) (bs outs : List Interval) : Prop :=
  List.Forall₂ (fun n b => CheckNeuron eps n bs b) ns outs

instance (eps : ℚ) (ns : List Neuron) (bs outs : List Interval) : Decidable (CheckLayer eps ns bs outs) :=
  inferInstanceAs (Decidable (List.Forall₂ _ _ _))

def LayerTrace (eps : ℚ) (ns : List Neuron) (xs ys : List ℝ) : Prop :=
  List.Forall₂ (fun n y => Approx eps n xs y) ns ys

theorem layer_sound (eps : ℚ) (ns : List Neuron) (bs outs : List Interval)
    (xs ys : List ℝ) (hx : InBox bs xs) (hc : CheckLayer eps ns bs outs)
    (he : LayerTrace eps ns xs ys) : InBox outs ys := by
  induction hc generalizing ys with
  | nil => cases he; exact .nil
  | @cons n b ns outs hn ht ih =>
    cases he with
    | cons hy hyrest => exact .cons (neuron_sound eps n bs b xs _ hx hn hy) (ih _ hyrest)

def relu (x : ℝ) : ℝ := max 0 x

def reluBox (bs : List Interval) : List Interval :=
  bs.map fun b => ⟨max 0 b.lo, max 0 b.hi⟩

theorem relu_sound (bs : List Interval) (xs : List ℝ) (h : InBox bs xs) :
    InBox (reluBox bs) (xs.map relu) := by
  induction h with
  | nil => exact .nil
  | @cons b x bs xs hx ht ih =>
    apply List.Forall₂.cons _ ih
    rcases hx with ⟨hl, hu⟩
    constructor <;> simp only [Rat.cast_max, Rat.cast_zero] <;> exact max_le_max le_rfl (by assumption)

structure Network where
  first : List Neuron
  second : List Neuron
  third : List Neuron
  deriving Repr, DecidableEq

def evalLayer (ns : List Neuron) (xs : List ℝ) : List ℝ := ns.map fun n => n.eval xs

def Network.eval (net : Network) (xs : List ℝ) : List ℝ :=
  evalLayer net.third ((evalLayer net.second ((evalLayer net.first xs).map relu)).map relu)

def Trace (net : Network) (eps : ℚ) (xs ys : List ℝ) : Prop :=
  ∃ a b, LayerTrace eps net.first xs a ∧ LayerTrace eps net.second (a.map relu) b ∧
    LayerTrace eps net.third (b.map relu) ys

theorem exact_layer_trace (ns : List Neuron) (eps : ℚ) (he : 0 ≤ eps) (xs : List ℝ) :
    LayerTrace eps ns xs (evalLayer ns xs) := by
  have he' : (0 : ℝ) ≤ eps := by exact_mod_cast he
  induction ns with
  | nil => exact .nil
  | cons n ns ih =>
    apply List.Forall₂.cons _ ih
    constructor <;> linarith

theorem exact_trace (net : Network) (eps : ℚ) (he : 0 ≤ eps) (xs : List ℝ) :
    Trace net eps xs (net.eval xs) := by
  exact ⟨_, _, exact_layer_trace _ _ he _, exact_layer_trace _ _ he _, exact_layer_trace _ _ he _⟩

structure Leaf where
  first : List Interval
  second : List Interval
  third : List Interval
  deriving Repr, DecidableEq

def CheckLeaf (net : Network) (eps cap : ℚ) (bs : List Interval) (c : Leaf) : Prop :=
  CheckLayer eps net.first bs c.first ∧
  CheckLayer eps net.second (reluBox c.first) c.second ∧
  CheckLayer eps net.third (reluBox c.second) c.third ∧
  ∀ b ∈ c.third, b.hi ≤ cap

instance (net : Network) (eps cap : ℚ) (bs : List Interval) (c : Leaf) :
    Decidable (CheckLeaf net eps cap bs c) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem box_upper (bs : List Interval) (ys : List ℝ) (cap : ℚ) (h : InBox bs ys)
    (hu : ∀ b ∈ bs, b.hi ≤ cap) : ∀ y ∈ ys, y ≤ (cap : ℝ) := by
  induction h with
  | nil => simp
  | @cons b y bs ys hy ht ih =>
    intro z hz
    rcases List.mem_cons.mp hz with he | hm
    · subst z
      exact hy.2.trans (by exact_mod_cast hu b (List.mem_cons_self))
    · exact ih (fun b hb => hu b (List.mem_cons_of_mem _ hb)) z hm

theorem leaf_sound (net : Network) (eps cap : ℚ) (bs : List Interval) (c : Leaf)
    (xs ys : List ℝ) (hc : CheckLeaf net eps cap bs c) (hx : InBox bs xs)
    (ht : Trace net eps xs ys) : ∀ y ∈ ys, y ≤ (cap : ℝ) := by
  rcases ht with ⟨a,b,ha,hb,hy⟩
  have h1 := relu_sound _ _ (layer_sound _ _ _ _ _ _ hx hc.1 ha)
  have h2 := relu_sound _ _ (layer_sound _ _ _ _ _ _ h1 hc.2.1 hb)
  have h3 := layer_sound _ _ _ _ _ _ h2 hc.2.2.1 hy
  exact box_upper _ _ cap h3 hc.2.2.2

/-- Both children are clipped from the parent; an omitted region cannot be
hidden in a user-provided list of boxes. An out-of-range split is harmless. -/
def bisect : List Interval → Nat → ℚ → List Interval × List Interval
  | [], _, _ => ([], [])
  | b::bs, 0, cut => (⟨b.lo, min b.hi cut⟩::bs, ⟨max b.lo cut, b.hi⟩::bs)
  | b::bs, n+1, cut => let children := bisect bs n cut; (b::children.1, b::children.2)

theorem bisect_covers (bs : List Interval) (axis : Nat) (cut : ℚ) (xs : List ℝ)
    (hx : InBox bs xs) : InBox (bisect bs axis cut).1 xs ∨ InBox (bisect bs axis cut).2 xs := by
  induction hx generalizing axis with
  | nil => exact Or.inl .nil
  | @cons b x bs xs h ht ih =>
    cases axis with
    | zero =>
      by_cases hc : x ≤ (cut : ℝ)
      · left; apply List.Forall₂.cons _ ht
        exact ⟨h.1, by simpa only [Rat.cast_min] using le_min h.2 hc⟩
      · right; apply List.Forall₂.cons _ ht
        exact ⟨by simpa only [Rat.cast_max] using max_le h.1 (le_of_not_ge hc), h.2⟩
    | succ n =>
      rcases ih n with hl | hr
      · exact Or.inl (.cons h hl)
      · exact Or.inr (.cons h hr)

inductive Tree where
  | leaf : Leaf → Tree
  | split : Nat → ℚ → Tree → Tree → Tree
  deriving Repr

def CheckTree (net : Network) (eps cap : ℚ) : List Interval → Tree → Prop
  | bs, .leaf c => CheckLeaf net eps cap bs c
  | bs, .split axis cut left right =>
    CheckTree net eps cap (bisect bs axis cut).1 left ∧
    CheckTree net eps cap (bisect bs axis cut).2 right

theorem tree_sound (net : Network) (eps cap : ℚ) (bs : List Interval) (t : Tree)
    (hc : CheckTree net eps cap bs t) (xs ys : List ℝ) (hx : InBox bs xs)
    (ht : Trace net eps xs ys) : ∀ y ∈ ys, y ≤ (cap : ℝ) := by
  induction t generalizing bs with
  | leaf c => exact leaf_sound net eps cap bs c xs ys hc hx ht
  | split axis cut left right il ir =>
    rcases bisect_covers bs axis cut xs hx with hl | hr
    · exact il _ hc.1 hl
    · exact ir _ hc.2 hr

end Contribution.Universal
