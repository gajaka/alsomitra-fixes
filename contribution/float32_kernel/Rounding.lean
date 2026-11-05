import Mathlib

/-! Nearest rounding in the finite binary32 VALUE format. This is not an
implementation-refinement proof for a vendor library or processor ISA. -/
set_option autoImplicit false
noncomputable section
namespace Contribution.Binary32

def Finite (x : ℝ) : Prop :=
  ∃ (m e : ℤ), |m| < 2^24 ∧ -149 ≤ e ∧ e ≤ 104 ∧ x = (m : ℝ) * (2 : ℝ)^e

def Nearest (x y : ℝ) : Prop :=
  Finite y ∧ ∀ v, Finite v → |y - x| ≤ |v - x|

def delta : ℝ := 1 / 524288

theorem delta_positive : 0 < delta := by norm_num [delta]

/-- A representable grid point exists within half a grid step. -/
theorem nearby (x : ℝ) (hx : |x| ≤ 32) :
    ∃ v, Finite v ∧ |v - x| ≤ delta := by
  let m : ℤ := round (x * 262144)
  have hm : |x * 262144 - (m : ℝ)| ≤ (1/2 : ℝ) := abs_sub_round _
  have hmx := (abs_le.mp hm)
  have hxx := (abs_le.mp hx)
  have mb : |m| < (2^24 : ℤ) := by
    have hr : |(m : ℝ)| < (16777216 : ℝ) := by
      rw [abs_lt]
      constructor <;> linarith [hmx.1,hmx.2,hxx.1,hxx.2]
    exact_mod_cast hr
  refine ⟨(m : ℝ) / 262144, ?_, ?_⟩
  · refine ⟨m,-18,mb,by norm_num,by norm_num,?_⟩
    norm_num
    ring
  · unfold delta
    rw [abs_le]
    constructor <;> linarith [hmx.1,hmx.2]

theorem nearest_error (x y : ℝ) (hx : |x| ≤ 32) (hn : Nearest x y) :
    |y - x| ≤ delta := by
  obtain ⟨v,hv,he⟩ := nearby x hx
  exact (hn.2 v hv).trans he

def CorrectRounding (r : ℝ → ℝ) : Prop :=
  ∀ x, |x| ≤ 32 → Nearest x (r x)

inductive Expr where
  | atom : ℝ → Expr
  | product : ℝ → ℝ → Expr
  | add : Expr → Expr → Expr
  | fma : ℝ → ℝ → Expr → Expr

def Expr.exact : Expr → ℝ
  | .atom x => x
  | .product w x => w*x
  | .add a b => a.exact + b.exact
  | .fma w x a => w*x + a.exact

def Expr.mass : Expr → ℝ
  | .atom x => |x|
  | .product w x => |w*x|
  | .add a b => a.mass + b.mass
  | .fma w x a => |w*x| + a.mass

def Expr.cost : Expr → ℕ
  | .atom _ => 0
  | .product _ _ => 1
  | .add a b => a.cost + b.cost + 1
  | .fma _ _ a => a.cost + 1

def Expr.run (r : ℝ → ℝ) : Expr → ℝ
  | .atom x => x
  | .product w x => r (w*x)
  | .add a b => r (a.run r + b.run r)
  | .fma w x a => r (w*x + a.run r)

theorem mass_nonnegative (t : Expr) : 0 ≤ t.mass := by
  induction t with
  | atom x => exact abs_nonneg _
  | product w x => exact abs_nonneg _
  | add a b ha hb => exact add_nonneg ha hb
  | fma w x a ha => exact add_nonneg (abs_nonneg _) ha

theorem exact_le_mass (t : Expr) : |t.exact| ≤ t.mass := by
  induction t with
  | atom x => exact le_rfl
  | product w x => exact le_rfl
  | add a b ha hb => exact (abs_add_le _ _).trans (add_le_add ha hb)
  | fma w x a ha => exact (abs_add_le _ _).trans (add_le_add le_rfl ha)

/-- Bounds every intermediate rounding operand and accumulates operation errors.
The expression includes separated operations, FMA and arbitrary addition trees. -/
theorem expression_error (r : ℝ → ℝ) (hr : CorrectRounding r) (t : Expr)
    (hm : t.mass ≤ 16) (hc : t.cost ≤ 129) :
    |t.run r - t.exact| ≤ (t.cost : ℝ) * delta := by
  have hd := delta_positive
  have hbudget : (129 : ℝ) * delta < 1 := by norm_num [delta]
  induction t with
  | atom x => simp [Expr.run, Expr.exact, Expr.cost]
  | product w x =>
    have hh : |w*x| ≤ 32 := by simpa [Expr.mass] using hm.trans (by norm_num : (16:ℝ) ≤ 32)
    simpa [Expr.run, Expr.exact, Expr.cost] using nearest_error (w*x) (r (w*x)) hh (hr _ hh)
  | add a b ia ib =>
    have hma : a.mass ≤ 16 := by have := mass_nonnegative b; change a.mass+b.mass ≤ 16 at hm; linarith
    have hmb : b.mass ≤ 16 := by have := mass_nonnegative a; change a.mass+b.mass ≤ 16 at hm; linarith
    have hca : a.cost ≤ 129 := by change a.cost+b.cost+1 ≤ 129 at hc; omega
    have hcb : b.cost ≤ 129 := by change a.cost+b.cost+1 ≤ 129 at hc; omega
    have ha := ia hma hca
    have hb := ib hmb hcb
    have hcost : (a.cost:ℝ)+(b.cost:ℝ)+1 ≤ 129 := by exact_mod_cast hc
    have hdiff : |(a.run r+b.run r)-(a.exact+b.exact)| ≤ ((a.cost:ℝ)+(b.cost:ℝ))*delta := by
      calc
        _ = |(a.run r-a.exact)+(b.run r-b.exact)| := by congr 1; ring
        _ ≤ |a.run r-a.exact|+|b.run r-b.exact| := abs_add_le _ _
        _ ≤ (a.cost:ℝ)*delta+(b.cost:ℝ)*delta := add_le_add ha hb
        _ = _ := by ring
    have he : |a.exact+b.exact| ≤ 16 := (exact_le_mass (.add a b)).trans hm
    have harg : |a.run r+b.run r| ≤ 32 := by
      have hh : |a.run r+b.run r| ≤ |(a.run r+b.run r)-(a.exact+b.exact)|+|a.exact+b.exact| :=
        by simpa using abs_add_le ((a.run r+b.run r)-(a.exact+b.exact)) (a.exact+b.exact)
      nlinarith
    have hout := nearest_error _ _ harg (hr _ harg)
    change |r (a.run r+b.run r)-(a.exact+b.exact)| ≤ ((a.cost+b.cost+1:ℕ):ℝ)*delta
    have hh := abs_add_le (r (a.run r+b.run r)-(a.run r+b.run r)) ((a.run r+b.run r)-(a.exact+b.exact))
    simp only [sub_add_sub_cancel] at hh
    push_cast
    nlinarith
  | fma w x a ia =>
    have hma : a.mass ≤ 16 := by have := abs_nonneg (w*x); change |w*x|+a.mass ≤ 16 at hm; linarith
    have hca : a.cost ≤ 129 := by change a.cost+1 ≤ 129 at hc; omega
    have ha := ia hma hca
    have hcost : (a.cost:ℝ)+1 ≤ 129 := by exact_mod_cast hc
    have he : |w*x+a.exact| ≤ 16 := (exact_le_mass (.fma w x a)).trans hm
    have harg : |w*x+a.run r| ≤ 32 := by
      have hh : |w*x+a.run r| ≤ |a.run r-a.exact|+|w*x+a.exact| := by
        calc
          _ = |(a.run r-a.exact)+(w*x+a.exact)| := by congr 1; ring
          _ ≤ _ := abs_add_le _ _
      nlinarith
    have hout := nearest_error _ _ harg (hr _ harg)
    change |r (w*x+a.run r)-(w*x+a.exact)| ≤ ((a.cost+1:ℕ):ℝ)*delta
    have hh := abs_add_le (r (w*x+a.run r)-(w*x+a.run r)) (a.run r-a.exact)
    have hident : (r (w*x+a.run r)-(w*x+a.run r))+(a.run r-a.exact) = r (w*x+a.run r)-(w*x+a.exact) := by ring
    rw [hident] at hh
    push_cast
    nlinarith

theorem expression_within_neuron_budget (r : ℝ → ℝ) (hr : CorrectRounding r) (t : Expr)
    (hm : t.mass ≤ 16) (hc : t.cost ≤ 129) :
    |t.run r - t.exact| ≤ (1/1024 : ℝ) := by
  have h := expression_error r hr t hm hc
  have hcost : (t.cost : ℝ) ≤ 129 := by exact_mod_cast hc
  have hd := delta_positive
  have hn : (129 : ℝ)*delta ≤ 1/1024 := by norm_num [delta]
  exact h.trans ((mul_le_mul_of_nonneg_right hcost hd.le).trans hn)

end Contribution.Binary32
