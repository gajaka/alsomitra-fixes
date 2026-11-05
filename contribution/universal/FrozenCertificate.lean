import FrozenLeaves
namespace Contribution.Frozen
open Contribution.Universal

theorem all_approximate_bound (xs ys : List ℝ) (hx : InBox exactBox xs)
    (ht : Trace network epsilon xs ys) : ∀ y ∈ ys, y ≤ (cap : ℝ) := by
  exact tree_sound network epsilon cap rootBox certificate certificate_checked xs ys
    (enclosed rootBox exactBox xs root_encloses hx) ht

theorem all_approximate_inputs (xs ys : List ℝ) (hx : InBox exactBox xs)
    (ht : Trace network epsilon xs ys) : ∀ y ∈ ys, y ≤ (1/2 : ℝ) := by
  intro y hy
  have hcap : (cap : ℝ) ≤ (1/2 : ℝ) := by norm_num [cap]
  exact (all_approximate_bound xs ys hx ht y hy).trans hcap

theorem all_exact_inputs (xs : List ℝ) (hx : InBox exactBox xs) :
    ∀ y ∈ network.eval xs, y ≤ (1/2 : ℝ) :=
  all_approximate_inputs xs _ hx (exact_trace network epsilon epsilon_nonnegative xs)

end Contribution.Frozen
