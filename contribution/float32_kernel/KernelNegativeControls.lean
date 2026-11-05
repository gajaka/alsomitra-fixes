import FrozenRounding
import ReductionExistence

set_option autoImplicit false
noncomputable section
namespace Contribution.Binary32.Controls
open Contribution.Universal

theorem reject_bad_rounding : ¬ CorrectRounding (fun _ => 100) := by
  intro h
  have he := nearest_error 0 100 (by norm_num) (h 0 (by norm_num))
  norm_num [delta] at he

theorem reject_insufficient_budget : ¬ ((129 : ℝ)*delta ≤ 1/10000) := by
  norm_num [delta]

theorem reject_duplicated_terms :
    ¬ (Expr.add (.product 1 1) (.atom 1)).terms.Perm [1] := by
  intro h
  have hh := h.length_eq
  norm_num [Expr.terms] at hh

theorem reject_invalid_neuron (r : ℝ → ℝ) (hr : CorrectRounding r) :
    ¬ Reduction r ⟨[0],0⟩ [0] 1 := by
  intro h
  have he := reduction_approx r hr ⟨[0],0⟩ [⟨0,0⟩] [0] 1
    (.cons ⟨by norm_num,by norm_num⟩ .nil)
    (by norm_num [massBound,magnitude]) (by norm_num) h
  norm_num [Approx,Neuron.eval,dot] at he

end Contribution.Binary32.Controls
