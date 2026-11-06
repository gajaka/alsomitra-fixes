import PropertyTransfer
import RationalFeatures

/-! Executable rational evaluation linked to the existing real checkpoint
semantics, including all three ReLUs. Python search is not trusted. -/
set_option autoImplicit false
namespace Contribution.Reduction.PropertyDecision
open Contribution.Universal PropertyTransfer

def evalQ (net : Network) (xs : List ℚ) : List ℚ :=
  RationalFeatures.layerQ net.third
    (RationalFeatures.layerQ net.second (RationalFeatures.layerQ net.first xs))

theorem evalQ_cast (net : Network) (xs : List ℚ) :
    (evalQ net xs).map (fun q : ℚ => (q : ℝ)) =
      eval net (xs.map (fun q : ℚ => (q : ℝ))) := by
  unfold evalQ eval Network.eval
  rw [RationalFeatures.layer_cast, RationalFeatures.layer_cast, RationalFeatures.layer_cast]

theorem exact_output (net : Network) (x : Input) (xs : List ℚ) (v : ℚ)
    (hx : x.val = xs.map (fun q : ℚ => (q : ℝ))) (hv : evalQ net xs = [v]) :
    output net x = (v : ℝ) := by
  unfold output
  rw [hx, ← evalQ_cast, hv]
  rfl

theorem refutes {spec : Specification} {f : Input → ℝ} {x : Input}
    (h : ViolatesAt spec f x) : ¬ Satisfies spec f := by
  intro hs
  exact h.2 (hs x h.1)

end Contribution.Reduction.PropertyDecision
