module

public import Mathlib

/-!
# Real-number model of the Alsomitra input regions

This file models, over the real numbers, the parts of the upstream
`property-driven-ml` code (revision `616df1e`) that the reported defects
concern. It is a model of the code's arithmetic, not the code itself:
PyTorch evaluates the same formulas in float32/float64, and rounding is not
represented here. The correspondence was established by reading
`src/property_driven_ml/constraints/preconditions.py` and
`src/property_driven_ml/constraints/constraints.py` at that revision; the
Python tests in `tests/test_property2_bugs.py` exercise the same behaviour.

The constants are the six-decimal physical domain of `AlsomitraBase`,
written as exact fractions.
-/

@[expose] public section

namespace AlsomitraFixes

noncomputable section

/-- Lower end of the `x` domain: `0.482421` (`AlsomitraBase.min[4]`). -/
def xMin : ℝ := 482421 / 1000000

/-- Upper end of the `x` domain: `41.714717` (`AlsomitraBase.max[4]`). -/
def xMax : ℝ := 41714717 / 1000000

/-- Lower end of the `y` domain: `-41.681405` (`AlsomitraBase.min[5]`). -/
def yMin : ℝ := -41681405 / 1000000

/-- Upper end of the `y` domain: `4.197234` (`AlsomitraBase.max[5]`). -/
def yMax : ℝ := 4197234 / 1000000

/-- Upper end of the `theta` domain: `-0.068003` (`AlsomitraBase.max[3]`). -/
def thetaMax : ℝ := -68003 / 1000000

/-- Upstream `normalize` on the `y` coordinate:
`(t - min) / (max - min)` (`AlsomitraBase.normalize`). -/
def ny (t : ℝ) : ℝ := (t - yMin) / (yMax - yMin)

lemma yScale_pos : 0 < yMax - yMin := by
  unfold yMax yMin; norm_num

lemma ny_strictMono : StrictMono ny := by
  intro a b h
  unfold ny
  exact div_lt_div_of_pos_right (by linarith) yScale_pos

lemma ny_injective : Function.Injective ny := ny_strictMono.injective

end

end AlsomitraFixes
