import AlsomitraFixes.Defs

/-!
# Property2: swapped thresholds and double normalization

Upstream `AlsomitraProperty2.get_bounds` (revision `616df1e`) computes the
`y` column of the bounds for a physical anchor `xa` as

```
lo_y = -xa                 hi_y = y_threshold - xa
lo = normalize(lo)         hi = normalize(hi)
return apply_domain_bounds(lo, hi)
```

and `apply_domain_bounds` clips with the physical domain and normalizes again:
`normalize(max(lo, min))`, `normalize(min(hi, max))`. The functions below
model exactly that pipeline for the `y` coordinate.
-/

namespace AlsomitraFixes

noncomputable section

/-- Upstream lower `y` bound at physical anchor `xa`, as coded. -/
def upLo (xa : ℝ) : ℝ := ny (max (ny (-xa)) yMin)

/-- Upstream upper `y` bound at physical anchor `xa` with stored
`y_threshold = yth`, as coded. -/
def upHi (yth xa : ℝ) : ℝ := ny (min (ny (yth - xa)) yMax)

/-! ## Defect 1: swapped constructor arguments -/

/-- The three thresholds stored by the precondition. -/
structure P2Thresholds where
  vY : ℝ
  y : ℝ
  omega : ℝ

/-- Upstream `AlsomitraProperty2Constraint.__init__` calls
`AlsomitraProperty2(device, y_threshold, v_y_threshold, omega_threshold)`,
while the precondition's parameters are
`(device, v_y_threshold, y_threshold, omega_threshold)`. Positional binding
therefore stores its first value as `vY` and its second as `y`. -/
def upstreamPrecondition (y_threshold v_y_threshold omega_threshold : ℝ) :
    P2Thresholds :=
  { vY := y_threshold, y := v_y_threshold, omega := omega_threshold }

/-- With the upstream defaults `y_threshold = 2.0`, `v_y_threshold = -0.3`,
the velocity threshold becomes `2` and the band threshold becomes `-0.3`. -/
theorem upstream_defaults_swapped :
    upstreamPrecondition 2 (-3 / 10) (-12 / 100) =
      { vY := 2, y := -3 / 10, omega := -12 / 100 } := rfl

/-- Consequence of defect 1: for EVERY physical anchor `xa`, the upstream
`y` interval is empty (upper bound strictly below lower bound). This holds
through both normalizations and the domain clipping. -/
theorem defect1_y_interval_empty (xa : ℝ) :
    upHi (upstreamPrecondition 2 (-3 / 10) (-12 / 100)).y xa < upLo xa := by
  simp only [upstreamPrecondition, upHi, upLo]
  apply ny_strictMono
  have hlt : ny (-3 / 10 - xa) < ny (-xa) := ny_strictMono (by linarith)
  calc min (ny (-3 / 10 - xa)) yMax ≤ ny (-3 / 10 - xa) := min_le_left _ _
    _ < ny (-xa) := hlt
    _ ≤ max (ny (-xa)) yMin := le_max_left _ _

/-! ## Defect 2: bounds normalized twice -/

/-- The upper `y` bound normalized ONCE, as intended: clip the physical bound
`2 - xa` to the domain, then normalize. This is the reference value used by
`test_upstream_double_normalization_alone`. -/
def intendedHi (xa : ℝ) : ℝ := ny (min (2 - xa) yMax)

/-- The unique fixed point of `ny`. -/
def c : ℝ := -yMin / (yMax - yMin - 1)

lemma ny_eq_self_iff (s : ℝ) : ny s = s ↔ s = c := by
  have hS : yMax - yMin ≠ 0 := ne_of_gt yScale_pos
  have hS1 : yMax - yMin - 1 ≠ 0 := by unfold yMax yMin; norm_num
  unfold ny c
  rw [div_eq_iff hS, eq_div_iff hS1]
  constructor <;> intro h <;> linear_combination -h

/-- Even with the correct threshold `2`, the doubly normalized upstream upper
bound agrees with the intended value only at the single anchor `xa = 2 - c`.
This holds for every anchor with `xMin ≤ xa`, in particular for the whole
`x` domain; `exceptional_anchor_in_domain` shows that `2 - c` lies in it. -/
theorem defect2_hi_agrees_iff (xa : ℝ) (h1 : xMin ≤ xa) :
    upHi 2 xa = intendedHi xa ↔ xa = 2 - c := by
  have hs : 2 - xa < yMax := by unfold xMin yMax at *; linarith
  have hn : ny (2 - xa) < yMax := by
    unfold ny
    rw [div_lt_iff₀ yScale_pos]
    unfold xMin yMax yMin at *
    nlinarith
  unfold upHi intendedHi
  rw [min_eq_left hn.le, min_eq_left hs.le, ny_injective.eq_iff, ny_eq_self_iff]
  constructor <;> intro h <;> linarith

/-- The exceptional anchor lies inside the `x` domain. -/
theorem exceptional_anchor_in_domain : xMin ≤ 2 - c ∧ 2 - c ≤ xMax := by
  unfold c xMin xMax yMin yMax
  constructor <;> norm_num

/-- A concrete instance: at the lower end of the `x` domain the upstream
upper bound is wrong. -/
theorem defect2_wrong_at_xMin : upHi 2 xMin ≠ intendedHi xMin := by
  intro h
  have hx := (defect2_hi_agrees_iff xMin le_rfl).mp h
  unfold c xMin yMin yMax at hx
  norm_num at hx

end

end AlsomitraFixes
