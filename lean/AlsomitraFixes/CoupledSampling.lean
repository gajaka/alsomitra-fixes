import AlsomitraFixes.Defs

/-!
# Optional specification variant: rectangular versus coupled regions

The gliding-drone paper (arXiv:2505.00622v1, Eqs. 23-24) couples a
candidate's own `x` and `y` through `bl ≤ x + y ≤ bh`. The framework paper
(arXiv:2505.00466v2, Appendix A.3) instead specifies anchor-relative
rectangles. Its upstream `Constraint.uniform_sample` draws every
coordinate independently in a box; the `y` range of that box is computed
from the ANCHOR `x`, while the candidate's own `x` is redrawn over its whole
domain, consistently with that local rectangular specification. This optional
variant draws a point of the unit square and maps it
by `decode`: first `x`, then `y` inside the interval allowed by that `x`.

This file proves, over the reals:

* the upstream Property1 box contains points outside the band, for EVERY
  anchor of the `x` domain (`upstream_box_escapes_band`);
* the variant map sends every point of the unit square into the coupled region
  (`decode_sound`) and reaches every point of the region (`decode_complete`).

These results compare different specifications. They do not establish a third
implementation defect in the framework. Only the `(x, y)` pair is modelled;
the other four coordinates are independent intervals in both specifications.
-/

namespace AlsomitraFixes

noncomputable section

/-! ## Upstream box for Property1 -/

/-- The box upstream `uniform_sample` draws from for Property1 at physical
anchor `xa`, in physical units: `x` over its whole domain (its bound is
`nan`, replaced by the domain in `apply_domain_bounds`), and `y` in
`[-2 - xa, 2 - xa]` clipped to the `y` domain. Normalization is affine and
increasing in each coordinate, so the normalized box maps onto this one. -/
def UpstreamBox1 (xa x y : ℝ) : Prop :=
  xMin ≤ x ∧ x ≤ xMax ∧ max (-2 - xa) yMin ≤ y ∧ y ≤ min (2 - xa) yMax

/-- The optional global Property1 variant's condition on the candidate itself. -/
def Band1 (x y : ℝ) : Prop := -2 ≤ x + y ∧ x + y ≤ 2

/-- For every anchor of the `x` domain, the upstream box contains a point
whose own `x + y` lies outside `[-2, 2]`. -/
theorem upstream_box_escapes_band (xa : ℝ) (h1 : xMin ≤ xa) (h2 : xa ≤ xMax) :
    ∃ x y, UpstreamBox1 xa x y ∧ ¬ Band1 x y := by
  by_cases hlt : xa < xMax
  · refine ⟨xMax, 2 - xa, ⟨?_, le_rfl, ?_, ?_⟩, ?_⟩
    · unfold xMin xMax; norm_num
    · refine max_le (by linarith) ?_
      unfold yMin xMax at *; linarith
    · refine le_min le_rfl ?_
      unfold yMax xMin at *; linarith
    · intro hb; linarith [hb.2]
  · have hx : xa = xMax := le_antisymm h2 (not_lt.mp hlt)
    refine ⟨xMin, yMin, ⟨le_rfl, ?_, ?_, ?_⟩, ?_⟩
    · unfold xMin xMax; norm_num
    · refine max_le ?_ le_rfl
      rw [hx]; unfold xMax yMin; norm_num
    · refine le_min ?_ ?_
      · rw [hx]; unfold xMax yMin; norm_num
      · unfold yMin yMax; norm_num
    · intro hb
      have := hb.1
      unfold xMin yMin at this; norm_num at this

/-! ## The optional parameterization, for an arbitrary coupled region -/

/-- A region given by coordinate intervals and a band on `x + y`. -/
structure Coupled where
  lx : ℝ
  ux : ℝ
  ly : ℝ
  uy : ℝ
  bl : ℝ
  bh : ℝ

namespace Coupled

variable (R : Coupled)

/-- Membership in the region. -/
def Mem (x y : ℝ) : Prop :=
  R.lx ≤ x ∧ x ≤ R.ux ∧ R.ly ≤ y ∧ y ≤ R.uy ∧ R.bl ≤ x + y ∧ x + y ≤ R.bh

/-- Tightened `x` limits: positions with an empty `y` interval are removed
(`_AlsomitraRegion.__init__`). -/
def xLo : ℝ := max R.lx (R.bl - R.uy)
def xHi : ℝ := min R.ux (R.bh - R.ly)

/-- The `y` interval allowed by a given `x` (`_AlsomitraRegion._y_limits`). -/
def yLo (x : ℝ) : ℝ := max R.ly (R.bl - x)
def yHi (x : ℝ) : ℝ := min R.uy (R.bh - x)

/-- `decode`, in physical units: `x` first, then `y` given that `x`. -/
def decodeX (u : ℝ) : ℝ := R.xLo + u * (R.xHi - R.xLo)
def decodeY (u v : ℝ) : ℝ :=
  R.yLo (R.decodeX u) + v * (R.yHi (R.decodeX u) - R.yLo (R.decodeX u))

/-- The conditions under which the Python constructor does not raise. -/
structure WellFormed : Prop where
  band : R.bl ≤ R.bh
  yInt : R.ly ≤ R.uy
  xInt : R.xLo ≤ R.xHi

lemma lerp_mem {a b u : ℝ} (hab : a ≤ b) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    a ≤ a + u * (b - a) ∧ a + u * (b - a) ≤ b := by
  constructor
  · nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hab)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hu1) (sub_nonneg.mpr hab)]

variable {R}

lemma yLo_le_yHi (hR : R.WellFormed) {x : ℝ} (hx0 : R.xLo ≤ x) (hx1 : x ≤ R.xHi) :
    R.yLo x ≤ R.yHi x := by
  have h0 : R.bl - R.uy ≤ x := le_trans (le_max_right _ _) hx0
  have h1 : x ≤ R.bh - R.ly := le_trans hx1 (min_le_right _ _)
  unfold yLo yHi
  refine max_le (le_min hR.yInt (by linarith)) (le_min (by linarith) ?_)
  linarith [hR.band]

/-- Soundness: every point of the unit square is mapped into the region. -/
theorem decode_sound (hR : R.WellFormed) {u v : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    R.Mem (R.decodeX u) (R.decodeY u v) := by
  obtain ⟨hx0, hx1⟩ := lerp_mem hR.xInt hu0 hu1
  have hy := yLo_le_yHi hR hx0 hx1
  obtain ⟨hy0, hy1⟩ := lerp_mem hy hv0 hv1
  change R.xLo ≤ R.decodeX u at hx0
  change R.decodeX u ≤ R.xHi at hx1
  change R.yLo (R.decodeX u) ≤ R.decodeY u v at hy0
  change R.decodeY u v ≤ R.yHi (R.decodeX u) at hy1
  have a1 := le_max_left R.lx (R.bl - R.uy)
  have a2 := min_le_left R.ux (R.bh - R.ly)
  have a3 := le_max_left R.ly (R.bl - R.decodeX u)
  have a4 := le_max_right R.ly (R.bl - R.decodeX u)
  have a5 := min_le_left R.uy (R.bh - R.decodeX u)
  have a6 := min_le_right R.uy (R.bh - R.decodeX u)
  unfold xLo xHi yLo yHi at *
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- Completeness: every point of the region is reached from the unit square. -/
theorem decode_complete {x y : ℝ} (h : R.Mem x y) :
    ∃ u v, 0 ≤ u ∧ u ≤ 1 ∧ 0 ≤ v ∧ v ≤ 1 ∧ R.decodeX u = x ∧ R.decodeY u v = y := by
  obtain ⟨hlx, hux, hly, huy, hbl, hbh⟩ := h
  have hx0 : R.xLo ≤ x := max_le hlx (by linarith)
  have hx1 : x ≤ R.xHi := le_min hux (by linarith)
  have hy0 : R.yLo x ≤ y := max_le hly (by linarith)
  have hy1 : y ≤ R.yHi x := le_min huy (by linarith)
  -- Choose `u` so that `decodeX u = x`.
  obtain ⟨u, hu0, hu1, hux'⟩ : ∃ u, 0 ≤ u ∧ u ≤ 1 ∧ R.decodeX u = x := by
    by_cases hw : R.xLo < R.xHi
    · refine ⟨(x - R.xLo) / (R.xHi - R.xLo), ?_, ?_, ?_⟩
      · exact div_nonneg (by linarith) (by linarith)
      · exact (div_le_one (by linarith)).mpr (by linarith)
      · unfold decodeX; field_simp; ring
    · refine ⟨0, le_rfl, zero_le_one, ?_⟩
      unfold decodeX; linarith [not_lt.mp hw]
  -- Then choose `v` for the `y` interval of that same `x`.
  obtain ⟨v, hv0, hv1, hvy⟩ :
      ∃ v, 0 ≤ v ∧ v ≤ 1 ∧ R.yLo x + v * (R.yHi x - R.yLo x) = y := by
    by_cases hw : R.yLo x < R.yHi x
    · refine ⟨(y - R.yLo x) / (R.yHi x - R.yLo x), ?_, ?_, ?_⟩
      · exact div_nonneg (by linarith) (by linarith)
      · exact (div_le_one (by linarith)).mpr (by linarith)
      · field_simp; ring
    · refine ⟨0, le_rfl, zero_le_one, ?_⟩
      linarith [not_lt.mp hw]
  refine ⟨u, v, hu0, hu1, hv0, hv1, hux', ?_⟩
  unfold decodeY
  rw [hux']
  exact hvy

end Coupled

/-! ## Instantiation for the two Alsomitra properties -/

/-- Property1 (paper Eq. 23): `-2 ≤ x + y ≤ 2` on the physical domain. -/
def region1 : Coupled := ⟨xMin, xMax, yMin, yMax, -2, 2⟩

/-- Property2 (paper Eq. 24): `0 ≤ x + y ≤ 2` on the physical domain. -/
def region2 : Coupled := ⟨xMin, xMax, yMin, yMax, 0, 2⟩

theorem region1_wellFormed : region1.WellFormed where
  band := by unfold region1; norm_num
  yInt := by unfold region1 yMin yMax; norm_num
  xInt := by
    unfold Coupled.xLo Coupled.xHi region1 xMin xMax yMin yMax
    exact max_le (le_min (by norm_num) (by norm_num)) (le_min (by norm_num) (by norm_num))

theorem region2_wellFormed : region2.WellFormed where
  band := by unfold region2; norm_num
  yInt := by unfold region2 yMin yMax; norm_num
  xInt := by
    unfold Coupled.xLo Coupled.xHi region2 xMin xMax yMin yMax
    exact max_le (le_min (by norm_num) (by norm_num)) (le_min (by norm_num) (by norm_num))

/-- Every candidate of the optional coupled Property1 variant satisfies its
own band. The historical theorem name is retained for compatibility. -/
theorem fixed_property1_candidates_in_band {u v : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    Band1 (region1.decodeX u) (region1.decodeY u v) := by
  have h := Coupled.decode_sound region1_wellFormed hu0 hu1 hv0 hv1
  exact ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩

end

end AlsomitraFixes
