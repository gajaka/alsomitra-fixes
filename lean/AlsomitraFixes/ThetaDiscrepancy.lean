import AlsomitraFixes.Defs

/-!
# Property1 theta bound: paper versus upstream default

The paper (SAIV 2025, Eq. 23) states `-0.786 ≤ theta ≤ -0.747`. Upstream
`AlsomitraProperty1Constraint` defaults to `theta_threshold = (-0.786, 0.747)`;
`apply_domain_bounds` then clips the upper end to the domain maximum
`-0.068003`.

This file only proves that the two resulting intervals differ and that the
paper's interval is strictly contained in upstream's. It does NOT, and cannot,
establish which interval the authors intended: that is a question about the
specification, not a mathematical fact.
-/

namespace AlsomitraFixes

noncomputable section

/-- Upstream upper theta bound after `apply_domain_bounds`. -/
def upstreamThetaHi : ℝ := min (747 / 1000) thetaMax

theorem upstreamThetaHi_eq : upstreamThetaHi = thetaMax :=
  min_eq_right (by unfold thetaMax; norm_num)

/-- The theta interval stated in the paper. -/
def paperTheta : Set ℝ := Set.Icc (-786 / 1000) (-747 / 1000)

/-- The theta interval upstream actually samples from. The lower end
`-0.786` is above the domain minimum `-0.968479`, so it is not clipped. -/
def upstreamTheta : Set ℝ := Set.Icc (-786 / 1000) upstreamThetaHi

theorem paper_theta_strictly_inside_upstream : paperTheta ⊂ upstreamTheta := by
  unfold paperTheta upstreamTheta
  rw [upstreamThetaHi_eq]
  refine ⟨Set.Icc_subset_Icc le_rfl (by unfold thetaMax; norm_num), ?_⟩
  intro hsub
  have hmem : (-7 / 10 : ℝ) ∈ Set.Icc (-786 / 1000 : ℝ) thetaMax := by
    unfold thetaMax; constructor <;> norm_num
  have := (hsub hmem).2
  norm_num at this

end

end AlsomitraFixes
