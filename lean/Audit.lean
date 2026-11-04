import AlsomitraFixes

/-! Axiom audit of the main statements. Each should depend only on
`propext`, `Classical.choice` and `Quot.sound`. -/

open AlsomitraFixes

#print axioms upstream_defaults_swapped
#print axioms defect1_y_interval_empty
#print axioms defect2_hi_agrees_iff
#print axioms exceptional_anchor_in_domain
#print axioms defect2_wrong_at_xMin
#print axioms upstream_box_escapes_band
#print axioms Coupled.decode_sound
#print axioms Coupled.decode_complete
#print axioms region1_wellFormed
#print axioms region2_wellFormed
#print axioms fixed_property1_candidates_in_band
#print axioms paper_theta_strictly_inside_upstream
