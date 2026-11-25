import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_231.trace

set_option maxHeartbeats 1000000 in
theorem case2_endpoint_one (U V : ℂ)
    (hq : 10*U^2 - 8*U*V - V^2 + 36 = 0)
    (hc : 8*U^3 + 8*U^2*V - 112*U^2 + 4*U*V^2 - 40*U*V - V^3 + 7*V^2 - 36 = 0)
    (hr : 5*U - 2*V + 12 = 0) : U = 0 ∧ V = 6 := by
  have hu : U = 0 := by
    linear_combination
      (115*U/62316 - 5843/405054) * hq + (25/31158 : ℂ) * hc +
      (-155*U^2/31158 - 5*U*V/15579 + 3967*U/67509 - 25*V^2/62316 +
        514*V/67509 + 1028/22503) * hr
  refine ⟨hu, ?_⟩
  linear_combination (-1/2 : ℂ) * hr + (5/2 : ℂ) * hu

set_option maxHeartbeats 1000000 in
theorem case2_endpoint_sixteen_thirds (U V : ℂ)
    (hq : 4*U^2 + 2*U*V - 3*V^2 - 48 = 0)
    (hr : U - 3*V - 4 = 0)
    (hl : U*(U - 3*V + 8) = 0) : False := by
  have hu : U = 0 := by
    linear_combination (1/12 : ℂ) * hl - (U/12) * hr
  have hv : V = -4/3 := by
    linear_combination (-1/3 : ℂ) * hr + (1/3 : ℂ) * hu
  rw [hu, hv] at hq
  norm_num at hq

end PEqualNP.Outside.L_gct_231.trace

#print axioms PEqualNP.Outside.L_gct_231.trace.case2_endpoint_one
#print axioms PEqualNP.Outside.L_gct_231.trace.case2_endpoint_sixteen_thirds
