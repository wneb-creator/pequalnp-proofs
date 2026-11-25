import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

namespace PEqualNP.Outside.L_gct_231_aux.TriangleAxis

set_option maxHeartbeats 600000 in
theorem reduced_system_inconsistent (p k s : ℂ)
    (h0 : s^2 + 2*s - 1 = 0)
    (h1 : 4*k^3*s + 4*k^3 - 6*k^2*p*s - 14*k^2*p + 4*k^2*s - 12*k^2 - 4*k*p^2*s + 24*k*p - 4*k*s - 20*k + p^3 + 4*p^2*s + 8*p^2 + 6*p*s - 2*p - 4*s - 4 = 0)
    (h2 : k^2*s - 2*k*p*s - 2*k*p + 2*k + 2*p*s + 2*p - s - 2 = 0)
    (h3 : 4*k^2 - 20*k*p - 24*k - 7*p^2 - 20*p + 4 = 0)
    : False := by
  have h : (4214784 : ℂ) = 0 := by
    linear_combination
      (-266724*k^5 + 1077732*k^4*p + 1398636*k^4 - 977517*k^3*p^2 - 4132800*k^3*p + 683400*k^3 - 222102*k^2*p^3 + 2873745*k^2*p^2 + 3980600*k^2*p + 1385128*k^2 - 139932*k*p^3 - 6837139*k*p^2 - 3932096*k*p - 416676*k + 362034*p^3 + 4940911*p^2 + 3006564*p - 2783764) * h0
      + (289152*k^2*s - 155052*k^2 + 1079688*k*s + 1458384*k - 576240*p - 1368840*s - 1676516) * h1
      + (-889884*k^3*s - 337212*k^3 - 1122588*k^2*p*s + 179460*k^2*p - 6873996*k^2*s - 3446364*k^2 - 111051*k*p^2*s + 33525*k*p^2 - 1357296*k*p*s + 5087616*k*p + 739932*k*s + 23956060*k - 181017*p^2*s + 1655883*p^2 + 176716*p*s + 6628668*p + 2691596*s + 1850428) * h2
      + (83565*k^3*s + 88371*k^3 - 406959*k^2*s - 875049*k^2 + 168463*k*s + 1663169*k - 82320*p^2 - 241472*p + 154931*s - 393547) * h3
  norm_num at h

end PEqualNP.Outside.L_gct_231_aux.TriangleAxis
