import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9811.TopFormArithmetic

lemma critical_counts (u t c j o : ℕ)
    (hcover : 14 ≤ u + 2 * t)
    (hsize : 19 + t + 2 * c + j + o ≤ 25 + u)
    (hdirty : 0 < u → 0 < j)
    (hnotone : j ≠ 1)
    (hcleanup : 0 < u → 0 < 2 * c + o) :
    3 ≤ u ∧ (u ≤ 3 → u = 3 ∧ t = 6 ∧ c = 0 ∧ j = 2 ∧ o = 1) := by
  have hu : 0 < u := by omega
  have hj := hdirty hu
  have hp := hcleanup hu
  omega

end PEqualNP.Outside.L_meta_9811.TopFormArithmetic
