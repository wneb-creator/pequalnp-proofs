import Mathlib

namespace PEqualNP.Outside.LiteratureRoute

/-- The optimistic block-cache accounting already costs at least T^(3/2).
This is an arithmetic statement about that particular accounting, not a
lower bound for arbitrary short-input simulation algorithms. -/
lemma optimistic_cache_budget (T b A : ℕ) (hb : 0 < b)
    (hlocal : T * b ≤ A) (hfetch : T * T ≤ A * b) :
    T * T * T ≤ A * A := by
  have h₁ := Nat.mul_le_mul_right (T * T) hlocal
  have h₂ := Nat.mul_le_mul_left A hfetch
  have hscaled : (T * T * T) * b ≤ (A * A) * b := by
    nlinarith
  exact (mul_le_mul_iff_of_pos_right hb).mp hscaled

/-- Composing the optimistic cache budget with a two-thirds-power
verification budget yields no power saving. -/
lemma optimistic_cache_then_two_thirds (T b A C : ℕ) (hb : 0 < b)
    (hlocal : T * b ≤ A) (hfetch : T * T ≤ A * b)
    (hverify : A * A ≤ C * C * C) : T ≤ C := by
  have hcache := optimistic_cache_budget T b A hb hlocal hfetch
  by_contra hnot
  have hlt : C < T := by omega
  have hcubes : C * C * C < T * T * T := by
    simpa [pow_succ] using Nat.pow_lt_pow_left hlt (by decide : 3 ≠ 0)
  omega

end PEqualNP.Outside.LiteratureRoute
