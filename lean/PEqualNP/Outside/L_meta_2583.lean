import Mathlib.Tactic.Linarith

namespace PEqualNP.Outside.L_meta_2583_aux

lemma cover_large_of_missing_lt_degree
    (N d t u : ℕ) (hud : u < d)
    (hcover : N * d ≤ d * t + u) : N ≤ t := by
  by_contra h
  have hstep : t + 1 ≤ N := by omega
  have hmul := Nat.mul_le_mul_right d hstep
  nlinarith

lemma cover_large_of_few_missing
    (N d t u : ℕ) (hd : 3 ≤ d) (hu : u ≤ 2)
    (hcover : N * d ≤ d * t + u) : N ≤ t := by
  exact cover_large_of_missing_lt_degree N d t u (by omega) hcover

lemma lower_bound_of_penalty_covers_missing
    (N d size t u j z r : ℕ)
    (hud : u < d)
    (hcover : N * d ≤ d * t + u)
    (hledger : N * d + t + 2 * z + j + r ≤ size + u + 1)
    (hpenalty : u ≤ 2 * z + j + r) :
    N * d + N ≤ size + 1 := by
  have hNt := cover_large_of_missing_lt_degree N d t u hud hcover
  omega

lemma small_uncovered_lower_bound
    (N d size t u j z r : ℕ)
    (hd : 3 ≤ d) (hu : u ≤ 2)
    (hcover : N * d ≤ d * t + u)
    (hledger : N * d + t + 2 * z + j + r ≤ size + u + 1)
    (hzero_or_junk : u = 0 ∨ 2 ≤ j) :
    N * d + N ≤ size + 1 := by
  have hNt := cover_large_of_few_missing N d t u hd hu hcover
  have huj : u ≤ j := by
    rcases hzero_or_junk with hzero | hjunk
    · omega
    · omega
  omega

lemma three_uncovered_lower_bound
    (N d size t u j z r : ℕ)
    (hd : 4 ≤ d) (hu : u ≤ 3)
    (hcover : N * d ≤ d * t + u)
    (hledger : N * d + t + 2 * z + j + r ≤ size + u + 1)
    (hzero_or_penalty : u = 0 ∨ 3 ≤ 2 * z + j + r) :
    N * d + N ≤ size + 1 := by
  apply lower_bound_of_penalty_covers_missing N d size t u j z r
    (by omega) hcover hledger
  rcases hzero_or_penalty with hzero | hpenalty <;> omega

end PEqualNP.Outside.L_meta_2583_aux
