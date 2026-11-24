import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1395

def Cert (r m x k : ℕ) : Prop :=
  (4 * (k : ℤ) ^ 2 - 1) * (m : ℤ) + 2 * (r : ℤ) ≤ (4 * (k : ℤ) - 1) * (x : ℤ)

lemma space {r m x k : ℕ} (hm : 0 < m) (hk : 0 < k) (hc : Cert r m x k) :
    k ≤ x ∧ (1 < k → k < x) := by
  have ha : (1 : ℤ) ≤ m := by omega
  have hb : (1 : ℤ) ≤ k := by omega
  have he : 0 ≤ 4 * (k : ℤ) ^ 2 - 1 := by nlinarith [sq_nonneg ((k : ℤ) - 1)]
  have hf := mul_nonneg he (sub_nonneg.mpr ha)
  have hg : 0 < 4 * (k : ℤ) - 1 := by omega
  have hr : 0 ≤ (r : ℤ) := by positivity
  unfold Cert at hc
  constructor
  · by_contra! h
    have hi : (x : ℤ) < k := by exact_mod_cast h
    nlinarith [mul_pos hg (sub_pos.mpr hi)]
  · intro h
    by_contra! h'
    have hi : (x : ℤ) ≤ k := by exact_mod_cast h'
    have hj : (1 : ℤ) < k := by exact_mod_cast h
    nlinarith [mul_nonneg hg.le (sub_nonneg.mpr hi)]

lemma raiseWidth {r m x k : ℕ} (hk : 0 < k) (hc : Cert r m x k) (h : k*x < r) :
    Cert r m x (k+1) := by
  have hk' : 0 < 2 * (k : ℤ) - 1 := by omega
  have h' : (k : ℤ) * x < r := by exact_mod_cast h
  unfold Cert at *
  have hz : (2 * (k : ℤ) + 1) * m ≤ x := by
    by_contra! hh
    nlinarith [mul_pos hk' (sub_pos.mpr hh)]
  push_cast
  nlinarith

lemma pickWidth {r m x k : ℕ} (hm : 0 < m) (hk : 0 < k) (hc : Cert r m x k) :
    ∃ d : ℕ, 0 < d ∧ Cert r m x d ∧ r ≤ d*x := by
  by_cases h : r ≤ k*x
  · exact ⟨k, hk, hc, h⟩
  · have hfit := (space hm hk hc).1
    have hx : 0 < x := by omega
    have hsmall := Nat.le_mul_of_pos_right k hx
    exact pickWidth hm (Nat.succ_pos k) (raiseWidth hk hc (by omega))
termination_by r-k
decreasing_by omega

lemma advance {q r m x k : ℕ} (hq : 2 ≤ q) (hx : x ≤ q+1) (hm : 0 < m) (hk : 0 < k)
    (hc : Cert r m x k) :
    ∃ d : ℕ, 0 < d ∧ d ≤ x ∧ d ≤ q ∧ r ≤ d*x ∧ Cert r (m-1) (x-d) d := by
  obtain ⟨d, hd, hc', hr⟩ := pickWidth hm hk hc
  obtain ⟨hf, hg⟩ := space hm hd hc'
  refine ⟨d, hd, hf, by omega, hr, ?_⟩
  have hh : ((m-1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
  have hi : ((x-d : ℕ) : ℤ) = (x : ℤ) - d := by omega
  have hj : (1 : ℤ) ≤ d := by omega
  unfold Cert at hc' ⊢
  rw [hh, hi]
  nlinarith only [hc', hj]

lemma start {q n r : ℕ} (hn : 0 < n) (h : n ≤ q+1)
    (hr : r*(2*n) ≤ q*(q+1-n)) : ∃ k : ℕ, 0 < k ∧ Cert r n (q+1) k := by
  let x := q + 1
  let k := (x + n) / (2 * n)
  have hnx : n ≤ x := h
  have hden : 0 < 2 * n := by omega
  have hk : 0 < k := Nat.div_pos (by omega) hden
  refine ⟨k, hk, ?_⟩
  change Cert r n x k
  have hmod := Nat.mod_lt (x + n) hden
  have hdiv : (x + n) % (2 * n) + (2 * n) * k = x + n :=
    Nat.mod_add_div (x + n) (2 * n)
  have hlo : x ≤ (2 * n) * k + n := by omega
  have hhi : (2 * n) * k ≤ x + n := by omega
  have hloZ : (x : ℤ) ≤ 2 * (n : ℤ) * (k : ℤ) + (n : ℤ) := by exact_mod_cast hlo
  have hhiZ : 2 * (n : ℤ) * (k : ℤ) ≤ (x : ℤ) + (n : ℤ) := by exact_mod_cast hhi
  let d : ℤ := 2 * (n : ℤ) * (k : ℤ) - (x : ℤ)
  have hdlo : 0 ≤ (n : ℤ) + d := by dsimp [d]; linarith only [hloZ]
  have hdhi : 0 ≤ (n : ℤ) - d := by dsimp [d]; linarith only [hhiZ]
  have hsquare := mul_nonneg hdhi hdlo
  dsimp [d] at hsquare
  have hqx : q ≤ x := Nat.le_succ q
  have hbudgetN : r * (2 * n) ≤ x * (x - n) :=
    le_trans hr (Nat.mul_le_mul_right (x - n) hqx)
  have hbudget : (r : ℤ) * (2 * (n : ℤ)) ≤ (x : ℤ) * ((x : ℤ) - (n : ℤ)) := by
    rw [← Nat.cast_sub hnx]
    exact_mod_cast hbudgetN
  have hscaled : 0 ≤ (n : ℤ) *
      ((4 * (k : ℤ) - 1) * (x : ℤ) - ((4 * (k : ℤ) ^ 2 - 1) * (n : ℤ) + 2 * (r : ℤ))) := by
    nlinarith only [hsquare, hbudget]
  have hnZ : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hscaled hnZ)

lemma le_foldr (f : ℕ → ℕ) (xs : List ℕ) {j : ℕ} (hj : j ∈ xs) :
    f j ≤ xs.foldr (fun i acc => max acc (f i)) 0 := by
  induction xs with
  | nil => simp at hj
  | cons a as ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp hj with h | h
    · subst a
      exact le_max_right _ _
    · exact (ih h).trans (le_max_left _ _)

lemma base_bound {q b x d K : ℕ} (hbx : b + x = q + 1) (hdq : d ≤ q) (hdK : d ≤ K) :
    q * x * d ≤ ((q ^ 2 + q + 1) -
      (if b = 0 then 0 else min (q ^ 2 + q + 1) (b * q + 1))) * min K q := by
  have hsum : b * q + 1 + q * x = q ^ 2 + q + 1 := by
    calc
      _ = (b + x) * q + 1 := by ring
      _ = _ := by rw [hbx]; ring
  have hcap : q * x ≤ (q ^ 2 + q + 1) -
      (if b = 0 then 0 else min (q ^ 2 + q + 1) (b * q + 1)) := by
    by_cases hb : b = 0
    · rw [if_pos hb, Nat.sub_zero]
      omega
    · rw [if_neg hb, min_eq_right (show b * q + 1 ≤ q ^ 2 + q + 1 by omega)]
      omega
  exact Nat.mul_le_mul hcap (le_min hdK hdq)

lemma tree {q : ℕ} {G : ℕ → ℕ → ℕ → ℕ} (hq : 2 ≤ q)
    (g0 : ∀ b K : ℕ, G 0 b K = ((q ^ 2 + q + 1) -
      (if b = 0 then 0 else min (q ^ 2 + q + 1) (b * q + 1))) * min K q)
    (gs : ∀ t b K : ℕ, G (t + 1) b K = (List.range (K + 1)).foldr
      (fun (j acc : ℕ) => max acc (min (G t (b + j) (K - j)) (G t b j))) 0)
    (t r m b x k : ℕ) (hm : 2 ^ t ≤ m) (hbx : b + x = q + 1) (hk : 0 < k)
    (hc : Cert r m x k) :
    ∃ L ≤ x, ∃ k' > 0, Cert r (m - 2 ^ t) (x - L) k' ∧
      ∀ K ≥ L, q * r ≤ G t b K := by
  induction t generalizing m b x k with
  | zero =>
    have hm' : 0 < m := by
      simp only [pow_zero] at hm
      omega
    obtain ⟨d, hd, hdx, hdq, hdr, hcd⟩ := advance hq (by omega) hm' hk hc
    refine ⟨d, hdx, d, hd, hcd, ?_⟩
    intro K hdK
    rw [g0]
    calc
      q * r ≤ q * (d * x) := Nat.mul_le_mul_left q hdr
      _ = q * x * d := by ring
      _ ≤ _ := base_bound hbx hdq hdK
  | succ t ih =>
    have hm' : 2 ^ t + 2 ^ t ≤ m := by
      simpa only [pow_succ, Nat.mul_two] using hm
    obtain ⟨Ll, hlx, kl, hkl, hcl, hgl⟩ := ih m b x k (by omega) hbx hk hc
    have hbxl : (b + Ll) + (x - Ll) = q + 1 := by omega
    obtain ⟨Lr, hrx, kr, hkr, hcr, hgr⟩ :=
      ih (m - 2 ^ t) (b + Ll) (x - Ll) kl (by omega) hbxl hkl hcl
    refine ⟨Ll + Lr, by omega, kr, hkr, ?_, ?_⟩
    · simpa only [pow_succ, Nat.mul_two, Nat.sub_sub] using hcr
    · intro K hK
      rw [gs]
      have hj : Ll ∈ List.range (K + 1) := List.mem_range.mpr (by omega)
      exact (le_min (hgr (K - Ll) (by omega)) (hgl Ll le_rfl)).trans
        (le_foldr (fun j => min (G t (b + j) (K - j)) (G t b j)) _ hj)

end PEqualNP.Outside.L_meta_1395

open PEqualNP.Outside.L_meta_1395 in
theorem PEqualNP.Outside.L_meta_1395 : ∀ (q s : ℕ), 2 ≤ q → ∀ G : ℕ → ℕ → ℕ → ℕ, (∀ b K : ℕ, G 0 b K = ((q ^ 2 + q + 1) - (if b = 0 then 0 else min (q ^ 2 + q + 1) (b * q + 1))) * min K q) → (∀ t b K : ℕ, G (t + 1) b K = (List.range (K + 1)).foldr (fun (j acc : ℕ) => max acc (min (G t (b + j) (K - j)) (G t b j))) 0) → q * (q * (q + 1 - 2 ^ s) / 2 ^ (s + 1)) ≤ G s 0 (q ^ 2 + q + 1) := by
  intro q s hq G hzero hsucc
  let n := 2 ^ s
  have hn : 0 < n := pow_pos (by decide) _
  let r := q * (q+1-n) / (n*2)
  rw [pow_succ]
  change q*r ≤ G s 0 (q^2+q+1)
  by_cases h : n ≤ q+1
  · have hr : r*(2*n) ≤ q*(q+1-n) := by
      rw [Nat.mul_comm 2 n]
      exact Nat.div_mul_le_self _ _
    obtain ⟨k, hk, hc⟩ := start hn h hr
    obtain ⟨L, hL, k', hk', hc', hG⟩ := tree hq hzero hsucc s r n 0 (q+1) k (le_refl n)
      (Nat.zero_add _) hk hc
    exact hG _ (by omega)
  · have hz : q+1-n = 0 := by omega
    simp [r, hz]
