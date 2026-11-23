import Mathlib

namespace PEqualNP.Outside.FP3Strategy

def BlockMinimum (height : ℕ → ℕ) (B r m : ℕ) : Prop :=
  (∀ i : ℕ, i < B → m ≤ height (r * B + i)) ∧
    ∃ i : ℕ, i < B ∧ height (r * B + i) = m

lemma exists_block_minimum (height : ℕ → ℕ) (B r : ℕ) (hB : 0 < B) :
    ∃ m : ℕ, BlockMinimum height B r m := by
  classical
  have hex : ∃ m : ℕ, ∃ i : ℕ, i < B ∧ height (r * B + i) = m :=
    ⟨height (r * B), 0, hB, by simp⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  intro i hi
  exact Nat.find_min' hex ⟨i, hi, rfl⟩

lemma block_minimum_unique (height : ℕ → ℕ) (B r m n : ℕ)
    (hm : BlockMinimum height B r m) (hn : BlockMinimum height B r n) : m = n := by
  obtain ⟨i, hi, hmi⟩ := hm.2
  obtain ⟨j, hj, hnj⟩ := hn.2
  have hmn := hm.1 j hj
  have hnm := hn.1 i hi
  omega

lemma exists_minimum_table (height : ℕ → ℕ) (B : ℕ) (hB : 0 < B) :
    ∃ minimum : ℕ → ℕ, ∀ r : ℕ, BlockMinimum height B r (minimum r) := by
  exact Classical.axiomOfChoice (fun r => exists_block_minimum height B r hB)

lemma quotient_before_block (B j r : ℕ) (hB : 0 < B) (hjr : j / B < r) :
    j < r * B := by
  have hmul := Nat.mul_le_mul_right B (show j / B + 1 ≤ r by omega)
  have hrem := Nat.mod_lt j hB
  have hsplit : j % B + j / B * B = j := by
    simpa [Nat.mul_comm] using Nat.mod_add_div j B
  rw [Nat.add_mul, one_mul] at hmul
  omega

lemma block_before_quotient (B r t i : ℕ) (hrt : r < t / B) (hi : i < B) :
    r * B + i < t := by
  have hmul := Nat.mul_le_mul_right B (show r + 1 ≤ t / B by omega)
  have hdiv := Nat.div_mul_le_self t B
  rw [Nat.add_mul, one_mul] at hmul
  omega

def EdgeBlockDip (height : ℕ → ℕ) (B j t threshold : ℕ) : Prop :=
  ∃ k : ℕ, j < k ∧ k ≤ t ∧
    (k / B = j / B ∨ k / B = t / B) ∧ height k ≤ threshold

def InteriorBlockDip (minimum : ℕ → ℕ) (B j t threshold : ℕ) : Prop :=
  ∃ r : ℕ, j / B < r ∧ r < t / B ∧ minimum r ≤ threshold

lemma interval_dip_by_block_minima (height minimum : ℕ → ℕ)
    (B R j t threshold : ℕ) (hB : 0 < B) (ht : t ≤ R * B)
    (hminimum : ∀ r : ℕ, r < R → BlockMinimum height B r (minimum r)) :
    (∃ k : ℕ, j < k ∧ k ≤ t ∧ height k ≤ threshold) ↔
      EdgeBlockDip height B j t threshold ∨ InteriorBlockDip minimum B j t threshold := by
  have htq : t / B ≤ R := by
    apply Nat.le_of_mul_le_mul_right _ hB
    exact (Nat.div_mul_le_self t B).trans ht
  constructor
  · rintro ⟨k, hjk, hkt, hk⟩
    by_cases hleft : k / B = j / B
    · exact Or.inl ⟨k, hjk, hkt, Or.inl hleft, hk⟩
    by_cases hright : k / B = t / B
    · exact Or.inl ⟨k, hjk, hkt, Or.inr hright, hk⟩
    have hjq : j / B ≤ k / B := Nat.div_le_div_right hjk.le
    have hkq : k / B ≤ t / B := Nat.div_le_div_right hkt
    have hrR : k / B < R := by omega
    have hmin := (hminimum (k / B) hrR).1 (k % B) (Nat.mod_lt k hB)
    have hsplit : k / B * B + k % B = k := by
      simpa [Nat.add_comm, Nat.mul_comm] using Nat.mod_add_div k B
    rw [hsplit] at hmin
    exact Or.inr ⟨k / B, by omega, by omega, hmin.trans hk⟩
  · rintro (⟨k, hjk, hkt, _, hk⟩ | ⟨r, hjr, hrt, hr⟩)
    · exact ⟨k, hjk, hkt, hk⟩
    · have hrR : r < R := by omega
      obtain ⟨i, hi, hmi⟩ := (hminimum r hrR).2
      refine ⟨r * B + i, ?_, ?_, ?_⟩
      · have hstart := quotient_before_block B j r hB hjr
        omega
      · exact (block_before_quotient B r t i hrt hi).le
      · omega

end PEqualNP.Outside.FP3Strategy
