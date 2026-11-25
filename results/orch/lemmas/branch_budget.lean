import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031_aux.BranchBudget

lemma weighted_budget {α : Type*} [DecidableEq α]
    (W : Finset α) (output : α) (inputs gates : ℕ) (readers : α → ℕ)
    (output_mem : output ∈ W) (wire_count : W.card = inputs + gates)
    (live_reader : ∀ a ∈ W, a ≠ output → 1 ≤ readers a)
    (fanin_bound : (∑ a ∈ W, readers a) ≤ 2 * gates) :
    inputs + (∑ a ∈ W, (readers a - 1)) ≤ gates + 1 := by
  classical
  have count : (∑ a ∈ W, (if a = output then 0 else 1 : ℕ)) =
      (W.erase output).card := by
    calc
      _ = ∑ a ∈ W, (if a ≠ output then 1 else 0 : ℕ) := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases h : a = output <;> simp [h]
      _ = (W.erase output).card := by
        rw [← Finset.sum_filter]
        simp [Finset.filter_ne']
  have lower : (W.erase output).card + (∑ a ∈ W, (readers a - 1)) ≤
      ∑ a ∈ W, readers a := by
    rw [← count, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a ha
    by_cases h : a = output
    · simp only [h, ↓reduceIte, zero_add]
      exact Nat.sub_le _ _
    · have positive := live_reader a ha h
      simp only [h, ↓reduceIte]
      omega
  have erased := Finset.card_erase_add_one output_mem
  omega

lemma branch_count_le_surplus {α : Type*} [DecidableEq α]
    (W : Finset α) (readers : α → ℕ) :
    (W.filter fun a => 2 ≤ readers a).card ≤ ∑ a ∈ W, (readers a - 1) := by
  classical
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro a _
  by_cases h : 2 ≤ readers a
  · simp only [h, ↓reduceIte]
    omega
  · simp [h]

end PEqualNP.Outside.L_meta_1031_aux.BranchBudget
