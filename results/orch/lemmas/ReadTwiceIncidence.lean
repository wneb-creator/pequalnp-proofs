import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.ReadTwiceIncidence

lemma slot_partition (n : ℕ) (slots : List ℕ) :
    (slots.filter (fun w => w < n)).length +
      (slots.filter (fun w => n ≤ w)).length = slots.length := by
  induction slots with
  | nil => simp
  | cons w slots ih =>
    by_cases h : w < n
    · simp only [List.filter_cons, h, decide_true, Bool.true_eq, reduceIte,
        Nat.not_le_of_lt h, decide_false, Bool.false_eq_true, List.length_cons]
      omega
    · simp only [List.filter_cons, h, decide_false, Bool.false_eq_true, reduceIte,
        Nat.le_of_not_gt h, decide_true, Bool.true_eq, List.length_cons]
      omega

lemma primary_slot_budget (n B : ℕ) (slots : List ℕ)
    (internal : Finset ℕ) (out : ℕ)
    (cardinal : internal.card = B)
    (above : ∀ w ∈ internal, n ≤ w)
    (productive : ∀ w ∈ internal, w = out ∨ w ∈ slots)
    (capacity : slots.length ≤ 2 * B) :
    (slots.filter (fun w => w < n)).length ≤ B + 1 := by
  have contain : internal ⊆ insert out (slots.filter (fun w => n ≤ w)).toFinset := by
    intro w hw
    rcases productive w hw with rfl | hs
    · simp
    · exact Finset.mem_insert_of_mem (by simp [hs, above w hw])
  have cardBound := Finset.card_le_card contain
  have insertBound := Finset.card_insert_le out (slots.filter (fun w => n ≤ w)).toFinset
  have listBound := List.toFinset_card_le (slots.filter (fun w => n ≤ w))
  have partition := slot_partition n slots
  rw [cardinal] at cardBound
  omega

lemma singleton_budget {n : ℕ} (reads : Fin n → ℕ)
    (essential : ∀ i, 1 ≤ reads i) :
    2 * n ≤ (∑ i, reads i) + (Finset.univ.filter (fun i => reads i = 1)).card := by
  have pointwise : ∀ i, 2 ≤ reads i + if reads i = 1 then 1 else 0 := by
    intro i
    have hi := essential i
    split_ifs <;> omega
  have summed := Finset.sum_le_sum (s := Finset.univ) (fun i _ => pointwise i)
  simpa [Finset.sum_add_distrib, Nat.mul_comm] using summed

lemma three_singletons (reads : Fin 10 → ℕ)
    (essential : ∀ i, 1 ≤ reads i) (budget : (∑ i, reads i) ≤ 17) :
    3 ≤ (Finset.univ.filter (fun i => reads i = 1)).card := by
  have count := singleton_budget reads essential
  omega

end PEqualNP.Outside.L_meta_2592_aux.ReadTwiceIncidence
