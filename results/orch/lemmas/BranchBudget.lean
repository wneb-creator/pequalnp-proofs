import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.Count
import Mathlib.Data.List.ToFinsupp
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_2592_aux

lemma exact_branch_reads {α : Type*} [DecidableEq α] (operands : List α)
    (branches : Finset α) (two : ∀ w ∈ branches, 2 ≤ operands.count w)
    (tight : operands.length = operands.toFinset.card + branches.card) :
    ∀ w ∈ operands.toFinset, operands.count w = if w ∈ branches then 2 else 1 := by
  let W := operands.toFinset
  have sub : branches ⊆ W := by
    intro w hw
    exact List.mem_toFinset.mpr (List.count_pos_iff.mp (by have := two w hw; omega))
  have low : ∀ w ∈ W, (if w ∈ branches then 2 else 1) ≤ operands.count w := by
    intro w hw
    by_cases hb : w ∈ branches
    · simpa [hb] using two w hb
    · have pos := List.count_pos_iff.mpr (List.mem_toFinset.mp hw)
      simpa [hb] using pos
  have indicator : (∑ w ∈ W, if w ∈ branches then (1 : Nat) else 0) = branches.card := by
    calc
      _ = ∑ w ∈ branches, if w ∈ branches then (1 : Nat) else 0 := by
        symm
        exact Finset.sum_subset sub (fun _ _ h => by simp [h])
      _ = _ := by simp
  have sum_low : (∑ w ∈ W, if w ∈ branches then (2 : Nat) else 1) = operands.length := by
    calc
      _ = ∑ w ∈ W, (1 + if w ∈ branches then (1 : Nat) else 0) := by
        apply Finset.sum_congr rfl
        intro w hw
        split <;> rfl
      _ = W.card + branches.card := by rw [Finset.sum_add_distrib, indicator]; simp
      _ = _ := tight.symm
  have sum_actual : (∑ w ∈ W, operands.count w) = operands.length :=
    List.sum_toFinset_count_eq_length operands
  have eq := (Finset.sum_eq_sum_iff_of_le low).mp (sum_low.trans sum_actual.symm)
  exact fun w hw => (eq w hw).symm

end PEqualNP.Outside.L_meta_2592_aux
