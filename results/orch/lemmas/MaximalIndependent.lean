import PEqualNP.Defs
import Mathlib.Data.Finset.Max

namespace PEqualNP.Outside.L_meta_2592_aux

lemma exists_maximal_independent_superset {α : Type} [Fintype α] [DecidableEq α]
    (E : List (α × α)) (S : Finset α)
    (independent : ∀ e ∈ E, ¬ (e.1 ∈ S ∧ e.2 ∈ S)) :
    ∃ M : Finset α, S ⊆ M ∧ (∀ e ∈ E, ¬ (e.1 ∈ M ∧ e.2 ∈ M)) ∧
      ∀ T : Finset α, M ⊆ T → (∀ e ∈ E, ¬ (e.1 ∈ T ∧ e.2 ∈ T)) → T = M := by
  classical
  let candidates := (Finset.univ : Finset (Finset α)).filter
    (fun T => S ⊆ T ∧ ∀ e ∈ E, ¬ (e.1 ∈ T ∧ e.2 ∈ T))
  have nonempty : candidates.Nonempty := by
    refine ⟨S, ?_⟩
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Finset.Subset.refl S, independent⟩
  obtain ⟨M, member, largest⟩ := Finset.exists_max_image candidates Finset.card nonempty
  obtain ⟨contains, free⟩ := (Finset.mem_filter.mp member).2
  refine ⟨M, contains, free, ?_⟩
  intro T bigger tFree
  have tMember : T ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨contains.trans bigger, tFree⟩
  exact (Finset.eq_of_subset_of_card_le bigger (largest T tMember)).symm

lemma maximal_independent_extension_preserves_operand {α : Type}
    [Fintype α] [DecidableEq α] (E : List (α × α)) (S : Finset α)
    (independent : ∀ e ∈ E, ¬ (e.1 ∈ S ∧ e.2 ∈ S))
    (h : (α → Bool) → Bool) (mono : Monotone h)
    (positive : h (fun i => decide (i ∈ S)) = true) :
    ∃ M : Finset α, S ⊆ M ∧ (∀ e ∈ E, ¬ (e.1 ∈ M ∧ e.2 ∈ M)) ∧
      (∀ T : Finset α, M ⊆ T → (∀ e ∈ E, ¬ (e.1 ∈ T ∧ e.2 ∈ T)) → T = M) ∧
      h (fun i => decide (i ∈ M)) = true := by
  obtain ⟨M, contains, free, maximal⟩ := exists_maximal_independent_superset E S independent
  refine ⟨M, contains, free, maximal, ?_⟩
  have small : (fun i => decide (i ∈ S)) ≤ (fun i => decide (i ∈ M)) := by
    intro i
    exact Bool.le_iff_imp.mpr (fun hi => decide_eq_true (contains (of_decide_eq_true hi)))
  have bound := mono small
  rw [positive] at bound
  cases value : h (fun i => decide (i ∈ M)) with
  | false =>
    rw [value] at bound
    exact False.elim ((by decide : ¬ ((true : Bool) ≤ false)) bound)
  | true => rfl

end PEqualNP.Outside.L_meta_2592_aux
