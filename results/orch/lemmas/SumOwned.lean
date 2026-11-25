import Mathlib

namespace PEqualNP.Outside.L_meta_4970_aux

lemma owned_support_disjoint {α β : Type*} [DecidableEq α] [DecidableEq β]
    (Q : α → Finset β) (K : Finset ℕ) (supp : ℕ → Finset β)
    {a b : α} (hsep : (Q a ∩ Q b).card ≤ 1) :
    Disjoint (K.filter fun j => 2 ≤ (supp j).card ∧ supp j ⊆ Q a)
      (K.filter fun j => 2 ≤ (supp j).card ∧ supp j ⊆ Q b) := by
  apply Finset.disjoint_left.mpr
  intro j hja hjb
  obtain ⟨_, hlarge, hsa⟩ := Finset.mem_filter.mp hja
  obtain ⟨_, _, hsb⟩ := Finset.mem_filter.mp hjb
  have hcard := Finset.card_le_card (Finset.subset_inter hsa hsb)
  omega

lemma sum_owned_support_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (I : Finset α) (Q : α → Finset β) (K : Finset ℕ) (supp : ℕ → Finset β)
    (hsep : ∀ a ∈ I, ∀ b ∈ I, a ≠ b → (Q a ∩ Q b).card ≤ 1)
    (hcost : ∀ a ∈ I, (Q a).card - 1 ≤
      (K.filter fun j => 2 ≤ (supp j).card ∧ supp j ⊆ Q a).card) :
    ∑ a ∈ I, ((Q a).card - 1) ≤ K.card := by
  let owned := fun a => K.filter fun j => 2 ≤ (supp j).card ∧ supp j ⊆ Q a
  have hdisj : (I : Set α).PairwiseDisjoint owned := by
    intro a ha b hb hab
    exact owned_support_disjoint Q K supp (hsep a ha b hb hab)
  calc
    ∑ a ∈ I, ((Q a).card - 1) ≤ ∑ a ∈ I, (owned a).card :=
      Finset.sum_le_sum (fun a ha => hcost a ha)
    _ = (I.biUnion owned).card := (Finset.card_biUnion hdisj).symm
    _ ≤ K.card := by
      apply Finset.card_le_card
      intro j hj
      obtain ⟨a, _, hja⟩ := Finset.mem_biUnion.mp hj
      exact (Finset.mem_filter.mp hja).1

end PEqualNP.Outside.L_meta_4970_aux
