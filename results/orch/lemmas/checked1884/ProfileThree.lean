import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1884_aux.ProfileThree

lemma at_least_three {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (S : Finset α) (N : α → Finset β) (P : α → Finset γ) (R : Finset γ)
    (hsize : 3 ≤ S.card) (hall : 4 ≤ (S.biUnion N).card)
    (hpair : ∀ c ∈ S, ∀ d ∈ S, c ≠ d → 3 ≤ (N c ∪ N d).card)
    (hnonempty : ∀ c ∈ S, (P c).Nonempty) (hsub : ∀ c ∈ S, P c ⊆ R)
    (hbudget : ∀ c ∈ S,
      ((S.filter fun x => P x ⊆ P c).biUnion N).card ≤ (P c).card + 1) :
    3 ≤ R.card := by
  by_contra hsmall
  have small : R.card ≤ 2 := by omega
  have pone (c : α) (hc : c ∈ S) : (P c).card = 1 := by
    have hpos := Finset.card_pos.mpr (hnonempty c hc)
    have hlim := Finset.card_le_card (hsub c hc)
    by_contra hnot
    have htwo : (P c).card = 2 := by omega
    have heq : P c = R := Finset.eq_of_subset_of_card_le (hsub c hc) (by omega)
    have hf : (S.filter fun x => P x ⊆ P c) = S := by
      apply Finset.filter_eq_self.mpr
      intro x hx
      rw [heq]
      exact hsub x hx
    have hb := hbudget c hc
    rw [hf] at hb
    omega
  have hinj : Set.InjOn P S := by
    intro c hc d hd hsame
    by_contra hne
    have hinc : N c ∪ N d ⊆ (S.filter fun x => P x ⊆ P c).biUnion N := by
      intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_filter.mpr ⟨hc, le_rfl⟩, hz⟩
      · exact Finset.mem_biUnion.mpr
          ⟨d, Finset.mem_filter.mpr ⟨hd, by rw [hsame]⟩, hz⟩
    have hle := Finset.card_le_card hinc
    have hp := hpair c hc d hd hne
    have hb := hbudget c hc
    have ho := pone c hc
    omega
  have hinc : S.image P ⊆ Finset.powersetCard 1 R := by
    intro T hT
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hT
    exact Finset.mem_powersetCard.mpr ⟨hsub c hc, pone c hc⟩
  have hle := Finset.card_le_card hinc
  rw [Finset.card_image_iff.mpr hinj, Finset.card_powersetCard] at hle
  apply hsmall
  simpa using hsize.trans hle

end PEqualNP.Outside.L_meta_1884_aux.ProfileThree
