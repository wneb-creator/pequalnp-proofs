import Mathlib

namespace PEqualNP.Outside.L_meta_4970_aux

lemma irredundant_subfamily {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : Finset α) (Q : α → Finset β) :
    ∃ R : Finset α, R ⊆ F ∧ R.biUnion Q = F.biUnion Q ∧
      ∀ u ∈ R, ∃ b ∈ Q u, ∀ v ∈ R, b ∈ Q v → v = u := by
  classical
  refine Finset.strongInductionOn F ?_
  intro F ih
  by_cases hremove : ∃ u ∈ F, (F.erase u).biUnion Q = F.biUnion Q
  · obtain ⟨u, hu, hsame⟩ := hremove
    obtain ⟨R, hsub, heq, hprivate⟩ := ih (F.erase u) (Finset.erase_ssubset hu)
    exact ⟨R, hsub.trans (Finset.erase_subset _ _), heq.trans hsame, hprivate⟩
  · refine ⟨F, Finset.Subset.refl _, rfl, ?_⟩
    intro u hu
    have hnot : ¬ Q u ⊆ (F.erase u).biUnion Q := by
      intro hsub
      apply hremove
      refine ⟨u, hu, ?_⟩
      ext b
      constructor
      · intro hb
        obtain ⟨v, hv, hq⟩ := Finset.mem_biUnion.mp hb
        exact Finset.mem_biUnion.mpr ⟨v, (Finset.mem_erase.mp hv).2, hq⟩
      · intro hb
        obtain ⟨v, hv, hq⟩ := Finset.mem_biUnion.mp hb
        by_cases h : v = u
        · subst v
          exact hsub hq
        · exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_erase.mpr ⟨h, hv⟩, hq⟩
    obtain ⟨b, hb, hout⟩ := Finset.not_subset.mp hnot
    refine ⟨b, hb, ?_⟩
    intro v hv hbv
    by_contra hne
    exact hout (Finset.mem_biUnion.mpr ⟨v, Finset.mem_erase.mpr ⟨hne, hv⟩, hbv⟩)

end PEqualNP.Outside.L_meta_4970_aux
