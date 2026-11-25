import Mathlib

namespace PEqualNP.Outside.L_meta_4970.OrCount

lemma biUnion_erase_dominated {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : Finset α) (Q : α → Finset β) (u v : α)
    (hv : v ∈ F) (huv : u ≠ v) (hdom : Q u ⊆ Q v) :
    (F.erase u).biUnion Q = F.biUnion Q := by
  ext b
  constructor
  · intro hb
    obtain ⟨w, hw, hbw⟩ := Finset.mem_biUnion.mp hb
    exact Finset.mem_biUnion.mpr ⟨w, (Finset.mem_erase.mp hw).2, hbw⟩
  · intro hb
    obtain ⟨w, hw, hbw⟩ := Finset.mem_biUnion.mp hb
    by_cases hwu : w = u
    · subst w
      exact Finset.mem_biUnion.mpr
        ⟨v, Finset.mem_erase.mpr ⟨huv.symm, hv⟩, hdom hbw⟩
    · exact Finset.mem_biUnion.mpr
        ⟨w, Finset.mem_erase.mpr ⟨hwu, hw⟩, hbw⟩

lemma undominated_rt_subfamily {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : Finset α) (Q : α → Finset β) :
    ∃ R : Finset α, R ⊆ F ∧ R.biUnion Q = F.biUnion Q ∧
      ∀ u ∈ R, ∀ v ∈ R, u ≠ v → ¬ Q u ⊆ Q v := by
  classical
  refine Finset.strongInductionOn F ?_
  intro F ih
  by_cases hanti : ∀ u ∈ F, ∀ v ∈ F, u ≠ v → ¬ Q u ⊆ Q v
  · exact ⟨F, Finset.Subset.refl _, rfl, hanti⟩
  · push Not at hanti
    obtain ⟨u, hu, v, hv, huv, hdom⟩ := hanti
    obtain ⟨R, hRF, hRU, hRanti⟩ := ih (F.erase u) (Finset.erase_ssubset hu)
    exact ⟨R, hRF.trans (Finset.erase_subset _ _),
      hRU.trans (biUnion_erase_dominated F Q u v hv huv hdom), hRanti⟩

end PEqualNP.Outside.L_meta_4970.OrCount
