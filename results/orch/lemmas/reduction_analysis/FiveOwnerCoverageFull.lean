import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_650_aux.FiveOwnerCoverage

theorem twenty_cover_five {ι α : Type} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (E : Finset α) (B : ι → Finset α)
    (hi : I.card = 5) (he : E.card = 20)
    (hb : ∀ i ∈ I, (B i).card ≤ 4)
    (hcover : ∀ e ∈ E, ∃ i ∈ I, e ∈ B i) :
    ∀ i ∈ I, (B i).card = 4 := by
  have hsub : E ⊆ I.biUnion B := by
    intro e he
    obtain ⟨i,hi,hb⟩ := hcover e he
    exact Finset.mem_biUnion.mpr ⟨i,hi,hb⟩
  have htotal : 20 ≤ ∑ i ∈ I, (B i).card := by
    have h1 := Finset.card_le_card hsub
    have h2 : (I.biUnion B).card ≤ ∑ i ∈ I, (B i).card := Finset.card_biUnion_le
    omega
  intro i him
  have hc : (I.erase i).card = 4 := by
    have h := Finset.sum_erase_add I (fun _ => (1 : ℕ)) him
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
    omega
  have hrest : (∑ j ∈ I.erase i, (B j).card) ≤ 16 := by
    calc
      _ ≤ ∑ _j ∈ I.erase i, (4 : ℕ) := Finset.sum_le_sum fun j hj =>
        hb j (Finset.mem_of_mem_erase hj)
      _ = 16 := by simp [hc]
  have hs := Finset.sum_erase_add I (fun j => (B j).card) him
  have hu := hb i him
  omega

theorem twenty_cover_distinct {ι α : Type} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (E : Finset α) (B : ι → Finset α)
    (hi : I.card = 5) (he : E.card = 20)
    (hb : ∀ i ∈ I, (B i).card ≤ 4)
    (hcover : ∀ e ∈ E, ∃ i ∈ I, e ∈ B i) :
    ∀ i ∈ I, ∀ j ∈ I, i ≠ j → B i ≠ B j := by
  intro i him j hjm hne heq
  have hsub : E ⊆ (I.erase j).biUnion B := by
    intro e hem
    obtain ⟨k,hkm,hek⟩ := hcover e hem
    by_cases hkj : k = j
    · subst k
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_erase.mpr ⟨hne,him⟩,heq.symm ▸ hek⟩
    · exact Finset.mem_biUnion.mpr ⟨k,Finset.mem_erase.mpr ⟨hkj,hkm⟩,hek⟩
  have hc : (I.erase j).card = 4 := by
    have h := Finset.sum_erase_add I (fun _ => (1 : ℕ)) hjm
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
    omega
  have hs : (∑ k ∈ I.erase j, (B k).card) ≤ 16 := by
    calc
      _ ≤ ∑ _k ∈ I.erase j, (4 : ℕ) := Finset.sum_le_sum fun k hk =>
        hb k (Finset.mem_of_mem_erase hk)
      _ = 16 := by simp [hc]
  have h1 := Finset.card_le_card hsub
  have h2 : ((I.erase j).biUnion B).card ≤ ∑ k ∈ I.erase j, (B k).card :=
    Finset.card_biUnion_le
  omega

end PEqualNP.Outside.L_meta_650_aux.FiveOwnerCoverage
