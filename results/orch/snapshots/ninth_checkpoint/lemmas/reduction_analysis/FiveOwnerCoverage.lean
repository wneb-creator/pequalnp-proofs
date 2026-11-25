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

end PEqualNP.Outside.L_meta_650_aux.FiveOwnerCoverage
