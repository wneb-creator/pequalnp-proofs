import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2732_aux.OwnerOverlap

theorem biUnion_card_add_one_le {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (E : ι → Finset α) (i j : ι) (e : α)
    (hi : i ∈ I) (hj : j ∈ I) (hij : i ≠ j) (hei : e ∈ E i) (hej : e ∈ E j) :
    (I.biUnion E).card + 1 ≤ ∑ c ∈ I, (E c).card := by
  have hj' : j ∈ I.erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
  have he' : e ∈ (I.erase i).biUnion E := Finset.mem_biUnion.mpr ⟨j, hj', hej⟩
  have hpos : 0 < (E i ∩ (I.erase i).biUnion E).card :=
    Finset.card_pos.mpr ⟨e, Finset.mem_inter.mpr ⟨hei, he'⟩⟩
  have hU : I.biUnion E = E i ∪ (I.erase i).biUnion E := by
    conv_lhs => rw [← Finset.insert_erase hi]
    rw [Finset.biUnion_insert]
  have hcard := Finset.card_union_add_card_inter (E i) ((I.erase i).biUnion E)
  have hbound := Finset.card_biUnion_le (s := I.erase i) (t := E)
  have hsum := Finset.sum_erase_add I (fun c => (E c).card) hi
  rw [hU]
  omega

theorem owner_overlap_budget {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (E : ι → Finset α) (r b : ι → ℕ) (target : Finset α) (A O : ℕ)
    (cover : target ⊆ Finset.univ.biUnion E)
    (localBound : ∀ c, (E c).card ≤ r c + b c)
    (roots : (∑ c, r c) ≤ A + 1) (paid : (∑ c, b c) ≤ O)
    (i j : ι) (e : α) (hij : i ≠ j) (hei : e ∈ E i) (hej : e ∈ E j) :
    target.card ≤ A + O := by
  have hover := biUnion_card_add_one_le Finset.univ E i j e
    (Finset.mem_univ i) (Finset.mem_univ j) hij hei hej
  have hlocal : (∑ c, (E c).card) ≤ (∑ c, r c) + (∑ c, b c) := by
    calc
      _ ≤ ∑ c, (r c + b c) := Finset.sum_le_sum fun c _ => localBound c
      _ = _ := Finset.sum_add_distrib
  have htarget := Finset.card_le_card cover
  omega

end PEqualNP.Outside.L_meta_2732_aux.OwnerOverlap
