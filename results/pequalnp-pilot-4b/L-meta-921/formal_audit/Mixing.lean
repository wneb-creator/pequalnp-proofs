import Mathlib

namespace Meta921Audit

variable {α : Type*} [DecidableEq α]

theorem large_cross_forces_small_bad_cross
    (L K A B C D : Finset α) (p : α)
    (hL : L.card = 4) (hK : K.card = 4)
    (hinter : L ∩ K = {p})
    (hAB : A ∪ B = L) (hCD : C ∪ D = K)
    (hA : A.card ≤ 3) (hB : B.card ≤ 3)
    (hC : C.card ≤ 3) (hD : D.card ≤ 3)
    (hlarge : 6 ≤ (A ∪ D).card)
    (hnotL : ¬ L ⊆ A ∪ D) (hnotK : ¬ K ⊆ A ∪ D) :
    (B ∪ C).card ≤ 5 ∧ ¬ L ⊆ B ∪ C ∧ ¬ K ⊆ B ∪ C := by
  have hAsub : A ⊆ L := by rw [← hAB]; exact Finset.subset_union_left
  have hBsub : B ⊆ L := by rw [← hAB]; exact Finset.subset_union_right
  have hCsub : C ⊆ K := by rw [← hCD]; exact Finset.subset_union_left
  have hDsub : D ⊆ K := by rw [← hCD]; exact Finset.subset_union_right
  have hpL : p ∈ L := (Finset.mem_inter.mp (by rw [hinter]; simp)).1
  have hpK : p ∈ K := (Finset.mem_inter.mp (by rw [hinter]; simp)).2
  have hcounts := Finset.card_union_add_card_inter A D
  have hAc : A.card = 3 := by omega
  have hDc : D.card = 3 := by omega
  have hzero : (A ∩ D).card = 0 := by omega
  have hdisj : Disjoint A D := Finset.disjoint_iff_inter_eq_empty.mpr
    (Finset.card_eq_zero.mp hzero)
  have hpnotA : p ∉ A := by
    intro hpA
    have hpnotD : p ∉ D := fun hpD => Finset.disjoint_left.mp hdisj hpA hpD
    have hins : insert p D = K := by
      apply Finset.eq_of_subset_of_card_le
      · exact Finset.insert_subset hpK hDsub
      · simp [Finset.card_insert_of_notMem hpnotD, hDc, hK]
    apply hnotK
    rw [← hins]
    exact Finset.insert_subset (Finset.mem_union_left D hpA) Finset.subset_union_right
  have hpnotD : p ∉ D := by
    intro hpD
    have hins : insert p A = L := by
      apply Finset.eq_of_subset_of_card_le
      · exact Finset.insert_subset hpL hAsub
      · simp [Finset.card_insert_of_notMem hpnotA, hAc, hL]
    apply hnotL
    rw [← hins]
    exact Finset.insert_subset (Finset.mem_union_right A hpD) Finset.subset_union_left
  have hpB : p ∈ B := by
    have hp : p ∈ A ∪ B := by simpa [hAB] using hpL
    exact (Finset.mem_union.mp hp).resolve_left hpnotA
  have hpC : p ∈ C := by
    have hp : p ∈ C ∪ D := by simpa [hCD] using hpK
    exact (Finset.mem_union.mp hp).resolve_right hpnotD
  have hpos : 1 ≤ (B ∩ C).card := by
    exact Finset.card_pos.mpr ⟨p, Finset.mem_inter.mpr ⟨hpB, hpC⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · have hc := Finset.card_union_add_card_inter B C
    omega
  · intro hsub
    have hLB : L ⊆ B := by
      intro a haL
      rcases Finset.mem_union.mp (hsub haL) with haB | haC
      · exact haB
      · have hap : a = p := by
          have haI : a ∈ L ∩ K := Finset.mem_inter.mpr ⟨haL, hCsub haC⟩
          simpa [hinter] using haI
        simpa [hap] using hpB
    have hc := Finset.card_le_card hLB
    omega
  · intro hsub
    have hKC : K ⊆ C := by
      intro a haK
      rcases Finset.mem_union.mp (hsub haK) with haB | haC
      · have hap : a = p := by
          have haI : a ∈ L ∩ K := Finset.mem_inter.mpr ⟨hBsub haB, haK⟩
          simpa [hinter] using haI
        simpa [hap] using hpC
      · exact haC
    have hc := Finset.card_le_card hKC
    omega

end Meta921Audit
