import Mathlib

namespace PEqualNP.Outside.L_meta_650

def lineDifferences : Finset (Fin 13) := {0, 1, 3, 9}

def compatibleLines (S : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter fun l => ∀ p ∈ S, p + l ∉ lineDifferences

def incidentLines (p : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter fun l => p + l ∈ lineDifferences

lemma incidentLines_card : ∀ p : Fin 13, (incidentLines p).card = 4 := by
  decide +kernel

lemma incidentLines_inter_card : ∀ p q : Fin 13, p ≠ q →
    (incidentLines p ∩ incidentLines q).card = 1 := by
  decide +kernel

lemma independent_rectangle_small (P L : Finset (Fin 13))
    (h : ∀ p ∈ P, ∀ l ∈ L, p + l ∉ lineDifferences) :
    P.card ≤ 3 ∨ L.card ≤ 3 := by
  by_cases hp : P.card ≤ 3
  · exact Or.inl hp
  · right
    obtain ⟨a, b, c, d, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd⟩ :=
      Finset.three_lt_card_iff.mp (show 3 < P.card by omega)
    let A := incidentLines a
    let B := incidentLines b
    let C := incidentLines c
    let D := incidentLines d
    have ca : A.card = 4 := incidentLines_card a
    have cb : B.card = 4 := incidentLines_card b
    have cc : C.card = 4 := incidentLines_card c
    have cd : D.card = 4 := incidentLines_card d
    have cab : (A ∩ B).card = 1 := incidentLines_inter_card a b hab
    have cac : (A ∩ C).card = 1 := incidentLines_inter_card a c hac
    have cad : (A ∩ D).card = 1 := incidentLines_inter_card a d had
    have cbc : (B ∩ C).card = 1 := incidentLines_inter_card b c hbc
    have cbd : (B ∩ D).card = 1 := incidentLines_inter_card b d hbd
    have ccd : (C ∩ D).card = 1 := incidentLines_inter_card c d hcd
    have cAB : (A ∪ B).card = 7 := by
      have := Finset.card_union_add_card_inter A B
      omega
    have cABCinter : ((A ∪ B) ∩ C).card ≤ 2 := by
      rw [Finset.union_inter_distrib_right]
      have := Finset.card_union_le (A ∩ C) (B ∩ C)
      omega
    have cABC : 9 ≤ ((A ∪ B) ∪ C).card := by
      have := Finset.card_union_add_card_inter (A ∪ B) C
      omega
    have cABCDinter : (((A ∪ B) ∪ C) ∩ D).card ≤ 3 := by
      rw [Finset.union_inter_distrib_right, Finset.union_inter_distrib_right]
      have := Finset.card_union_le (A ∩ D) (B ∩ D)
      have := Finset.card_union_le ((A ∩ D) ∪ (B ∩ D)) (C ∩ D)
      omega
    let U := ((A ∪ B) ∪ C) ∪ D
    have cU : 10 ≤ U.card := by
      have := Finset.card_union_add_card_inter ((A ∪ B) ∪ C) D
      change 10 ≤ (((A ∪ B) ∪ C) ∪ D).card
      omega
    have disj : Disjoint U L := by
      apply Finset.disjoint_left.mpr
      intro l hl hL
      have cases : l ∈ A ∨ l ∈ B ∨ l ∈ C ∨ l ∈ D := by
        simpa only [U, Finset.mem_union, or_assoc] using hl
      rcases cases with hl | hl | hl | hl
      · exact h a ha l hL (Finset.mem_filter.mp hl).2
      · exact h b hb l hL (Finset.mem_filter.mp hl).2
      · exact h c hc l hL (Finset.mem_filter.mp hl).2
      · exact h d hd l hL (Finset.mem_filter.mp hl).2
    have upper : (U ∪ L).card ≤ 13 := by
      simpa using Finset.card_le_card (Finset.subset_univ (U ∪ L))
    have unionCard := Finset.card_union_of_disjoint disj
    omega

end PEqualNP.Outside.L_meta_650
