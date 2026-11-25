import PetersenGeometry

namespace PEqualNP.Outside.L_meta_1884.SixOrbit

open PEqualNP.Outside.L_meta_2590_aux.Surplus

def triI : Finset (Fin 10) := {1, 3, 5}
def triT : Finset (Fin 10) := {0, 2, 8}
def triA (f : Fin 10) : Finset (Fin 10) :=
  if f = 0 then {2, 4, 8} else if f = 2 then {0, 7, 8} else {0, 2, 6}

theorem triple_orbit_impossible {D : Dag} (h : StrictLive 10 D) (hD : Correct D)
    (hsize : D.length ≤ 18) (hI : ineligSet 10 D = triI) : False := by
  classical
  have hG := sem_petersen_gr
  obtain ⟨b, hb⟩ := sem_exists_pureBranch hG h.1 hD
  obtain ⟨pos, hpos⟩ := k4_assigned hG h hD
  have hi1 : (1 : Fin 10) ∈ ineligSet 10 D := by rw [hI]; decide
  have hi3 : (3 : Fin 10) ∈ ineligSet 10 D := by rw [hI]; decide
  have hp : (eligSet 10 D).card = 7 := by
    have he := Finset.card_le_univ (eligSet 10 D)
    have hc : (ineligSet 10 D).card + (eligSet 10 D).card = 10 := by
      rw [ineligSet, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        Fintype.card_fin]
      simp only [Fintype.card_fin] at he
      omega
    rw [hI, show triI.card = 3 by decide] at hc
    omega
  have hJ : ∀ i ∈ triI, i ∈ ineligSet 10 D ∧ (∃ a ∈ triT, Adj i a) ∧
      ∀ f ∈ triT, ∃ a ∈ triA f, Adj i a := by
    intro i hi
    refine ⟨by rw [hI]; exact hi, ?_⟩
    have hc : ∀ i ∈ triI, (∃ a ∈ triT, Adj i a) ∧
        ∀ f ∈ triT, ∃ a ∈ triA f, Adj i a := by decide +kernel
    exact hc i hi
  have hA : ∀ f ∈ triT, (∀ a ∈ triA f, ∀ c ∈ triA f, ¬ Adj a c) ∧
      triT.erase f ⊆ triA f ∧ ∃ a ∈ triA f, Adj f a := by decide +kernel
  have hbound := tri_bound hG h hD b hb hpos triT triI triA hJ hA
    (x := (2 : Fin 10)) (y := (0 : Fin 10)) (z := (8 : Fin 10))
    (by decide : triT = {2, 0, 8}) (by decide) (by decide) (by decide)
    ((hpos.1 1 hi1).2.2.1 2 (by decide)) ((hpos.1 1 hi1).2.2.1 0 (by decide))
    ((hpos.1 3 hi3).2.2.1 2 (by decide)) ((hpos.1 3 hi3).2.2.1 8 (by decide))
  have hs := surplus_identity h
  have hsplit := totalSurplus_split 10 D
  rw [hp, show triI.card = 3 by decide] at hbound
  have hzero : Bzero 10 D = 0 := by omega
  have hB : Bplus 10 D ≤ 9 := by omega
  have hTind : ∀ a ∈ triT, ∀ c ∈ triT, ¬ Adj a c := by decide +kernel
  have hocc : ∀ i ∈ triI, sup_Occ 10 D triT (triT.filter (Adj i)) := by
    intro i hi
    have hii : i ∈ ineligSet 10 D := by rw [hI]; exact hi
    have chain := sem_noempty_chain_out hG h hD hzero hii
    obtain ⟨j, s, hj, ht, hc, he⟩ := sem_exact_nbhd hG h.1 hD triT hTind chain
    refine ⟨src D (j, s), ?_⟩
    ext a
    simp only [Finset.mem_inter, Finset.mem_filter]
    constructor
    · intro ha
      exact ⟨ha.2, (he a ha.2).mp ha.1⟩
    · intro ha
      exact ⟨(he a ha.1).mpr ha.2, ha.1⟩
  let F : Finset (Finset (Fin 10)) := {{0, 2}, {2, 8}, {0, 8}}
  have hF : ∀ M ∈ F, 2 ≤ M.card ∧ sup_Occ 10 D triT M := by
    intro M hM
    simp only [F, Finset.mem_insert, Finset.mem_singleton] at hM
    rcases hM with rfl | rfl | rfl
    · refine ⟨by decide, ?_⟩
      convert hocc 1 (by decide) using 1 <;> decide
    · refine ⟨by decide, ?_⟩
      convert hocc 3 (by decide) using 1 <;> decide
    · refine ⟨by decide, ?_⟩
      convert hocc 5 (by decide) using 1 <;> decide
  have hc := tri_occ hG h hD b hb hpos triT triI triA hJ hA F hF
  rw [hp, show triI.card = 3 by decide, show triT.card = 3 by decide,
    show F.card = 3 by decide] at hc
  omega

end PEqualNP.Outside.L_meta_1884.SixOrbit
