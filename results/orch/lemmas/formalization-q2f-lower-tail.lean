namespace PEqualNP.Outside.L_meta_6659_aux

theorem q2f_line_mask_cost {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hI : ineligSet 14 D = {0,1,2,3})
    (hM : equality_missing_points D = {2,4,5,6})
    (Y : Finset (Finset (Fin 14)))
    (good : ∀ M ∈ Y, sup_Occ 14 D (sem_hw_opp 0) M ∧ 2 ≤ M.card ∧
      (M.card = 2 → ∃ i ∈ ({0,1,3} : Finset (Fin 14)), M ⊆ sem_hw_nb i)) :
    Y.card + 6 ≤ Bplus 14 D := by
  classical
  let P := sem_hw_opp 0
  let Oc := ({0,1,3} : Finset (Fin 14))
  let Ct := (({2,4,5,6} : Finset (Fin 7)).image os_pt)
  have eligible : P ⊆ eligSet 14 D := by
    intro x hx
    by_contra hn
    have hi := sem_mem_inelig.2 hn
    rw [hI] at hi
    exact Finset.disjoint_left.1
      (by decide : Disjoint P ({0,1,2,3} : Finset (Fin 14))) hx hi
  have disjoint : Disjoint Oc Ct := by decide
  have occurs : ∀ i ∈ Oc, sem_hw_nb i ⊆ P ∧ sup_Occ 14 D P (sem_hw_nb i) := by
    intro i hi
    have geo : ∀ i ∈ ({0,1,3} : Finset (Fin 14)), ∃ q : Fin 7,
        os_pt q = i ∧ q ∉ ({2,4,5,6} : Finset (Fin 7)) := by decide +kernel
    obtain ⟨q,rfl,hq⟩ := geo i hi
    refine ⟨os_nb_sub q,?_⟩
    by_contra absent
    have hm : q ∈ equality_missing_points D := Finset.mem_filter.2 ⟨Finset.mem_univ _,absent⟩
    exact hq (hM ▸ hm)
  have centers : ∀ c ∈ Ct, c ∉ Oc ∧ ((sem_hw_nb c ∩ P).card ≤ 2 ∨
      (sem_hw_nb c ⊆ P ∧ ¬ sup_Occ 14 D P (sem_hw_nb c))) := by
    intro c hc
    refine ⟨fun ho => Finset.disjoint_left.1 disjoint ho hc,Or.inr ?_⟩
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.1 hc
    refine ⟨os_nb_sub q,?_⟩
    have hm : q ∈ equality_missing_points D := by rw [hM]; exact hq
    exact (Finset.mem_filter.1 hm).2
  have ineligible : ∀ i ∈ ({0,1,2,3} : Finset (Fin 14)),
      i ∈ ineligSet 14 D ∧ sem_hw_nb i ⊆ P := by
    intro i hi
    refine ⟨by rw [hI]; exact hi,?_⟩
    exact (by decide +kernel : ∀ i ∈ ({0,1,2,3} : Finset (Fin 14)),
      sem_hw_nb i ⊆ sem_hw_opp 0) i hi
  have bound := equality_hw_mask_family h hD P (Finset.Subset.refl _) eligible Oc Ct
    {0,1,2,3} occurs centers ineligible Y
    (fun M hMY => ⟨(good M hMY).2.1,(good M hMY).1⟩)
    (fun M hMY h2 => (good M hMY).2.2 h2)
  have pc : P.card = 7 := by decide
  have ic : ({0,1,2,3} : Finset (Fin 14)).card = 4 := rfl
  have union : (Ct.biUnion (fun c => sem_hw_nb c ∩ P)).card = 6 := by decide
  have ec := inelig_card_add 14 D
  rw [hI,ic] at ec
  rw [pc,ic,union] at bound
  omega


lemma q2f_circuit_Bplus_lower {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hI : ineligSet 14 D = {0,1,2,3})
    (hM : equality_missing_points D = {2,4,5,6})
    (certificate : ∀ s a b c, q2f_certificate s a b c = true) :
    13 ≤ Bplus 14 D := by
  classical
  obtain ⟨S,strict,s,a,b,c,eq,good⟩ := q2f_circuit_family h hD hI hM
  let Y := (q2f_codes s a b c).image (fun m => (cap7_decode m).image q2f_line_embed)
  have cost := q2f_line_mask_cost h hD hI hM Y (q2f_image_good _ good)
  have count : Y.card = (q2f_codes s a b c).card :=
    Finset.card_image_of_injective _
      ((Finset.image_injective q2f_line_geometry.1).comp cap7_decode_injective)
  have large := q2f_certificate_card s a b c (certificate s a b c)
  rw [count] at cost
  omega

end PEqualNP.Outside.L_meta_6659_aux
