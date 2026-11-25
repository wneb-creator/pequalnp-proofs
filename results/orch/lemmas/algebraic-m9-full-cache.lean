import AlgebraicM9One
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace PEqualNP.Outside.L_meta_6659_aux

theorem equality_m9_missing_card_cases {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h14 : totalSurplus 14 D ≤ 14)
    (hI : ineligSet 14 D = {0, 1, 2, 5, 11}) :
    (equality_missing_cap D).card = 1 ∨ (equality_missing_cap D).card = 2 := by
  classical
  have hel := inelig_card_add 14 D
  rw [hI, show ({0, 1, 2, 5, 11} : Finset (Fin 14)).card = 5 from rfl] at hel
  have hcap : ∀ i ∈ ({0, 1, 2, 5} : Finset (Fin 14)), i ∈ ineligSet 14 D := by rw [hI]; decide
  have hstar := mx_star h hD hcap
  have hLl : mx_L ⊆ sem_hw_opp 0 := by decide
  have hPe : mx_L ⊆ eligSet 14 D := by
    intro a ha
    by_contra hne
    have h1 := sem_mem_inelig.2 hne
    rw [hI] at h1
    exact mx_el a ha h1
  let Oc := ({0, 1, 2, 5} : Finset (Fin 14)).filter (fun i => sup_Occ 14 D mx_L (sem_hw_nb i))
  let Mc := ({0, 1, 2, 5} : Finset (Fin 14)).filter (fun i => ¬ sup_Occ 14 D mx_L (sem_hw_nb i))
  have hcnt := hw_count h hD mx_L hLl hPe Oc {3, 4, 6} {0, 1, 2, 5}
    (fun i hi => ⟨mx_cap i (Finset.mem_filter.1 hi).1, (Finset.mem_filter.1 hi).2⟩)
    (fun c hc => ⟨fun hc' => (mx_ctr c hc).1 (Finset.mem_filter.1 hc').1, Or.inl (mx_ctr c hc).2⟩)
    (fun i hi => ⟨hcap i hi, mx_cap i hi⟩)
  have hlost := hw_lost h hD mx_L
    (fun a ha b hb => sem_hw_opp_indep 0 a (hLl ha) b (hLl hb)) Mc
    (fun i hi => ⟨hcap i (Finset.mem_filter.1 hi).1, mx_cap i (Finset.mem_filter.1 hi).1,
      (Finset.mem_filter.1 hi).2⟩)
  have hsplit : Oc.card + Mc.card = 4 :=
    Finset.card_filter_add_card_filter_not (s := ({0, 1, 2, 5} : Finset (Fin 14)))
      (fun i => sup_Occ 14 D mx_L (sem_hw_nb i))
  rw [mx_lab, show ({0, 1, 2, 5} : Finset (Fin 14)).card = 4 from rfl,
    show mx_L.card = 6 from rfl] at hcnt
  have htotal := totalSurplus_split 14 D
  change Mc.card = 1 ∨ Mc.card = 2
  omega

theorem equality_m9_any_one_missing_impossible {D : Dag}
    (h : StrictLive 14 D) (hD : Correct D) (h14 : totalSurplus 14 D ≤ 14)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (one : (equality_missing_cap D).card = 1) : False := by
  classical
  obtain ⟨q,hM⟩ := Finset.card_eq_one.1 one
  have cap : q ∈ ({0,1,2,5} : Finset (Fin 14)) := by
    have member : q ∈ equality_missing_cap D := by rw [hM]; simp
    exact (Finset.mem_filter.1 member).1
  have geometry : ∀ q ∈ ({0,1,2,5} : Finset (Fin 14)), ∃ k l : Fin 6,
      equality_m9_automorphism l (equality_m9_automorphism k q) = 5 := by decide +kernel
  obtain ⟨k,l,equal⟩ := geometry q cap
  obtain ⟨h',hD',_,total',_,_,_,ineligible'⟩ :=
    heawood_relabel (equality_m9_automorphism k) (equality_m9_automorphism_aut k) h hD
  have hI' : ineligSet 14 (relabel (equality_m9_automorphism k) D) = {0,1,2,5,11} := by
    rw [ineligible',hI]
    exact (equality_m9_automorphism_geometry k).2.1
  have hM' : equality_missing_cap (relabel (equality_m9_automorphism k) D) =
      {equality_m9_automorphism k q} := by
    rw [equality_m9_missing_relabel h.1 k,hM,Finset.image_singleton]
  obtain ⟨h'',hD'',_,total'',_,_,_,ineligible''⟩ :=
    heawood_relabel (equality_m9_automorphism l) (equality_m9_automorphism_aut l) h' hD'
  apply equality_m9_one_missing_five_impossible h'' hD''
    (by rw [total'',total']; exact h14)
  · rw [ineligible'',hI']
    exact (equality_m9_automorphism_geometry l).2.1
  · rw [equality_m9_missing_relabel h'.1 l,hM',Finset.image_singleton,equal]

theorem equality_p9_mixed_impossible {D : Dag}
    (h : StrictLive 14 D) (hD : Correct D) (h14 : totalSurplus 14 D ≤ 14)
    (hI : ineligSet 14 D = {0,1,2,5,11}) : False := by
  rcases equality_m9_missing_card_cases h hD h14 hI with one | two
  · exact equality_m9_any_one_missing_impossible h hD h14 hI one
  · exact equality_m9_any_two_missing_impossible h hD h14 hI two

end PEqualNP.Outside.L_meta_6659_aux
