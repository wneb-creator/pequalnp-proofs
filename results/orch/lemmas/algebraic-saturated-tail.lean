noncomputable def equality_missing_points (D : Dag) : Finset (Fin 7) := by
  classical
  exact Finset.univ.filter
    (fun k => ¬ sup_Occ 14 D (sem_hw_opp 0) (sem_hw_nb (os_pt k)))

noncomputable def equality_missing_cap (D : Dag) : Finset (Fin 14) := by
  classical
  exact ({0, 1, 2, 5} : Finset (Fin 14)).filter
    (fun i => ¬ sup_Occ 14 D mx_L (sem_hw_nb i))

theorem equality_five_point_star {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hI : ineligSet 14 D = {0, 1, 2, 3, 4}) :
    (eligSet 14 D).card + 3 ≤ Bplus 14 D := by
  let σ := collPerm⁻¹ * collPerm⁻¹
  have hσ : IsAut σ := isAut_mul (isAut_inv collPerm_isAut) (isAut_inv collPerm_isAut)
  obtain ⟨h1,h2,_,_,h5,_,h7,h8⟩ := heawood_relabel σ hσ h hD
  have hcap : ∀ i ∈ ({0, 1, 2, 5} : Finset (Fin 14)),
      i ∈ ineligSet 14 (relabel σ D) := by
    rw [h8,hI]
    change ∀ i ∈ ({0, 1, 2, 5} : Finset (Fin 14)),
      i ∈ ({0, 1, 2, 3, 4} : Finset (Fin 14)).image (collPerm⁻¹ * collPerm⁻¹)
    decide +kernel
  have lower := mx_star h1 h2 hcap
  rw [h5,h7,Finset.card_image_of_injective _ σ.injective] at lower
  exact lower

theorem equality_cap_union : ∀ Q ∈ ([{0, 1, 2, 3, 4}, {0, 1, 2, 5}] :
    List (Finset (Fin 7))), ∀ M : Finset (Fin 7),
    (M ∩ Q).card + 3 ≤ Q.card →
      2 * M.card ≤ ((M.image os_pt).biUnion
        (fun c => sem_hw_nb c ∩ sem_hw_opp 0)).card + (M ∩ Q).card := by
  decide +kernel

theorem equality_onesided_saturated {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h14 : totalSurplus 14 D ≤ 14) (Q : Finset (Fin 7))
    (hI : ineligSet 14 D = Q.image os_pt)
    (hQ : Q ∈ ([{0, 1, 2, 3, 4}, {0, 1, 2, 5}] : List (Finset (Fin 7))))
    (hstar : (eligSet 14 D).card + 3 ≤ Bplus 14 D) :
    (equality_missing_points D ∩ Q).card = Bzero 14 D := by
  classical
  have hQi : ∀ k ∈ Q, os_pt k ∈ ineligSet 14 D := fun k hk => by
    rw [hI]; exact Finset.mem_image_of_mem _ hk
  have hPe : sem_hw_opp 0 ⊆ eligSet 14 D := by
    intro a ha
    by_contra hne
    have h1 := sem_mem_inelig.2 hne
    rw [hI] at h1
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 h1
    exact (by decide : ∀ k : Fin 7, os_pt k ∉ sem_hw_opp 0) k ha
  let Oc := Finset.univ.filter
    (fun k : Fin 7 => sup_Occ 14 D (sem_hw_opp 0) (sem_hw_nb (os_pt k)))
  let Mi := Finset.univ.filter
    (fun k : Fin 7 => ¬ sup_Occ 14 D (sem_hw_opp 0) (sem_hw_nb (os_pt k)))
  have hcnt := hw_count h hD (sem_hw_opp 0) (Finset.Subset.refl _) hPe (Oc.image os_pt)
    (Mi.image os_pt) (Q.image os_pt)
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      exact ⟨os_nb_sub k, (Finset.mem_filter.1 hk).2⟩)
    (fun c hc => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hc
      refine ⟨fun hc' => ?_, Or.inr ⟨os_nb_sub k, (Finset.mem_filter.1 hk).2⟩⟩
      obtain ⟨k', hk', hkk⟩ := Finset.mem_image.1 hc'
      rw [os_pt_inj hkk] at hk'
      exact (Finset.mem_filter.1 hk).2 (Finset.mem_filter.1 hk').2)
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      exact ⟨hQi k hk, os_nb_sub k⟩)
  have hlost := hw_lost h hD (sem_hw_opp 0) (sem_hw_opp_indep 0) ((Mi ∩ Q).image os_pt)
    (fun i hi => by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      rw [Finset.mem_inter] at hk
      exact ⟨hQi k hk.2, os_nb_sub k, (Finset.mem_filter.1 hk.1).2⟩)
  rw [Finset.card_image_of_injective _ os_pt_inj] at hlost
  rw [Finset.card_image_of_injective _ os_pt_inj,
    Finset.card_image_of_injective _ os_pt_inj] at hcnt
  have hsplit : Oc.card + Mi.card = 7 := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 7)))
      (fun k : Fin 7 => sup_Occ 14 D (sem_hw_opp 0) (sem_hw_nb (os_pt k)))
    simpa using this
  have hP7 : (sem_hw_opp 0).card = 7 := by decide
  have hel := inelig_card_add 14 D
  rw [hI,Finset.card_image_of_injective _ os_pt_inj] at hel
  have htotal := totalSurplus_split 14 D
  have hgeo := equality_cap_union Q hQ Mi (by omega)
  change (Mi ∩ Q).card = Bzero 14 D
  omega

theorem equality_onesided_occ_chain {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h14 : totalSurplus 14 D ≤ 14) (Q : Finset (Fin 7))
    (hI : ineligSet 14 D = Q.image os_pt)
    (hQ : Q ∈ ([{0, 1, 2, 3, 4}, {0, 1, 2, 5}] : List (Finset (Fin 7))))
    (hstar : (eligSet 14 D).card + 3 ≤ Bplus 14 D)
    {k : Fin 7} (hk : k ∈ Q)
    (hmask : sup_Occ 14 D (sem_hw_opp 0) (sem_hw_nb (os_pt k))) :
    sem_Chain 14 D (os_pt k).val (outW 14 D) := by
  classical
  let Mi := Finset.univ.filter
    (fun k : Fin 7 => ¬ sup_Occ 14 D (sem_hw_opp 0) (sem_hw_nb (os_pt k)))
  let J := (Mi ∩ Q).image os_pt
  have hin : ∀ t ∈ Q, os_pt t ∈ ineligSet 14 D := fun t ht => by
    rw [hI]; exact Finset.mem_image_of_mem _ ht
  apply equality_lost_saturates_chain h hD (sem_hw_opp 0) (sem_hw_opp_indep 0) J
  · intro i hi
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.1 hi
    exact ⟨hin t (Finset.mem_inter.1 ht).2,os_nb_sub t,
      (Finset.mem_filter.1 (Finset.mem_inter.1 ht).1).2⟩
  · rw [Finset.card_image_of_injective _ os_pt_inj]
    exact equality_onesided_saturated h hD h14 Q hI hQ hstar
  · exact hin k hk
  · intro hm
    obtain ⟨t,ht,equal⟩ := Finset.mem_image.1 hm
    have same := os_pt_inj equal
    subst t
    exact (Finset.mem_filter.1 (Finset.mem_inter.1 ht).1).2 hmask
  · exact os_nb_sub k

theorem equality_mixed_cap_saturated {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h14 : totalSurplus 14 D ≤ 14)
    (hI : ineligSet 14 D = {0, 1, 2, 5, 11}) :
    (equality_missing_cap D).card = Bzero 14 D := by
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
  change Mc.card = Bzero 14 D
  omega

theorem equality_mixed_cap_occ_chain {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h14 : totalSurplus 14 D ≤ 14)
    (hI : ineligSet 14 D = {0, 1, 2, 5, 11}) {v : Fin 14}
    (hv : v ∈ ({0, 1, 2, 5} : Finset (Fin 14)))
    (hmask : sup_Occ 14 D mx_L (sem_hw_nb v)) :
    sem_Chain 14 D v.val (outW 14 D) := by
  classical
  let J := ({0, 1, 2, 5} : Finset (Fin 14)).filter
    (fun i => ¬ sup_Occ 14 D mx_L (sem_hw_nb i))
  have hLl : mx_L ⊆ sem_hw_opp 0 := by decide
  have hin : ∀ i ∈ ({0, 1, 2, 5} : Finset (Fin 14)), i ∈ ineligSet 14 D := by rw [hI]; decide
  apply equality_lost_saturates_chain h hD mx_L
    (fun a ha b hb => sem_hw_opp_indep 0 a (hLl ha) b (hLl hb)) J
  · intro i hi
    exact ⟨hin i (Finset.mem_filter.1 hi).1,mx_cap i (Finset.mem_filter.1 hi).1,
      (Finset.mem_filter.1 hi).2⟩
  · exact equality_mixed_cap_saturated h hD h14 hI
  · exact hin v hv
  · intro hi
    exact (Finset.mem_filter.1 hi).2 hmask
  · exact mx_cap v hv
