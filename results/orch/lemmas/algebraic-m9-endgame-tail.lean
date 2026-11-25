theorem equality_m9_two_missing_impossible_of_certificate
    (certificate : ∀ (r : Fin 6 → Fin 8) (a b : Fin 3) (T : Fin 8),
      (r 0 = 1 ∨ r 0 = 3) → m9_normal r a b = true → m9_pointAllowed r a b T = false)
    {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (h14 : totalSurplus 14 D ≤ 14)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (hM : equality_missing_cap D = {2,5}) : False := by
  classical
  have missing2 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 2) := by
    have member : (2 : Fin 14) ∈ equality_missing_cap D := by rw [hM]; decide
    exact (Finset.mem_filter.1 member).2
  have missing5 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 5) := by
    have member : (5 : Fin 14) ∈ equality_missing_cap D := by rw [hM]; decide
    exact (Finset.mem_filter.1 member).2
  have protects : ∀ i ∈ ({0,1} : Finset (Fin 14)), ∀ w,
      Relation.ReflTransGen (sem_step 14 D) i.val w → fanout D w ≤ 1 := by
    intro i hi
    apply equality_chain_protected h.1
    apply equality_mixed_cap_occ_chain h hD h14 hI
      ((by decide : ({0,1} : Finset (Fin 14)) ⊆ {0,1,2,5}) hi)
    by_contra missing
    have member : i ∈ equality_missing_cap D := Finset.mem_filter.2
      ⟨((by decide : ({0,1} : Finset (Fin 14)) ⊆ {0,1,2,5}) hi),missing⟩
    rw [hM] at member
    exact Finset.disjoint_left.1 (by decide : Disjoint ({0,1} : Finset (Fin 14)) {2,5}) hi member
  obtain ⟨b,first⟩ := sem_exists_firstBranch sem_heawood_gr h.1 (sem_heawood_comp hD)
  have hb := sem_firstBranch_pure first
  have total := totalSurplus_split 14 D
  have zero := equality_mixed_cap_saturated h hD h14 hI
  rw [hM,show ({2,5} : Finset (Fin 14)).card = 2 from rfl] at zero
  have eligible := inelig_card_add 14 D
  rw [hI,show ({0,1,2,5,11} : Finset (Fin 14)).card = 5 from rfl] at eligible
  have lower := mx_star h hD (by rw [hI]; decide)
  have residual := card_residual h.1 b hb
  have three : (residualUnits 14 D b).card = 3 := by omega
  obtain ⟨a,injective,onto,normalized⟩ := equality_m9_normal_coordinates h hD h14 b hb hI three
  have zeros := equality_m9_zero_points_of_certificate certificate h hD h14 b hb hI missing2 missing5
    protects a injective onto normalized
  have upper := equality_m9_cofactor_supported_upper h hD h14 b first hI zeros missing2 missing5
  have lower := equality_cf_supported_eight h hD cf3_good
    (by change ∀ w, Relation.ReflTransGen (sem_step 14 D) 0 w → fanout D w ≤ 1
        exact protects 0 (by decide))
    (by change ∀ w, Relation.ReflTransGen (sem_step 14 D) 1 w → fanout D w ≤ 1
        exact protects 1 (by decide))
  omega
