theorem equality_missing_empty_branch {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (P : Finset (Fin 14)) (hP : ∀ a ∈ P, ∀ b ∈ P, ¬ Adj a b) {i : Fin 14}
    (hi : i ∈ ineligSet 14 D) (hNi : sem_hw_nb i ⊆ P)
    (missing : ¬ sup_Occ 14 D P (sem_hw_nb i)) :
    ∃ w, sem_Chain 14 D i.val w ∧ 2 ≤ fanout D w ∧ supp 14 D w = ∅ := by
  rcases sem_inelig_reach sem_heawood_gr h (sem_heawood_comp hD) hi with chain | branch
  · obtain ⟨j,s,_,_,_,hq⟩ := sem_exact_nbhd sem_heawood_gr h.1 (sem_heawood_comp hD) P hP chain
    apply False.elim
    apply missing
    refine ⟨src D (j,s),?_⟩
    ext x
    rw [Finset.mem_inter,hw_mem_nb]
    exact ⟨fun hx => (hq x hx.2).1 hx.1,
      fun hx => ⟨(hq x (hNi (hw_mem_nb.2 hx))).2 hx,hNi (hw_mem_nb.2 hx)⟩⟩
  · exact branch

theorem equality_m9_center_absent {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (pos : Fin 14 → ℕ × Bool) (hpos : k4_Pos 14 HG D pos)
    (hI : ineligSet 14 D = {0,1,2,5,11}) (zero : ru D b 3 = ∅)
    {i : Fin 14} (hi : i ∈ ({0,1,2,5} : Finset (Fin 14))) :
    (3 : Fin 14) ∉ supp 14 D (src D (pos i)) := by
  intro member
  have hi' : i ∈ ineligSet 14 D := by
    rw [hI]
    exact (by decide : ({0,1,2,5} : Finset (Fin 14)) ⊆ {0,1,2,5,11}) hi
  have h11 : (11 : Fin 14) ∈ ineligSet 14 D := by rw [hI]; decide
  have hel7 : (7 : Fin 14) ∈ eligSet 14 D := by
    by_contra hn
    have := hI ▸ sem_mem_inelig.2 hn
    exact (by decide : (7 : Fin 14) ∉ ({0,1,2,5,11} : Finset (Fin 14))) this
  have hj : ∀ j ∈ ({11,i} : Finset (Fin 14)),
      j ∈ ineligSet 14 D ∧ (3 : Fin 14) ∈ supp 14 D (src D (pos j)) := by
    intro j hj
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact ⟨h11,(hpos.1 11 h11).2.2.1 3 (by decide)⟩
    · have eq := Finset.mem_singleton.1 hj
      subst j
      exact ⟨hi',member⟩
  have bound := equality_assigned_budget_extra h hD b hb pos hpos {11,i} hj hel7 (by decide : Adj 3 7)
  have ne : (11 : Fin 14) ≠ i := by
    intro eq
    rw [← eq] at hi
    exact (by decide : (11 : Fin 14) ∉ ({0,1,2,5} : Finset (Fin 14))) hi
  rw [Finset.card_pair ne,zero,Finset.card_empty] at bound
  omega

theorem equality_m9_cofactor_supported_upper {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h14 : totalSurplus 14 D ≤ 14) (b : Fin 14 → ℕ) (first : sem_FirstBranch 14 D b)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (zeros : ∀ x ∈ ({3,4,6} : Finset (Fin 14)), ru D b x = ∅)
    (missing2 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 2))
    (missing5 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 5)) :
    cof_surP D (cf_rho 3) (cf_iota cfL3) ≤ 7 := by
  classical
  have hb := sem_firstBranch_pure first
  obtain ⟨pos,hpos⟩ := k4_assigned sem_heawood_gr h (sem_heawood_comp hD)
  have eligible : ∀ x ∈ ({3,4,6,7,12} : Finset (Fin 14)), x ∈ eligSet 14 D := by
    intro x hx
    by_contra hn
    exact Finset.disjoint_left.1
      (by decide : Disjoint ({3,4,6,7,12} : Finset (Fin 14)) {0,1,2,5,11}) hx
      (hI ▸ sem_mem_inelig.2 hn)
  have ineligible : ∀ x ∈ ({2,5,11} : Finset (Fin 14)), x ∈ ineligSet 14 D := by
    intro x hx
    rw [hI]
    exact (by decide : ({2,5,11} : Finset (Fin 14)) ⊆ {0,1,2,5,11}) hx
  have Pind : ∀ a ∈ mx_L, ∀ b ∈ mx_L, ¬ Adj a b := by decide +kernel
  have n2 : sem_hw_nb 2 ⊆ mx_L := by decide
  have n5 : sem_hw_nb 5 ⊆ mx_L := by decide
  obtain ⟨u,cu,bu,eu⟩ := equality_missing_empty_branch h hD mx_L Pind
    (ineligible 2 (by decide)) n2 missing2
  obtain ⟨v,cv,bv,ev⟩ := equality_missing_empty_branch h hD mx_L Pind
    (ineligible 5 (by decide)) n5 missing5
  have different : u ≠ v := equality_missing_branches_distinct h hD mx_L Pind
    (by decide : (2 : Fin 14) ≠ 5) n5 missing2 n2 cu cv
  have empty_transfer : ∀ i ∈ ({2,5} : Finset (Fin 14)), ∀ w,
      sem_Chain 14 D i.val w → 2 ≤ fanout D w → supp 14 D w = ∅ →
        cof_supp D (cf_rho 3) (cf_iota cfL3) w = ∅ := by
    intro i hi w chain branch empty
    have hii : i ∈ ineligSet 14 D := by
      rw [hI]
      exact (by decide : ({2,5} : Finset (Fin 14)) ⊆ {0,1,2,5,11}) hi
    have wi : sem_bar (pos i) ∈ sem_W 14 D i := by
      rw [as_W h hD hpos hii]
      exact Finset.mem_singleton_self _
    apply equality_cofactor_empty_branch_empty h.1 hD cf3_good hii
      ((by decide : ∀ i ∈ ({2,5} : Finset (Fin 14)), i ≠ 3) i hi) wi _ chain branch empty
    rw [sem_bar_bar]
    exact equality_m9_center_absent h hD b hb pos hpos hI (zeros 3 (by decide))
      ((by decide : ({2,5} : Finset (Fin 14)) ⊆ {0,1,2,5}) hi)
  have lost : ∀ x ∈ ({3,4,6,7,12} : Finset (Fin 14)),
      x ∈ eligSet 14 D ∧ (⟨b x,0⟩ : Σ _ : ℕ, ℕ) ∉ cof_keptP D (cf_rho 3) (cf_iota cfL3) := by
    intro x hx
    refine ⟨eligible x hx,?_⟩
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · intro hk
      have member : (3 : Fin 14) ∈ supp 14 D (b 3) := by
        rw [(hb 3 (eligible 3 (by decide))).2]
        exact Finset.mem_singleton_self _
      exact cof_lost_of_true h.1 (by simp [cf_rho]) member (cof_keptP_sub hk)
    · intro hk
      have depleted := equality_cofactor_reserved_depleted (l := cfL3) h hD b hb
        (eligible 4 (by decide)) (by decide : (4 : Fin 14) ≠ 3)
        (by
          intro q hq h4
          have mem := mem_ru.2 ⟨hq,h4⟩
          rw [zeros 4 (by decide)] at mem
          exact (Finset.notMem_empty _ mem).elim)
        ⟨src D (pos 11),(hpos.1 11 (ineligible 11 (by decide))).2.2.1 4 (by decide),
          (hpos.1 11 (ineligible 11 (by decide))).2.2.1 3 (by decide)⟩
      exact depleted (cof_keptP_sub hk)
    · intro hk
      have depleted := equality_cofactor_reserved_depleted (l := cfL3) h hD b hb
        (eligible 6 (by decide)) (by decide : (6 : Fin 14) ≠ 3)
        (by
          intro q hq h6
          have mem := mem_ru.2 ⟨hq,h6⟩
          rw [zeros 6 (by decide)] at mem
          exact (Finset.notMem_empty _ mem).elim)
        ⟨src D (pos 11),(hpos.1 11 (ineligible 11 (by decide))).2.2.1 6 (by decide),
          (hpos.1 11 (ineligible 11 (by decide))).2.2.1 3 (by decide)⟩
      exact depleted (cof_keptP_sub hk)
    · exact cof_lostP_of_supp (equality_cofactor_neighbor_branch_empty h hD cf3_good
        (by decide : Adj 3 7) (first 7 (eligible 7 (by decide))).2.2)
    · exact cof_lostP_of_supp (equality_cofactor_neighbor_branch_empty h hD cf3_good
        (by decide : Adj 3 12) (first 12 (eligible 12 (by decide))).2.2)
  have bound := equality_cofactor_supported_loss h.1 (cf_rho 3) (cf_iota cfL3) b hb
    {3,4,6,7,12} {u,v} lost (by
      intro w hw
      rcases Finset.mem_insert.1 hw with eq | hw
      · subst w
        exact ⟨bu,eu,empty_transfer 2 (by decide) u cu bu eu⟩
      · have eq := Finset.mem_singleton.1 hw
        subst w
        exact ⟨bv,ev,empty_transfer 5 (by decide) v cv bv ev⟩)
  rw [show ({3,4,6,7,12} : Finset (Fin 14)).card = 5 from rfl,
    Finset.card_pair different] at bound
  omega

