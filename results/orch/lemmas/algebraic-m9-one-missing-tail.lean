def equality_m9_full_line (i : Fin 7) : Fin 14 := Fin.natAdd 7 i

theorem equality_m9_one_missing_family {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hI : ineligSet 14 D = {0,1,2,5,11}) (hM : equality_missing_cap D = {5}) :
    ∃ Y : Finset (Finset (Fin 14)), 7 ≤ Y.card ∧
      ∀ M ∈ Y, 2 ≤ M.card ∧ sup_Occ 14 D mx_L M ∧
        (M.card = 2 → ∃ i ∈ ({0,1,2} : Finset (Fin 14)), M ⊆ sem_hw_nb i) := by
  classical
  let f := equality_m9_full_line
  let Q := fun M : Finset (Fin 7) => sup_Occ 14 D mx_L (M.image f)
  have inj : Function.Injective f := by
    intro i j equal
    apply Fin.ext
    have eq := congrArg (Fin.val : Fin 14 → ℕ) equal
    change 7+i.val = 7+j.val at eq
    omega
  have range : Finset.univ.image f = sem_hw_opp 0 := by decide +kernel
  have subrange : mx_L ⊆ sem_hw_opp 0 := by decide
  have geometry : (∀ i : Fin 3, (cap7_triple i).image f = sem_hw_nb (![0,1,2] i)) ∧
      cap7_missing.image f = sem_hw_nb 5 := by decide +kernel
  have occurs (i : Fin 14) (hi : i ∈ ({0,1,2} : Finset (Fin 14))) :
      sup_Occ 14 D mx_L (sem_hw_nb i) := by
    by_contra absent
    have member : i ∈ equality_missing_cap D := Finset.mem_filter.2
      ⟨(by decide : ({0,1,2} : Finset (Fin 14)) ⊆ {0,1,2,5}) hi,absent⟩
    rw [hM] at member
    exact Finset.disjoint_left.1 (by decide : Disjoint ({0,1,2} : Finset (Fin 14)) {5}) hi member
  have base (i : Fin 3) : Q (cap7_triple i) := by
    change sup_Occ 14 D mx_L ((cap7_triple i).image f)
    rw [geometry.1 i]
    exact occurs _ ((by decide : ∀ i : Fin 3, (![0,1,2] i : Fin 14) ∈ ({0,1,2} : Finset (Fin 14))) i)
  have parents (i : Fin 3) : cap7_Parent Q (cap7_triple i) := by
    change equality_mask_parent Q (cap7_triple i)
    exact equality_occurring_parent_pull_subset h.1 f inj mx_L (sem_hw_opp 0)
      subrange range (cap7_triple i) (cap7_triple_card i) (base i)
  obtain ⟨pos,hpos⟩ := k4_assigned sem_heawood_gr h (sem_heawood_comp hD)
  have ineligible : (5 : Fin 14) ∈ ineligSet 14 D := by rw [hI]; decide
  let A := supp 14 D (src D (pos 5)) ∩ mx_L
  have hA : sup_Occ 14 D mx_L A := ⟨src D (pos 5),rfl⟩
  have subA : A ⊆ sem_hw_opp 0 := fun x hx => subrange (Finset.mem_inter.1 hx).2
  let S := equality_mask_pull f A
  have back : S.image f = A := equality_mask_pull_image f (sem_hw_opp 0) range subA
  have neighbors : sem_hw_nb 5 ⊆ A := by
    intro x hx
    exact Finset.mem_inter.2 ⟨(hpos.1 _ ineligible).2.2.1 x (hw_mem_nb.1 hx),mx_cap 5 (by decide) hx⟩
  have absent : ¬ sup_Occ 14 D mx_L (sem_hw_nb 5) := by
    have member : (5 : Fin 14) ∈ equality_missing_cap D := by rw [hM]; decide
    exact (Finset.mem_filter.1 member).2
  have strict : cap7_missing ⊂ S := by
    apply Finset.ssubset_iff_subset_ne.2
    constructor
    · apply (Finset.image_subset_image_iff inj).1
      rw [geometry.2,back]
      exact neighbors
    · intro equal
      apply absent
      rw [← geometry.2,equal,back]
      exact hA
  have hS : Q S := by change sup_Occ 14 D mx_L (S.image f); rwa [back]
  obtain ⟨Y,large,good⟩ := cap7_seven_occurring Q base parents S strict hS
  refine ⟨Y.image (fun M => M.image f),?_,?_⟩
  · rw [Finset.card_image_of_injective _ (Finset.image_injective inj)]
    exact large
  · intro M hMY
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.1 hMY
    refine ⟨?_,(good T hT).1,?_⟩
    · rw [Finset.card_image_of_injective _ inj]
      exact (good T hT).2.1
    · intro pair
      rw [Finset.card_image_of_injective _ inj] at pair
      obtain ⟨i,sub⟩ := (good T hT).2.2 pair
      refine ⟨![0,1,2] i,?_,?_⟩
      · exact (by decide : ∀ i : Fin 3, (![0,1,2] i : Fin 14) ∈ ({0,1,2} : Finset (Fin 14))) i
      · have imageSub := Finset.image_subset_image sub (f := f)
        rwa [geometry.1 i] at imageSub

theorem equality_m9_one_missing_five_impossible {D : Dag}
    (h : StrictLive 14 D) (hD : Correct D) (h14 : totalSurplus 14 D ≤ 14)
    (hI : ineligSet 14 D = {0,1,2,5,11}) (hM : equality_missing_cap D = {5}) : False := by
  classical
  obtain ⟨Y,large,good⟩ := equality_m9_one_missing_family h hD hI hM
  have eligible : mx_L ⊆ eligSet 14 D := by
    intro x hx
    by_contra no
    exact mx_el x hx (hI ▸ sem_mem_inelig.2 no)
  have occurs : ∀ i ∈ ({0,1,2} : Finset (Fin 14)),
      sem_hw_nb i ⊆ mx_L ∧ sup_Occ 14 D mx_L (sem_hw_nb i) := by
    intro i hi
    have cap : i ∈ ({0,1,2,5} : Finset (Fin 14)) := (by decide : ({0,1,2} : Finset (Fin 14)) ⊆ {0,1,2,5}) hi
    refine ⟨mx_cap i cap,?_⟩
    by_contra absent
    have member : i ∈ equality_missing_cap D := Finset.mem_filter.2 ⟨cap,absent⟩
    rw [hM] at member
    exact Finset.disjoint_left.1 (by decide : Disjoint ({0,1,2} : Finset (Fin 14)) {5}) hi member
  have centers : ∀ c ∈ ({3,4,6} : Finset (Fin 14)), c ∉ ({0,1,2} : Finset (Fin 14)) ∧
      ((sem_hw_nb c ∩ mx_L).card ≤ 2 ∨
        (sem_hw_nb c ⊆ mx_L ∧ ¬ sup_Occ 14 D mx_L (sem_hw_nb c))) := by
    intro c hc
    exact ⟨fun hi => (mx_ctr c hc).1 ((by decide : ({0,1,2} : Finset (Fin 14)) ⊆ {0,1,2,5}) hi),
      Or.inl (mx_ctr c hc).2⟩
  have ineligible : ∀ i ∈ ({0,1,2,5} : Finset (Fin 14)),
      i ∈ ineligSet 14 D ∧ sem_hw_nb i ⊆ mx_L := by
    intro i hi
    exact ⟨by rw [hI]; exact (by decide : ({0,1,2,5} : Finset (Fin 14)) ⊆ {0,1,2,5,11}) hi,mx_cap i hi⟩
  have bound := equality_hw_mask_family h hD mx_L (by decide) eligible {0,1,2} {3,4,6}
    {0,1,2,5} occurs centers ineligible Y
    (fun M hMY => ⟨(good M hMY).1,(good M hMY).2.1⟩)
    (fun M hMY pair => (good M hMY).2.2 pair)
  have ec := inelig_card_add 14 D
  rw [hI,show ({0,1,2,5,11} : Finset (Fin 14)).card = 5 from rfl] at ec
  rw [show ({0,1,2,5} : Finset (Fin 14)).card = 4 from rfl,mx_lab,
    show mx_L.card = 6 from rfl] at bound
  have zero := equality_mixed_cap_saturated h hD h14 hI
  rw [hM,Finset.card_singleton] at zero
  have total := totalSurplus_split 14 D
  omega
