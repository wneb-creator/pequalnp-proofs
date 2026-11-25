def pilotM10P : Finset (Fin 14) := {0,1,2}
def pilotM10I : Finset (Fin 14) := {0,1,2,11}
def pilotM10T : Finset (Fin 14) := {7,8,13}
def pilotM10L : Finset (Fin 14) := {7,8,9,10,12,13}

theorem pilotM10_geometry :
    pilotM10P ⊆ pilotM10I ∧ pilotM10T ⊆ pilotM10L ∧
    (∀ t ∈ pilotM10L, t ∉ pilotM10I) ∧
    (∀ t ∈ pilotM10T,
      (pilotM10P.filter (fun i => hc_adjB i t = true)).card = 2 ∧
      ∃ z : Fin 14, z ∉ pilotM10I ∧ Adj t z) ∧
    (∀ x ∈ pilotM10T, ∀ t ∈ pilotM10T, x ≠ t →
      ∀ i ∈ pilotM10P, Adj i x ∨ Adj i t) ∧
    (∀ i ∈ pilotM10P, ∃ x ∈ pilotM10T, Adj i x) ∧
    (∀ x ∈ pilotM10L, ∃ i ∈ pilotM10P, Adj i x) := by
  simp only [← hc_adjB_iff]
  refine ⟨by decide +kernel,by decide +kernel,by decide +kernel,?_,?_,?_,?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

def pilotM10_cfList (c : Fin 14) : List ℕ :=
  if c = 8 then [1,3,4,5,7,13,9,11,12,10]
  else if c = 13 then [0,3,5,6,7,10,8,12,11,9]
  else cfL7

theorem pilotM10_cofactor_geometry :
    ∀ c ∈ pilotM10T,
      cf_good c (pilotM10_cfList c) ∧
      cf_iota (pilotM10_cfList c) (1 : Fin 10) ∉ pilotM10I ∧
      cf_iota (pilotM10_cfList c) (1 : Fin 10) ≠ c ∧
      cf_iota (pilotM10_cfList c) (1 : Fin 10) ∉ pilotM10L ∧
      (pilotM10L.erase c).card = 5 := by
  decide +kernel

theorem pilotM10_co_label {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) (pos : Fin 14 → ℕ × Bool)
    (hpos : k4_Pos 14 HG D pos) {x t i : Fin 14}
    (hx : x ∈ eligSet 14 D) (ht : t ∈ eligSet 14 D)
    (hi : i ∈ ineligSet 14 D) (hix : Adj i x)
    (hne : (ru D b x).Nonempty) (hsub : ru D b x ⊆ ru D b t) :
    t ∈ supp 14 D (src D (pos i)) := by
  obtain ⟨u,hu⟩ := hne
  apply equality_residual_co_label h hD b hb pos hpos hx ht hi hix
  · intro v hv hvx
    exact (Finset.mem_filter.1 (hsub (Finset.mem_filter.2 ⟨hv,hvx⟩))).2
  · exact ⟨u.1,(Finset.mem_filter.1 hu).2,
      (Finset.mem_filter.1 (hsub hu)).2⟩

theorem pilotM10_triangle_nonempty {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hI : ineligSet 14 D = pilotM10I)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) (pos : Fin 14 → ℕ × Bool)
    (hpos : k4_Pos 14 HG D pos) :
    ∀ t ∈ pilotM10T, (ru D b t).Nonempty := by
  classical
  intro t ht
  obtain ⟨hPI,hTL,hLI,hN,hcover,hpoint,hline⟩ := pilotM10_geometry
  obtain ⟨hcard,z,hz,hedge⟩ := hN t ht
  have hze : z ∈ eligSet 14 D := by
    by_contra hn
    exact hz (hI ▸ sem_mem_inelig.2 hn)
  have hJ : ∀ i ∈ pilotM10P.filter (fun i => hc_adjB i t = true),
      i ∈ ineligSet 14 D ∧ t ∈ supp 14 D (src D (pos i)) := by
    intro i hi
    obtain ⟨hip,hit⟩ := Finset.mem_filter.1 hi
    have hii : i ∈ ineligSet 14 D := by rw [hI]; exact hPI hip
    exact ⟨hii,(hpos.1 i hii).2.2.1 t ((hc_adjB_iff _ _).1 hit)⟩
  have bound := equality_assigned_budget_extra h hD b hb pos hpos
    (pilotM10P.filter (fun i => hc_adjB i t = true)) hJ hze hedge
  rw [hcard] at bound
  exact Finset.card_pos.1 (by omega)

theorem pilotM10_triangle_no_equal_singleton {D : Dag}
    (h : StrictLive 14 D) (hD : Correct D) (hI : ineligSet 14 D = pilotM10I)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) (pos : Fin 14 → ℕ × Bool)
    (hpos : k4_Pos 14 HG D pos) {x t : Fin 14}
    (hxT : x ∈ pilotM10T) (htT : t ∈ pilotM10T) (hxt : x ≠ t)
    (heq : ru D b x = ru D b t) (hone : (ru D b t).card ≤ 1) : False := by
  classical
  obtain ⟨hPI,hTL,hLI,hN,hcover,hpoint,hline⟩ := pilotM10_geometry
  have eligible (z : Fin 14) (hz : z ∉ pilotM10I) : z ∈ eligSet 14 D := by
    by_contra hn
    exact hz (hI ▸ sem_mem_inelig.2 hn)
  have hxe := eligible x (hLI x (hTL hxT))
  have hte := eligible t (hLI t (hTL htT))
  have nonempty := pilotM10_triangle_nonempty h hD hI b hb pos hpos x hxT
  have hJ : ∀ i ∈ pilotM10P,
      i ∈ ineligSet 14 D ∧ t ∈ supp 14 D (src D (pos i)) := by
    intro i hi
    have hii : i ∈ ineligSet 14 D := by rw [hI]; exact hPI hi
    refine ⟨hii,?_⟩
    rcases hcover x hxT t htT hxt i hi with hix | hit
    · exact pilotM10_co_label h hD b hb pos hpos hxe hte hii hix nonempty
        (by rw [heq])
    · exact (hpos.1 i hii).2.2.1 t hit
  obtain ⟨_,z,hz,hedge⟩ := hN t htT
  have bound := equality_assigned_budget_extra h hD b hb pos hpos pilotM10P
    hJ (eligible z hz) hedge
  have count : pilotM10P.card = 3 := rfl
  omega

theorem pilotM10_full_triangle {D : Dag}
    (h : StrictLive 14 D) (hD : Correct D) (hI : ineligSet 14 D = pilotM10I)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) (pos : Fin 14 → ℕ × Bool)
    (hpos : k4_Pos 14 HG D pos) (hres : (residualUnits 14 D b).card ≤ 2) :
    ∃ c ∈ pilotM10T, (ru D b c).card = 2 ∧ ru D b c = residualUnits 14 D b := by
  classical
  have subset (x : Fin 14) : ru D b x ⊆ residualUnits 14 D b := Finset.filter_subset _ _
  have nonempty := pilotM10_triangle_nonempty h hD hI b hb pos hpos
  have distinct {x t : Fin 14} :=
    pilotM10_triangle_no_equal_singleton h hD hI b hb pos hpos (x := x) (t := t)
  have result := three_subsets_full (residualUnits 14 D b)
    (ru D b 7) (ru D b 8) (ru D b 13) hres (subset 7) (subset 8) (subset 13)
    (nonempty 7 (by decide)) (nonempty 8 (by decide)) (nonempty 13 (by decide))
    (fun eq small => distinct (by decide) (by decide) (by decide) eq (by rwa [← eq]))
    (fun eq small => distinct (by decide) (by decide) (by decide) eq (by rwa [← eq]))
    (fun eq small => distinct (by decide) (by decide) (by decide) eq (by rwa [← eq]))
  rcases result with h7 | h8 | h13
  · exact ⟨7,by decide,h7⟩
  · exact ⟨8,by decide,h8⟩
  · exact ⟨13,by decide,h13⟩

theorem pilotM10_Bplus_ge13 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hS : totalSurplus 14 D ≤ 14) (hI : ineligSet 14 D = pilotM10I) :
    13 ≤ Bplus 14 D := by
  classical
  by_contra hn
  obtain ⟨b,hb⟩ := exists_pureBranch h hD
  obtain ⟨pos,hpos⟩ := k4_assigned sem_heawood_gr h (sem_heawood_comp hD)
  have hp := inelig_card_add 14 D
  have hIc : pilotM10I.card = 4 := rfl
  rw [hI,hIc] at hp
  have hr := card_residual h.1 b hb
  have hres : (residualUnits 14 D b).card ≤ 2 := by omega
  obtain ⟨c,hcT,hcard,hfull⟩ := pilotM10_full_triangle h hD hI b hb pos hpos hres
  obtain ⟨hPI,hTL,hLI,hN,hcover,hpoint,hline⟩ := pilotM10_geometry
  have eligible (z : Fin 14) (hz : z ∉ pilotM10I) : z ∈ eligSet 14 D := by
    by_contra hn
    exact hz (hI ▸ sem_mem_inelig.2 hn)
  have hce := eligible c (hLI c (hTL hcT))
  have shared_rows : ∀ i ∈ pilotM10P, c ∈ supp 14 D (src D (pos i)) := by
    intro i hi
    obtain ⟨x,hxT,hix⟩ := hpoint i hi
    have hii : i ∈ ineligSet 14 D := by rw [hI]; exact hPI hi
    exact pilotM10_co_label h hD b hb pos hpos (eligible x (hLI x (hTL hxT))) hce
      hii hix (pilotM10_triangle_nonempty h hD hI b hb pos hpos x hxT)
      (by rw [hfull]; exact Finset.filter_subset _ _)
  let X := pilotM10L.erase c
  have hX : ∀ x ∈ X, x ∈ eligSet 14 D ∧ x ≠ c ∧
      (∀ u ∈ residualUnits 14 D b, x ∈ supp 14 D u.1 → c ∈ supp 14 D u.1) ∧
      ∃ w, x ∈ supp 14 D w ∧ c ∈ supp 14 D w := by
    intro x hx
    obtain ⟨hxc,hxL⟩ := Finset.mem_erase.1 hx
    refine ⟨eligible x (hLI x hxL),hxc,?_,?_⟩
    · intro u hu _
      have huc : u ∈ ru D b c := by rw [hfull]; exact hu
      exact (Finset.mem_filter.1 huc).2
    · obtain ⟨i,hi,hix⟩ := hline x hxL
      have hii : i ∈ ineligSet 14 D := by rw [hI]; exact hPI hi
      exact ⟨src D (pos i),(hpos.1 i hii).2.2.1 x hix,shared_rows i hi⟩
  obtain ⟨hgood,hfree,hne,hout,hXcard⟩ := pilotM10_cofactor_geometry c hcT
  have bound := equality_cf_seven_free h hD b hb hgood hce X hX
    (by decide : (1 : Fin 10).val < 4) (eligible _ hfree) hne
    (fun hx => hout (Finset.mem_erase.1 hx).2)
  change X.card = 5 at hXcard
  omega

theorem pilotM10_Bzero_le1 {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hS : totalSurplus 14 D ≤ 14) (hI : ineligSet 14 D = pilotM10I) :
    Bzero 14 D ≤ 1 := by
  have lower := pilotM10_Bplus_ge13 h hD hS hI
  have split := totalSurplus_split 14 D
  omega
