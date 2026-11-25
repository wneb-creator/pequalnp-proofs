namespace PEqualNP.Outside.L_meta_6659_aux

theorem ke_as_mem {D : Dag} {pos : Fin 10 → ℕ × Bool} (hpos : k4_Pos 10 k4_Adj D pos) {i a : Fin 10} (hi : i ∈ ineligSet 10 D)
    (hia : k4_Adj i a) : pos i ∈ sem_W 10 D a := by
  obtain ⟨h1, h2, h4, -⟩ := hpos.1 i hi
  exact sem_mem_W.2 ⟨h1, h4 a hia, by rw [h2]; exact Finset.notMem_empty a⟩

/-- The position opposite the assigned one is private to `i`. -/
theorem ke_as_priv {D : Dag} {pos : Fin 10 → ℕ × Bool} (hpos : k4_Pos 10 k4_Adj D pos) {i t : Fin 10} (hi : i ∈ ineligSet 10 D)
    (ht : sem_bar (pos i) ∈ sem_W 10 D t) : t = i := by
  have := (sem_mem_W.1 ht).2.1
  rw [show src D (sem_bar (pos i)) = src D ((pos i).1, !(pos i).2) from rfl,
    (hpos.1 i hi).2.2.2] at this
  exact Finset.mem_singleton.1 this

theorem ke_as_W {D : Dag} {pos : Fin 10 → ℕ × Bool} (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D) (hpos : k4_Pos 10 k4_Adj D pos) {i : Fin 10}
    (hi : i ∈ ineligSet 10 D) : sem_W 10 D i = {sem_bar (pos i)} := by
  obtain ⟨e, -, -, h3, -, -, h6, -⟩ :=
    sem_inelig_consumer k4_gr h hD hi
  obtain ⟨h1, h2, -, h5⟩ := hpos.1 i hi
  have hm : sem_bar (pos i) ∈ sem_W 10 D i :=
    sem_mem_W.2 ⟨h1, by
      rw [show src D (sem_bar (pos i)) = src D ((pos i).1, !(pos i).2) from rfl, h5]
      exact Finset.mem_singleton_self i, by
      rw [show (sem_bar (pos i)).1 = (pos i).1 from rfl, h2]; exact Finset.notMem_empty i⟩
  have h7 : sem_W 10 D i = {e} := h6
  rw [h7] at hm ⊢
  rw [Finset.mem_singleton.1 hm]

theorem ke_residual_co_label {D : Dag} (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D)
    (b : Fin 10 → ℕ) (hb : PureBranch 10 D b) (pos : Fin 10 → ℕ × Bool)
    (hpos : k4_Pos 10 k4_Adj D pos) {x t i : Fin 10}
    (hx : x ∈ eligSet 10 D) (ht : t ∈ eligSet 10 D) (hi : i ∈ ineligSet 10 D)
    (hix : k4_Adj i x) (hx4 : x.val < 4) (ht4 : t.val < 4)
    (inclusion : ∀ u ∈ residualUnits 10 D b, x ∈ supp 10 D u.1 → t ∈ supp 10 D u.1)
    (shared : ∃ w, x ∈ supp 10 D w ∧ t ∈ supp 10 D w) :
    t ∈ supp 10 D (src D (pos i)) := by
  by_cases hxt : x = t
  · exact hxt ▸ (hpos.1 i hi).2.2.1 x hix
  obtain ⟨w,hw⟩ := shared
  obtain ⟨e0,he0⟩ := ri_gen k4_gr h hD b hb hxt hx inclusion hw
  have hti : t ≠ i := fun equal => sem_mem_inelig.1 hi (equal ▸ ht)
  have hgeo : ∀ i x t : Fin 10, k4_adjB i x = true → x.val < 4 → t.val < 4 →
      t ≠ x → ∃ q, k4_adjB i q = true ∧ q ≠ x ∧ k4_adjB t q = false := by decide +kernel
  obtain ⟨q,hiq,hqx,htq⟩ := hgeo i x t hix hx4 ht4 (Ne.symm hxt)
  have hiq' : k4_Adj i q := hiq
  have htq' : ¬ k4_Adj t q := by simpa only [k4_Adj,htq] using Bool.false_ne_true
  by_contra hnot
  have heq : pos i = e0 := by
    by_contra hne
    exact hnot (he0 _ (ke_as_mem hpos hi hix) hne)
  have hfree : ∀ x t q : Fin 10, x.val < 4 → t.val < 4 → q.val < 4 → x ≠ t → x ≠ q →
      ∃ y, k4_Adj x y ∧ ¬ k4_Adj y t ∧ ¬ k4_Adj y q := by decide +kernel
  have hq4 : q.val < 4 := by
    have hgeo : ∀ i x q : Fin 10, k4_adjB i x = true → x.val < 4 → k4_adjB i q = true → q.val < 4 := by decide +kernel
    exact hgeo i x q hix hx4 hiq
  obtain ⟨y,hxy,hyt,hyq⟩ := hfree x t q hx4 ht4 hq4 hxt (Ne.symm hqx)
  obtain ⟨e,he,hnt,hnq⟩ := sem_cover_free k4_gr h.1 hD htq' hxy hyt hyq
  exact hnt (he0 e he (fun equal => hnq (by
    rw [equal,← heq]
    exact (hpos.1 i hi).2.2.1 q hiq')))

theorem ke_three_slot_full {D : Dag} (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D)
    (hB0 : Bzero 10 D = 0) (pos : Fin 10 → ℕ × Bool)
    (hpos : k4_Pos 10 k4_Adj D pos) {x i j z : Fin 10}
    (hi : i ∈ ineligSet 10 D) (hj : j ∈ ineligSet 10 D)
    (hij : i ≠ j) (hix : k4_Adj i x) (hjx : k4_Adj j x) (hxz : k4_Adj x z)
    (hzi : z ≠ i) (hzj : z ≠ j) (small : (sem_W 10 D x).card ≤ 3) :
    ∀ t, t ∈ supp 10 D (src D (pos i)) ↔ k4_Adj i t := by
  classical
  obtain ⟨H,hHx,hHz,_,_,_⟩ := sem_edge_slots k4_gr h.1 hD hxz
  have ai := ke_as_mem hpos hi hix
  have aj := ke_as_mem hpos hj hjx
  have ni : H ≠ pos i := fun equal => hzi (ke_as_priv hpos hi (equal ▸ hHz))
  have nj : H ≠ pos j := fun equal => hzj (ke_as_priv hpos hj (equal ▸ hHz))
  have nij : pos i ≠ pos j := fun equal => hij (hpos.2 i hi j hj equal)
  have code : sem_W 10 D x = {pos i,pos j,H} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro e he
      simp only [Finset.mem_insert,Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl <;> assumption
    · rw [Finset.card_insert_of_notMem (by simp [nij,Ne.symm ni]),
        Finset.card_pair (Ne.symm nj)]
      exact small
  have full := full_gen k4_gr h hD hB0 hi (ke_as_W h hD hpos hi) hix
    (fun p hp hne hsub => by
      rw [code] at hp
      simp only [Finset.mem_insert,Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact hne rfl
      · have hjmem : j ∈ supp 10 D (src D (sem_bar (pos j))) := by
          rw [show src D (sem_bar (pos j)) = src D ((pos j).1,!(pos j).2) from rfl,
            (hpos.1 j hj).2.2.2]
          exact Finset.mem_singleton_self j
        exact hij (Finset.mem_singleton.1 (hsub hjmem)).symm
      · exact hzi (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hHz).2.1)))
  simpa only [sem_bar_bar] using full


theorem ke_cc_le {D : Dag} (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D)
    (b : Fin 10 → ℕ) (hb : PureBranch 10 D b) (x : Fin 10) :
    (sem_W 10 D x).card ≤ 2 +
      ((residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1)).card := by
  have h1 := sem_code_count k4_gr h hD b hb x
  have h2 := Finset.card_le_card
    (Finset.inter_subset_left : ({x} : Finset (Fin 10)) ∩ eligSet 10 D ⊆ {x})
  rw [Finset.card_singleton] at h2
  omega

abbrev ke_many (I : Finset (Fin 10)) (x : Fin 10) : Prop :=
  2 ≤ (I.filter (fun i => k4_Adj i x)).card

theorem ke_neighbor_pair {I : Finset (Fin 10)} {x i : Fin 10}
    (hm : ke_many I x) (hi : i ∈ I) (hix : k4_Adj i x) :
    ∃ j ∈ I, j ≠ i ∧ k4_Adj j x := by
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (by exact hm)
  obtain ⟨haI,hax⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbI,hbx⟩ := Finset.mem_filter.mp hb
  by_cases hai : a = i
  · exact ⟨b,hbI,by simpa only [hai] using Ne.symm hab,hbx⟩
  · exact ⟨a,haI,hai,hax⟩

theorem ke_two_neighbors_three {D : Dag} (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D)
    (pos : Fin 10 → ℕ × Bool) (hpos : k4_Pos 10 k4_Adj D pos) {x : Fin 10}
    (hx4 : x.val < 4) (hm : ke_many (ineligSet 10 D) x) :
    3 ≤ (sem_W 10 D x).card := by
  obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp (by exact hm)
  obtain ⟨hiI,hix⟩ := Finset.mem_filter.mp hi
  obtain ⟨hjI,hjx⟩ := Finset.mem_filter.mp hj
  have hgeo : ∀ x i j : Fin 10, x.val < 4 → k4_Adj i x → k4_Adj j x → i ≠ j →
      ∃ z, k4_Adj x z ∧ z ≠ i ∧ z ≠ j := by decide +kernel
  obtain ⟨z,hxz,hzi,hzj⟩ := hgeo x i j hx4 hix hjx hij
  exact k4_three_cons k4_gr h hD hpos hiI hjI hij (Ne.symm hzi) (Ne.symm hzj)
    (k4_gr.1 _ _ hix) (k4_gr.1 _ _ hjx) hxz

theorem ke_p6_obstruction {D : Dag} (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D)
    (hB : totalSurplus 10 D ≤ 7) (hp : (eligSet 10 D).card = 6)
    {x t i : Fin 10} (hx4 : x.val < 4) (ht4 : t.val < 4)
    (hxm : ke_many (ineligSet 10 D) x) (htm : ke_many (ineligSet 10 D) t)
    (hi : i ∈ ineligSet 10 D) (hix : k4_Adj i x) (hit : ¬ k4_Adj i t) : False := by
  classical
  obtain ⟨b,hb⟩ := sem_exists_pureBranch k4_gr h.1 hD
  obtain ⟨pos,hpos⟩ := k4_assigned k4_gr h hD
  have wx := ke_two_neighbors_three h hD pos hpos hx4 hxm
  have wt := ke_two_neighbors_three h hD pos hpos ht4 htm
  have cx := ke_cc_le h hD b hb x
  have ct := ke_cc_le h hD b hb t
  have cr := card_residual h.1 b hb
  have split := totalSurplus_split 10 D
  have hsubx : ((residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1)).card ≤
      (residualUnits 10 D b).card := Finset.card_le_card (Finset.filter_subset _ _)
  have hsubt : ((residualUnits 10 D b).filter (fun u => t ∈ supp 10 D u.1)).card ≤
      (residualUnits 10 D b).card := Finset.card_le_card (Finset.filter_subset _ _)
  have hR : (residualUnits 10 D b).card = 1 := by omega
  have hB0 : Bzero 10 D = 0 := by omega
  have small : (sem_W 10 D x).card ≤ 3 := by omega
  obtain ⟨rx,hrx⟩ := Finset.card_pos.mp (by omega :
    0 < ((residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1)).card)
  obtain ⟨rt,hrt⟩ := Finset.card_pos.mp (by omega :
    0 < ((residualUnits 10 D b).filter (fun u => t ∈ supp 10 D u.1)).card)
  obtain ⟨hrxR,hrxx⟩ := Finset.mem_filter.mp hrx
  obtain ⟨hrtR,hrtt⟩ := Finset.mem_filter.mp hrt
  have huniq : ∀ u ∈ residualUnits 10 D b, u = rt := fun u hu =>
    Finset.card_le_one.mp (by omega) u hu rt hrtR
  have incl : ∀ u ∈ residualUnits 10 D b, x ∈ supp 10 D u.1 → t ∈ supp 10 D u.1 := by
    intro u hu _
    rw [huniq u hu]
    exact hrtt
  have htmem := ke_residual_co_label h hD b hb pos hpos (res_elig hrxR hrxx)
    (res_elig hrtR hrtt) hi hix hx4 ht4 incl ⟨rx.1,hrxx,by rw [huniq rx hrxR];exact hrtt⟩
  obtain ⟨j,hj,hji,hjx⟩ := ke_neighbor_pair hxm hi hix
  have hgeo : ∀ x i j : Fin 10, x.val < 4 → k4_Adj i x → k4_Adj j x → i ≠ j →
      ∃ z, k4_Adj x z ∧ z ≠ i ∧ z ≠ j := by decide +kernel
  obtain ⟨z,hxz,hzi,hzj⟩ := hgeo x i j hx4 hix hjx (Ne.symm hji)
  exact hit ((ke_three_slot_full h hD hB0 pos hpos hi hj (Ne.symm hji) hix hjx hxz hzi hzj small t).1 htmem)


theorem ke_p6_geometry : ∀ I : Finset (Fin 10),
    (∀ u ∈ I, ∀ v ∈ I, k4_adjB u v = false) → I.card = 4 →
    3 ≤ (({0,1,2,3} : Finset (Fin 10)) \ I).card →
    ∃ x t i : Fin 10, x.val < 4 ∧ t.val < 4 ∧ ke_many I x ∧ ke_many I t ∧
      i ∈ I ∧ k4_Adj i x ∧ ¬ k4_Adj i t := by decide +kernel

theorem ke_p6_at_most_two {D : Dag} (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D)
    (hB : totalSurplus 10 D ≤ 7) (hp : (eligSet 10 D).card = 6) :
    (({0,1,2,3} : Finset (Fin 10)) ∩ eligSet 10 D).card ≤ 2 := by
  classical
  by_contra hnot
  have hcard := inelig_card_add 10 D
  have hIcard : (ineligSet 10 D).card = 4 := by omega
  have heq : ({0,1,2,3} : Finset (Fin 10)) \ ineligSet 10 D =
      ({0,1,2,3} : Finset (Fin 10)) ∩ eligSet 10 D := by
    ext i
    simp only [Finset.mem_sdiff,Finset.mem_inter,sem_mem_inelig,not_not]
  obtain ⟨x,t,i,hx4,ht4,hxm,htm,hi,hix,hit⟩ := ke_p6_geometry (ineligSet 10 D)
    (k4_inelig_indep h hD) hIcard (by rw [heq]; omega)
  exact ke_p6_obstruction h hD hB hp hx4 ht4 hxm htm hi hix hit


theorem ke_p7_geometry : ∀ I : Finset (Fin 10),
    (∀ u ∈ I, ∀ v ∈ I, k4_adjB u v = false) → I.card = 3 →
    3 ≤ (({0,1,2,3} : Finset (Fin 10)) \ I).card →
    ∃ x : Fin 10, x.val < 4 ∧ ke_many I x := by decide +kernel

theorem ke_p7_at_most_two {D : Dag} (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D)
    (hB : totalSurplus 10 D ≤ 7) (hp : (eligSet 10 D).card = 7) :
    (({0,1,2,3} : Finset (Fin 10)) ∩ eligSet 10 D).card ≤ 2 := by
  classical
  by_contra hnot
  have hcard := inelig_card_add 10 D
  have hIcard : (ineligSet 10 D).card = 3 := by omega
  have heq : ({0,1,2,3} : Finset (Fin 10)) \ ineligSet 10 D =
      ({0,1,2,3} : Finset (Fin 10)) ∩ eligSet 10 D := by
    ext i
    simp only [Finset.mem_sdiff,Finset.mem_inter,sem_mem_inelig,not_not]
  obtain ⟨x,hx4,hxm⟩ := ke_p7_geometry (ineligSet 10 D)
    (k4_inelig_indep h hD) hIcard (by rw [heq]; omega)
  obtain ⟨b,hb⟩ := sem_exists_pureBranch k4_gr h.1 hD
  obtain ⟨pos,hpos⟩ := k4_assigned k4_gr h hD
  have wx := ke_two_neighbors_three h hD pos hpos hx4 hxm
  have cx := ke_cc_le h hD b hb x
  have cr := card_residual h.1 b hb
  have split := totalSurplus_split 10 D
  have hsubx : ((residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1)).card ≤
      (residualUnits 10 D b).card := Finset.card_le_card (Finset.filter_subset _ _)
  omega

end PEqualNP.Outside.L_meta_6659_aux
