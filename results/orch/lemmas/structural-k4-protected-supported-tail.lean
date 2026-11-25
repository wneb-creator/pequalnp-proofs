namespace PEqualNP.Outside.L_meta_6659_aux

theorem ke_reachable_chain {n : ℕ} {D : Dag} {i w : ℕ}
    (hprotected : ∀ u, Relation.ReflTransGen (sem_step n D) i u → fanout D u ≤ 1)
    (path : Relation.ReflTransGen (sem_step n D) i w) : sem_Chain n D i w := by
  induction path with
  | refl => exact Relation.ReflTransGen.refl
  | @tail a c prior step ih =>
    have one : fanout D a = 1 := by
      have := hprotected a prior
      have := sem_step_fanout step
      omega
    exact Relation.ReflTransGen.tail ih ⟨step,one⟩

theorem ke_full_gen_protected {D : Dag} (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D)
    {i v : Fin 10} (hi : i ∈ ineligSet 10 D) {e : ℕ × Bool}
    (he : sem_W 10 D i = {e}) (hiv : k4_Adj i v)
    (hprotected : ∀ w, Relation.ReflTransGen (sem_step 10 D) i.val w → fanout D w ≤ 1)
    (hv : ∀ p ∈ sem_W 10 D v, p.1 ≠ e.1 → ¬ supp 10 D (src D (sem_bar p)) ⊆ {i}) :
    ∀ t, t ∈ supp 10 D (src D (sem_bar e)) ↔ k4_Adj i t := by
  have hG := k4_gr
  have hC := hD
  have hS := h.1
  refine sem_full_support hG h hC hi he (fun j hreach hj => ?_)
  by_contra ht
  rw [Bool.not_eq_false] at ht
  rcases Relation.ReflTransGen.cases_tail hreach with heq | ⟨w, hw1, hw2⟩
  · exact hj (by omega)
  · obtain ⟨j', s, hj', hjeq, hsrc⟩ := sem_step_iff.1 hw2
    have hjj : j' = j := by omega
    subst hjj
    have hew : e ∈ sem_W 10 D i := by rw [he]; exact Finset.mem_singleton_self e
    obtain ⟨he1, he2, -⟩ := sem_mem_W.1 hew
    have hreach2 : Relation.ReflTransGen (sem_step 10 D) i.val w :=
      ((sem_rtg_mono (fun _ _ hab => hab.1) (sem_inelig_chain hS hi he2)).tail
        (sem_step_src he1 e.2)).trans hw1
    have hch := ke_reachable_chain hprotected hreach2
    have hf : fanout D w = 1 := by
      have := hprotected w hreach2
      have := sem_step_fanout hw2
      omega
    have hsub : supp 10 D w ⊆ {i} := sem_dom_pure hG hS hC i w (sem_chain_dom hS hch)
    have hvi : v ≠ i := fun hvi => hG.2.1 i (hvi ▸ hiv)
    have hw' : src D (j', !(!s)) = w := by rw [Bool.not_not]; exact hsrc
    have hmem : v ∈ supp 10 D (src D (j', !s)) :=
      sem_and_sibling_nbrs hG hS hC hj' (!s) ht (hw' ▸ hch) (hw' ▸ hf)
        (by unfold outW; omega) hiv
    have hp : ((j', !s) : ℕ × Bool) ∈ sem_W 10 D v :=
      sem_mem_W.2 ⟨hj', hmem, fun hc => by
        have := hsub (hsrc ▸ sem_supp_and_sub hS hj' ht s hc)
        exact hvi (Finset.mem_singleton.1 this)⟩
    exact hv _ hp hj (by rw [show sem_bar (j', !s) = (j', !(!s)) from rfl, hw']; exact hsub)

theorem ke_three_slot_protected {D : Dag} (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D)
    (pos : Fin 10 → ℕ × Bool)
    (hpos : k4_Pos 10 k4_Adj D pos) {x i j z : Fin 10}
    (hi : i ∈ ineligSet 10 D) (hj : j ∈ ineligSet 10 D)
    (hij : i ≠ j) (hix : k4_Adj i x) (hjx : k4_Adj j x) (hxz : k4_Adj x z)
    (hzi : z ≠ i) (hzj : z ≠ j) (small : (sem_W 10 D x).card ≤ 3)
    (hprotected : ∀ w, Relation.ReflTransGen (sem_step 10 D) i.val w → fanout D w ≤ 1) :
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
  have full := ke_full_gen_protected h hD hi (ke_as_W h hD hpos hi) hix hprotected
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


theorem ke_p6_protected_obstruction {D : Dag} (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D)
    (hB : Bplus 10 D ≤ 7) (hp : (eligSet 10 D).card = 6)
    {x t i : Fin 10} (hx4 : x.val < 4) (ht4 : t.val < 4)
    (hxm : ke_many (ineligSet 10 D) x) (htm : ke_many (ineligSet 10 D) t)
    (hi : i ∈ ineligSet 10 D) (hix : k4_Adj i x) (hit : ¬ k4_Adj i t)
    (hprotected : ∀ w, Relation.ReflTransGen (sem_step 10 D) i.val w → fanout D w ≤ 1) : False := by
  classical
  obtain ⟨b,hb⟩ := sem_exists_pureBranch k4_gr h.1 hD
  obtain ⟨pos,hpos⟩ := k4_assigned k4_gr h hD
  have wx := ke_two_neighbors_three h hD pos hpos hx4 hxm
  have wt := ke_two_neighbors_three h hD pos hpos ht4 htm
  have cx := ke_cc_le h hD b hb x
  have ct := ke_cc_le h hD b hb t
  have cr := card_residual h.1 b hb
  have hsubx : ((residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1)).card ≤
      (residualUnits 10 D b).card := Finset.card_le_card (Finset.filter_subset _ _)
  have hsubt : ((residualUnits 10 D b).filter (fun u => t ∈ supp 10 D u.1)).card ≤
      (residualUnits 10 D b).card := Finset.card_le_card (Finset.filter_subset _ _)
  have hR : (residualUnits 10 D b).card = 1 := by omega
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
  exact hit ((ke_three_slot_protected h hD pos hpos hi hj (Ne.symm hji) hix hjx hxz hzi hzj small hprotected t).1 htmem)


theorem ke_p7_supported_at_most_two {D : Dag} (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D)
    (hB : Bplus 10 D ≤ 7) (hp : (eligSet 10 D).card = 7) :
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
  have hsubx : ((residualUnits 10 D b).filter (fun u => x ∈ supp 10 D u.1)).card ≤
      (residualUnits 10 D b).card := Finset.card_le_card (Finset.filter_subset _ _)
  omega

theorem ke_low_supported_impossible {D : Dag} (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D)
    (hB : Bplus 10 D ≤ 7) (hp : (eligSet 10 D).card ≤ 5) : False := by
  classical
  obtain ⟨b,hb⟩ := sem_exists_pureBranch k4_gr h.1 hD
  obtain ⟨pos,hpos⟩ := k4_assigned k4_gr h hD
  have cr := card_residual h.1 b hb
  have cover : ∀ u v : Fin 10, k4_Adj u v → u ∈ eligSet 10 D ∨ v ∈ eligSet 10 D :=
    fun u v huv => sem_elig_cover k4_gr h hD huv
  rcases ke_low_cover_geometry (eligSet 10 D) cover hp with heq | ⟨omitted,heq⟩
  · have hp4 : (eligSet 10 D).card = 4 := by rw [heq]; decide
    have hR : (residualUnits 10 D b).card ≤ 3 := by omega
    have hin : ∀ i ∈ (Finset.univ : Finset (Fin 6)), Fin.natAdd 4 i ∈ ineligSet 10 D := by
      intro i _
      rw [sem_mem_inelig,heq]
      have geo : ∀ i : Fin 6, Fin.natAdd 4 i ∉ ({0,1,2,3} : Finset (Fin 10)) := by decide
      exact geo i
    have hw : ∀ x : Fin 4, 3 ≤ (sem_W 10 D (Fin.castLE (by decide : 4 ≤ 10) x)).card := by
      intro x
      exact ke_two_neighbors_three h hD pos hpos x.isLt
        (ke_large_edge_family_many Finset.univ (by decide) hin x)
    obtain ⟨M,hM,_,hbudget⟩ := ke_coordinate_budget h hD b hb pos hpos hR hw Finset.univ hin
    obtain ⟨t,ht⟩ := ke_p4_mask_certificate M hM
    have := hbudget t
    omega
  · have hp5 : (eligSet 10 D).card = 5 := by
      rw [heq]
      have geo : ∀ i : Fin 6, (insert (Fin.natAdd 4 i) ({0,1,2,3} : Finset (Fin 10))).card = 5 := by decide
      exact geo omitted
    have hR : (residualUnits 10 D b).card ≤ 2 := by omega
    let J := (Finset.univ : Finset (Fin 6)).erase omitted
    have hJ : J.card = 5 := by simp [J]
    have hin : ∀ i ∈ J, Fin.natAdd 4 i ∈ ineligSet 10 D := by
      intro i hi
      rw [sem_mem_inelig,heq]
      have ine := (Finset.mem_erase.mp hi).1
      have geo : ∀ o i : Fin 6, i ≠ o → Fin.natAdd 4 i ∉
          insert (Fin.natAdd 4 o) ({0,1,2,3} : Finset (Fin 10)) := by decide
      exact geo omitted i ine
    have hw : ∀ x : Fin 4, 3 ≤ (sem_W 10 D (Fin.castLE (by decide : 4 ≤ 10) x)).card := by
      intro x
      exact ke_two_neighbors_three h hD pos hpos x.isLt
        (ke_large_edge_family_many J (by omega) hin x)
    obtain ⟨M,hM,hunion,hbudget⟩ := ke_coordinate_budget h hD b hb pos hpos (by omega) hw J hin
    obtain ⟨t,ht⟩ := ke_p5_mask_certificate omitted M hM (by omega)
    have same : J.filter (fun i => ∃ x : Fin 4,
        k4_Adj (Fin.castLE (by decide : 4 ≤ 10) x) (Fin.natAdd 4 i) ∧ M x ⊆ M t) =
      Finset.univ.filter (fun i : Fin 6 => i ≠ omitted ∧ ∃ x : Fin 4,
        k4_Adj (Fin.castLE (by decide : 4 ≤ 10) x) (Fin.natAdd 4 i) ∧ M x ⊆ M t) := by
      ext i
      simp only [J,Finset.mem_filter,Finset.mem_erase,Finset.mem_univ,true_and,and_true]
    have bound := hbudget t
    rw [same] at bound
    omega

theorem ke_matching_protected_geometry : ∀ I : Finset (Fin 10),
    (∀ u ∈ I, ∀ v ∈ I, k4_adjB u v = false) → I.card = 4 → 5 ∈ I → 8 ∈ I →
    ∃ x t : Fin 10, x.val < 4 ∧ t.val < 4 ∧ ke_many I x ∧ ke_many I t ∧
      k4_Adj 5 x ∧ ¬ k4_Adj 5 t := by
  have cases : ∀ I : Finset (Fin 10),
      (∀ u ∈ I, ∀ v ∈ I, k4_adjB u v = false) → I.card = 4 → 5 ∈ I → 8 ∈ I →
      I = {4,5,6,8} ∨ I = {4,5,7,8} ∨ I = {4,5,8,9} ∨
      I = {5,6,7,8} ∨ I = {5,6,8,9} ∨ I = {5,7,8,9} := by decide +kernel
  intro I hind hcard h5 h8
  rcases cases I hind hcard h5 h8 with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0,1,by decide⟩
  · exact ⟨0,1,by decide⟩
  · exact ⟨0,1,by decide⟩
  · exact ⟨0,1,by decide⟩
  · exact ⟨0,3,by decide⟩
  · exact ⟨2,1,by decide⟩

theorem ke_protected_matching_supported_lower {D : Dag}
    (h : StrictLive 10 D) (hD : sem_Comp 10 k4_Adj D)
    (h5 : (5 : Fin 10) ∈ ineligSet 10 D) (h8 : (8 : Fin 10) ∈ ineligSet 10 D)
    (hprotected : ∀ w, Relation.ReflTransGen (sem_step 10 D) 5 w → fanout D w ≤ 1) :
    8 ≤ Bplus 10 D := by
  classical
  by_contra hn
  have hB : Bplus 10 D ≤ 7 := by omega
  have cover : ∀ u v : Fin 10, k4_Adj u v → u ∈ eligSet 10 D ∨ v ∈ eligSet 10 D :=
    fun u v huv => sem_elig_cover k4_gr h hD huv
  have geo : ∀ S : Finset (Fin 10),
      (∀ u v : Fin 10, k4_Adj u v → u ∈ S ∨ v ∈ S) → 5 ∉ S → 8 ∉ S →
      ({0,1,2,3} : Finset (Fin 10)) ⊆ S := by decide +kernel
  have sub := geo (eligSet 10 D) cover (sem_mem_inelig.mp h5) (sem_mem_inelig.mp h8)
  have horig : (({0,1,2,3} : Finset (Fin 10)) ∩ eligSet 10 D).card = 4 := by
    rw [Finset.inter_eq_left.mpr sub]
    decide
  obtain ⟨b,hb⟩ := sem_exists_pureBranch k4_gr h.1 hD
  have hp := elig_le_Bplus h.1 b hb
  by_cases small : (eligSet 10 D).card ≤ 5
  · exact ke_low_supported_impossible h hD hB small
  · by_cases six : (eligSet 10 D).card = 6
    · have hcard := inelig_card_add 10 D
      obtain ⟨x,t,hx,ht,hxm,htm,hix,hit⟩ := ke_matching_protected_geometry (ineligSet 10 D)
        (k4_inelig_indep h hD) (by omega) h5 h8
      exact ke_p6_protected_obstruction h hD hB six hx ht hxm htm h5 hix hit hprotected
    · have bound := ke_p7_supported_at_most_two h hD hB (by omega)
      omega

end PEqualNP.Outside.L_meta_6659_aux
