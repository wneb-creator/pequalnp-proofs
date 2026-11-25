import PNPAccepted6659
namespace PEqualNP.Outside.L_meta_6659_aux

theorem equality_reachable_chain {n : ℕ} {D : Dag} {i w : ℕ}
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

theorem equality_full_gen_protected {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    {i v : Fin 14} (hi : i ∈ ineligSet 14 D) {e : ℕ × Bool}
    (he : sem_W 14 D i = {e}) (hiv : Adj i v)
    (hprotected : ∀ w, Relation.ReflTransGen (sem_step 14 D) i.val w → fanout D w ≤ 1)
    (hv : ∀ p ∈ sem_W 14 D v, p.1 ≠ e.1 → ¬ supp 14 D (src D (sem_bar p)) ⊆ {i}) :
    ∀ t, t ∈ supp 14 D (src D (sem_bar e)) ↔ Adj i t := by
  have hG := sem_heawood_gr
  have hC := sem_heawood_comp hD
  have hS := h.1
  refine sem_full_support hG h hC hi he (fun j hreach hj => ?_)
  by_contra ht
  rw [Bool.not_eq_false] at ht
  rcases Relation.ReflTransGen.cases_tail hreach with heq | ⟨w, hw1, hw2⟩
  · exact hj (by omega)
  · obtain ⟨j', s, hj', hjeq, hsrc⟩ := sem_step_iff.1 hw2
    have hjj : j' = j := by omega
    subst hjj
    have hew : e ∈ sem_W 14 D i := by rw [he]; exact Finset.mem_singleton_self e
    obtain ⟨he1, he2, -⟩ := sem_mem_W.1 hew
    have hreach2 : Relation.ReflTransGen (sem_step 14 D) i.val w :=
      ((sem_rtg_mono (fun _ _ hab => hab.1) (sem_inelig_chain hS hi he2)).tail
        (sem_step_src he1 e.2)).trans hw1
    have hch := equality_reachable_chain hprotected hreach2
    have hf : fanout D w = 1 := by
      have := hprotected w hreach2
      have := sem_step_fanout hw2
      omega
    have hsub : supp 14 D w ⊆ {i} := sem_dom_pure hG hS hC i w (sem_chain_dom hS hch)
    have hvi : v ≠ i := fun hvi => hG.2.1 i (hvi ▸ hiv)
    have hw' : src D (j', !(!s)) = w := by rw [Bool.not_not]; exact hsrc
    have hmem : v ∈ supp 14 D (src D (j', !s)) :=
      sem_and_sibling_nbrs hG hS hC hj' (!s) ht (hw' ▸ hch) (hw' ▸ hf)
        (by unfold outW; omega) hiv
    have hp : ((j', !s) : ℕ × Bool) ∈ sem_W 14 D v :=
      sem_mem_W.2 ⟨hj', hmem, fun hc => by
        have := hsub (hsrc ▸ sem_supp_and_sub hS hj' ht s hc)
        exact hvi (Finset.mem_singleton.1 this)⟩
    exact hv _ hp hj (by rw [show sem_bar (j', !s) = (j', !(!s)) from rfl, hw']; exact hsub)

theorem equality_residual_co_label {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) (pos : Fin 14 → ℕ × Bool)
    (hpos : k4_Pos 14 HG D pos) {x t i : Fin 14}
    (hx : x ∈ eligSet 14 D) (ht : t ∈ eligSet 14 D) (hi : i ∈ ineligSet 14 D)
    (hix : Adj i x)
    (inclusion : ∀ u ∈ residualUnits 14 D b, x ∈ supp 14 D u.1 → t ∈ supp 14 D u.1)
    (shared : ∃ w, x ∈ supp 14 D w ∧ t ∈ supp 14 D w) :
    t ∈ supp 14 D (src D (pos i)) := by
  by_cases hxt : x = t
  · exact hxt ▸ (hpos.1 i hi).2.2.1 x hix
  obtain ⟨w,hw⟩ := shared
  obtain ⟨e0,he0⟩ := ri_gen sem_heawood_gr h (sem_heawood_comp hD) b hb hxt hx inclusion hw
  have hti : t ≠ i := fun equal => sem_mem_inelig.1 hi (equal ▸ ht)
  have hgeo : ∀ i x t : Fin 14, hc_adjB i x = true → t ≠ x → t ≠ i →
      ∃ q, hc_adjB i q = true ∧ q ≠ x ∧ hc_adjB t q = false := by decide +kernel
  obtain ⟨q,hiq,hqx,htq⟩ := hgeo i x t ((hc_adjB_iff _ _).2 hix) (Ne.symm hxt) hti
  have hiq' := (hc_adjB_iff _ _).1 hiq
  have htq' := sem_adjB_false.1 htq
  by_contra hnot
  have heq : pos i = e0 := by
    by_contra hne
    exact hnot (he0 _ (as_mem hpos hi hix) hne)
  obtain ⟨e,he,hnt,hnq⟩ := sem_hw_cover_free h hD hxt (Ne.symm hqx) htq'
  exact hnt (he0 e he (fun equal => hnq (by
    rw [equal,← heq]
    exact (hpos.1 i hi).2.2.1 q hiq')))

theorem equality_three_slot_full {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) (pos : Fin 14 → ℕ × Bool)
    (hpos : k4_Pos 14 HG D pos) {x i j z : Fin 14}
    (hi : i ∈ ineligSet 14 D) (hj : j ∈ ineligSet 14 D)
    (hij : i ≠ j) (hix : Adj i x) (hjx : Adj j x) (hxz : Adj x z)
    (hzi : z ≠ i) (hzj : z ≠ j) (hru : (ru D b x).card ≤ 1)
    (hprotected : ∀ w, Relation.ReflTransGen (sem_step 14 D) i.val w → fanout D w ≤ 1) :
    ∀ t, t ∈ supp 14 D (src D (pos i)) ↔ Adj i t := by
  classical
  obtain ⟨H,hHx,hHz,_,_,_⟩ := sem_edge_slots sem_heawood_gr h.1 (sem_heawood_comp hD) hxz
  have ai := as_mem hpos hi hix
  have aj := as_mem hpos hj hjx
  have ni : H ≠ pos i := fun equal => hzi (as_priv hpos hi (equal ▸ hHz))
  have nj : H ≠ pos j := fun equal => hzj (as_priv hpos hj (equal ▸ hHz))
  have nij : pos i ≠ pos j := fun equal => hij (hpos.2 i hi j hj equal)
  have small : (sem_W 14 D x).card ≤ 3 := by
    have := cc_le h hD b hb x
    omega
  have code : sem_W 14 D x = {pos i,pos j,H} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro e he
      simp only [Finset.mem_insert,Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl <;> assumption
    · rw [Finset.card_insert_of_notMem (by simp [nij,Ne.symm ni]),
        Finset.card_pair (Ne.symm nj)]
      exact small
  have full := equality_full_gen_protected h hD hi (as_W h hD hpos hi) hix hprotected
    (fun p hp hne hsub => by
      rw [code] at hp
      simp only [Finset.mem_insert,Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact hne rfl
      · have hjmem : j ∈ supp 14 D (src D (sem_bar (pos j))) := by
          rw [show src D (sem_bar (pos j)) = src D ((pos j).1,!(pos j).2) from rfl,
            (hpos.1 j hj).2.2.2]
          exact Finset.mem_singleton_self j
        exact hij (Finset.mem_singleton.1 (hsub hjmem)).symm
      · exact hzi (Finset.mem_singleton.1 (hsub (sem_mem_W.1 hHz).2.1)))
  simpa only [sem_bar_bar] using full

theorem equality_assigned_mem {D : Dag} {pos : Fin 14 → ℕ × Bool}
    (hpos : k4_Pos 14 HG D pos) {i t : Fin 14} (hi : i ∈ ineligSet 14 D)
    (ht : t ∈ supp 14 D (src D (pos i))) : pos i ∈ sem_W 14 D t :=
  sem_mem_W.2 ⟨(hpos.1 i hi).1,ht,by
    rw [(hpos.1 i hi).2.1]
    exact Finset.notMem_empty t⟩

theorem equality_assigned_budget {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) (pos : Fin 14 → ℕ × Bool)
    (hpos : k4_Pos 14 HG D pos) (J : Finset (Fin 14)) {t : Fin 14}
    (hJ : ∀ i ∈ J, i ∈ ineligSet 14 D ∧ t ∈ supp 14 D (src D (pos i))) :
    J.card ≤ 2 + (ru D b t).card := by
  classical
  have injective : Set.InjOn pos (J : Set (Fin 14)) :=
    fun i hi j hj equal => hpos.2 i (hJ i hi).1 j (hJ j hj).1 equal
  have subset : J.image pos ⊆ sem_W 14 D t := by
    intro e he
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.1 he
    exact equality_assigned_mem hpos (hJ i hi).1 (hJ i hi).2
  have lower := Finset.card_le_card subset
  rw [Finset.card_image_of_injOn injective] at lower
  have upper := cc_le h hD b hb t
  omega

theorem equality_assigned_budget_extra {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) (pos : Fin 14 → ℕ × Bool)
    (hpos : k4_Pos 14 HG D pos) (J : Finset (Fin 14)) {t z : Fin 14}
    (hJ : ∀ i ∈ J, i ∈ ineligSet 14 D ∧ t ∈ supp 14 D (src D (pos i)))
    (hz : z ∈ eligSet 14 D) (edge : Adj t z) :
    J.card + 1 ≤ 2 + (ru D b t).card := by
  classical
  obtain ⟨H,hHt,hHz,_,_,_⟩ := sem_edge_slots sem_heawood_gr h.1 (sem_heawood_comp hD) edge
  have injective : Set.InjOn pos (J : Set (Fin 14)) :=
    fun i hi j hj equal => hpos.2 i (hJ i hi).1 j (hJ j hj).1 equal
  have fresh : H ∉ J.image pos := by
    intro he
    obtain ⟨i,hi,equal⟩ := Finset.mem_image.1 he
    have same : z = i := as_priv hpos (hJ i hi).1 (equal ▸ hHz)
    exact sem_mem_inelig.1 (hJ i hi).1 (same ▸ hz)
  have subset : insert H (J.image pos) ⊆ sem_W 14 D t := by
    intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · exact hHt
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.1 he
      exact equality_assigned_mem hpos (hJ i hi).1 (hJ i hi).2
  have lower := Finset.card_le_card subset
  rw [Finset.card_insert_of_notMem fresh,Finset.card_image_of_injOn injective] at lower
  have upper := cc_le h hD b hb t
  omega

theorem equality_saturated_slot_full {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) (pos : Fin 14 → ℕ × Bool)
    (hpos : k4_Pos 14 HG D pos) (J : Finset (Fin 14)) {x i z : Fin 14}
    (hJ : ∀ j ∈ J, j ∈ ineligSet 14 D ∧ x ∈ supp 14 D (src D (pos j)))
    (hiJ : i ∈ J) (hix : Adj i x) (hz : z ∈ eligSet 14 D) (hxz : Adj x z)
    (saturated : 2 + (ru D b x).card ≤ J.card + 1)
    (hprotected : ∀ w, Relation.ReflTransGen (sem_step 14 D) i.val w → fanout D w ≤ 1) :
    ∀ t, t ∈ supp 14 D (src D (pos i)) ↔ Adj i t := by
  classical
  have hi := (hJ i hiJ).1
  obtain ⟨H,hHx,hHz,_,_,_⟩ :=
    sem_edge_slots sem_heawood_gr h.1 (sem_heawood_comp hD) hxz
  have injective : Set.InjOn pos (J : Set (Fin 14)) :=
    fun j hj k hk equal => hpos.2 j (hJ j hj).1 k (hJ k hk).1 equal
  have fresh : H ∉ J.image pos := by
    intro member
    obtain ⟨j,hj,equal⟩ := Finset.mem_image.1 member
    have same : z = j := as_priv hpos (hJ j hj).1 (equal ▸ hHz)
    exact sem_mem_inelig.1 (hJ j hj).1 (same ▸ hz)
  have subset : insert H (J.image pos) ⊆ sem_W 14 D x := by
    intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp
    · exact hHx
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.1 hp
      exact equality_assigned_mem hpos (hJ j hj).1 (hJ j hj).2
  have code : sem_W 14 D x = insert H (J.image pos) := by
    symm
    apply Finset.eq_of_subset_of_card_le subset
    rw [Finset.card_insert_of_notMem fresh,Finset.card_image_of_injOn injective]
    have upper := cc_le h hD b hb x
    omega
  have full := equality_full_gen_protected h hD hi (as_W h hD hpos hi) hix hprotected
    (fun p hp hne hsub => by
      rw [code] at hp
      rcases Finset.mem_insert.1 hp with rfl | hp
      · have same : z = i := Finset.mem_singleton.1 (hsub (sem_mem_W.1 hHz).2.1)
        exact sem_mem_inelig.1 hi (same ▸ hz)
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.1 hp
        have member : j ∈ supp 14 D (src D (sem_bar (pos j))) := by
          rw [show src D (sem_bar (pos j)) = src D ((pos j).1,!(pos j).2) from rfl,
            (hpos.1 j (hJ j hj).1).2.2.2]
          exact Finset.mem_singleton_self j
        have same : j = i := Finset.mem_singleton.1 (hsub member)
        exact hne (by rw [same]; rfl))
  simpa only [sem_bar_bar] using full

end PEqualNP.Outside.L_meta_6659_aux
