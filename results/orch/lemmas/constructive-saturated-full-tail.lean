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
