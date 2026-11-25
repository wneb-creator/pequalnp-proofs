namespace PEqualNP.Outside.L_meta_6659_aux

lemma and_on_fullstar_chain_is_other {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (twoW : ∀ x, (sem_W 14 D x).card ≤ 2)
    (andEmpty : ∀ j, j < D.length → tag D j = true → supp 14 D (14+j) = ∅)
    (x : Fin 14) (e f : Nat × Bool) (he : e ∈ sem_W 14 D x)
    (empty : supp 14 D (src D (sem_bar e)) = ∅)
    (code : sem_W 14 D x = {e,f})
    (neighbors : ∀ u, Adj x u → sem_bar f ∈ sem_W 14 D u)
    (j : Nat) (s : Bool) (hj : j < D.length) (hand : tag D j = true)
    (chain : sem_Chain 14 D (14+f.1) (src D (j,s)))
    (one : fanout D (src D (j,s)) = 1) : j = e.1 := by
  classical
  by_contra different
  have before : f.1 < j := by
    have upper := sem_src_lt h.1 hj s
    have lower := single_reader_chain_le h.1 chain
    omega
  have two : ∀ q ∈ sem_W 14 D x, q.1 = f.1 ∨ q.1 = e.1 := by
    intro q hq
    rw [code,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  have absent : x ∉ supp 14 D (src D (j,!s)) := by
    intro member
    have consumed : (j,!s) ∈ sem_W 14 D x := sem_mem_W.mpr
      ⟨hj,member,by rw [andEmpty j hj hand]; simp⟩
    rcases two (j,!s) consumed with atF | atE
    · simp only at atF
      omega
    · exact different atE
  have offroute : ¬ Relation.ReflTransGen (sem_step 14 D) (14+f.1) (src D (j,!s)) :=
    single_reader_other_unreachable h.1 chain (sem_step_src hj s) one
      (sem_step_src hj (!s)) (sem_src_ne h.1 hj s).symm
  have extended : sem_Chain 14 D (14+f.1) (14+j) :=
    Relation.ReflTransGen.tail chain ⟨sem_step_src hj s,one⟩
  have outEmpty : supp 14 D (outW 14 D) = ∅ := heawood_supp_out hD
  have full : ∀ u, Adj x u → u ∈ supp 14 D (src D (j,!s)) := by
    intro u hxu
    have baseFalse : val D (single u) (outW 14 D) = false := by
      cases value : val D (single u) (outW 14 D) with
      | false => rfl
      | true =>
        have member := mem_supp.mpr value
        rw [outEmpty] at member
        exact False.elim (Finset.notMem_empty u member)
    have positive : val D (sem_ins x (single u)) (outW 14 D) = true := by
      apply (sem_heawood_comp hD _).mpr
      refine ⟨x,u,hxu,sem_ins_self _ _,sem_ins_ge _ _ u ?_⟩
      simp [single]
    have survives := consumer_barrier_true h.1 x u e he empty f.1 (14+j) two
      extended (outW 14 D) (by unfold outW; omega)
      (by rw [outEmpty]; simp) baseFalse positive
    rw [sem_val_gate_src h.1 _ hj s,hand,gop_true,Bool.and_eq_true] at survives
    have same := two_consumers_offroute_agreement h.1 x u e he empty f.1
      (src D (j,!s)) two offroute absent
    exact mem_supp.mpr (same.trans survives.2)
  obtain ⟨u,v,huv,hxu,hxv,_,_⟩ := sem_hw_two_nbrs x x
  have edgeU := (hc_adjB_iff x u).mp hxu
  have edgeV := (hc_adjB_iff x v).mp hxv
  have oldU := neighbors u edgeU
  have oldV := neighbors v edgeV
  have newU : (j,!s) ∈ sem_W 14 D u := sem_mem_W.mpr
    ⟨hj,full u edgeU,by rw [andEmpty j hj hand]; simp⟩
  have newV : (j,!s) ∈ sem_W 14 D v := sem_mem_W.mpr
    ⟨hj,full v edgeV,by rw [andEmpty j hj hand]; simp⟩
  have positions : sem_bar f ≠ (j,!s) := by
    intro equal
    have indices := congrArg Prod.fst equal
    change f.1 = j at indices
    omega
  have ucode : sem_W 14 D u = {sem_bar f,(j,!s)} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro q hq
      simp only [Finset.mem_insert,Finset.mem_singleton] at hq
      rcases hq with rfl | rfl <;> assumption
    · rw [Finset.card_pair positions]
      exact twoW u
  obtain ⟨q,hq,missing⟩ := sem_antichain sem_heawood_gr h.1 (sem_heawood_comp hD) huv
  rw [ucode,Finset.mem_insert,Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · exact missing (sem_mem_W.mp oldV).2.1
  · exact missing (sem_mem_W.mp newV).2.1

end PEqualNP.Outside.L_meta_6659_aux
