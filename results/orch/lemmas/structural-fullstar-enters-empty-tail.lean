namespace PEqualNP.Outside.L_meta_6659_aux

lemma fullstar_chain_enters_empty {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (x : Fin 14) (e f : Nat × Bool) (he : e ∈ sem_W 14 D x)
    (empty : supp 14 D (src D (sem_bar e)) = ∅)
    (code : sem_W 14 D x = {e,f})
    (s : Bool) (chain : sem_Chain 14 D (14+f.1) (src D (e.1,s)))
    (one : fanout D (src D (e.1,s)) = 1) : s = !e.2 := by
  classical
  have hj := (sem_mem_W.mp he).1
  have hand := sem_W_and h.1 he
  have two : ∀ q ∈ sem_W 14 D x, q.1 = f.1 ∨ q.1 = e.1 := by
    intro q hq
    rw [code,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  by_contra unequal
  have same : s = e.2 := by cases s <;> cases side : e.2 <;> simp_all
  subst s
  have offroute : ¬ Relation.ReflTransGen (sem_step 14 D) (14+f.1)
      (src D (sem_bar e)) :=
    single_reader_other_unreachable h.1 chain (sem_step_src hj e.2) one
      (sem_step_src hj (!e.2)) (sem_src_ne h.1 hj e.2).symm
  have extended : sem_Chain 14 D (14+f.1) (14+e.1) :=
    Relation.ReflTransGen.tail chain ⟨sem_step_src hj e.2,one⟩
  obtain ⟨u,v,huv,hxu,hxv,_,_⟩ := sem_hw_two_nbrs x x
  have edge := (hc_adjB_iff x u).mp hxu
  have outEmpty : supp 14 D (outW 14 D) = ∅ := heawood_supp_out hD
  have baseFalse : val D (single u) (outW 14 D) = false := by
    cases value : val D (single u) (outW 14 D) with
    | false => rfl
    | true =>
      have member := mem_supp.mpr value
      rw [outEmpty] at member
      exact False.elim (Finset.notMem_empty u member)
  have positive : val D (sem_ins x (single u)) (outW 14 D) = true := by
    apply (sem_heawood_comp hD _).mpr
    refine ⟨x,u,edge,sem_ins_self _ _,sem_ins_ge _ _ u ?_⟩
    simp [single]
  have survives := consumer_barrier_true h.1 x u e he empty f.1 (14+e.1) two
    extended (outW 14 D) (by unfold outW; omega)
    (by rw [outEmpty]; simp) baseFalse positive
  rw [sem_val_gate_src h.1 _ hj e.2,hand,gop_true,Bool.and_eq_true] at survives
  have agrees := two_consumers_offroute_agreement h.1 x u e he empty f.1
    (src D (sem_bar e)) two offroute (by rw [empty]; simp)
  have member : u ∈ supp 14 D (src D (sem_bar e)) :=
    mem_supp.mpr (agrees.trans survives.2)
  rw [empty] at member
  exact Finset.notMem_empty u member

end PEqualNP.Outside.L_meta_6659_aux
