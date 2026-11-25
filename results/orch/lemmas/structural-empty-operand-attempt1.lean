import PNPAccepted6659

namespace PEqualNP.Outside.L_meta_6659_aux

lemma empty_opposite_other_exit {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (two : ∀ x, (sem_W 14 D x).card ≤ 2) (e : ℕ × Bool)
    (valid : e.1 < D.length) (outEmpty : supp 14 D (14+e.1) = ∅)
    (oppositeEmpty : supp 14 D (src D (sem_bar e)) = ∅)
    {x : Fin 14} (member : x ∈ supp 14 D (src D e)) :
    ∃ f, f ≠ e ∧ sem_W 14 D x = {e,f} ∧
      ∀ y, Adj x y → sem_bar f ∈ sem_W 14 D y := by
  classical
  have he : e ∈ sem_W 14 D x := sem_mem_W.mpr
    ⟨valid,member,by rw [outEmpty]; simp⟩
  obtain ⟨f,hf,hother,_,_,_⟩ := sem_edge_slots sem_heawood_gr h.1
    (sem_heawood_comp hD) (matching_adj.2 x).1
  have different : f ≠ e := by
    intro equal
    have bad := (sem_mem_W.mp hother).2.1
    rw [equal,oppositeEmpty] at bad
    exact Finset.notMem_empty _ bad
  have code : sem_W 14 D x = {e,f} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro q hq
      simp only [Finset.mem_insert,Finset.mem_singleton] at hq
      rcases hq with rfl | rfl <;> assumption
    · rw [Finset.card_pair different.symm]
      exact two x
  refine ⟨f,different,code,?_⟩
  intro y hxy
  obtain ⟨q,hq,hqy,_,_,_⟩ := sem_edge_slots sem_heawood_gr h.1
    (sem_heawood_comp hD) hxy
  rw [code,Finset.mem_insert,Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · have bad := (sem_mem_W.mp hqy).2.1
    rw [oppositeEmpty] at bad
    exact (Finset.notMem_empty _ bad).elim
  · exact hqy

lemma empty_opposite_induced_degree {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (two : ∀ x, (sem_W 14 D x).card ≤ 2) (e : ℕ × Bool)
    (valid : e.1 < D.length) (outEmpty : supp 14 D (14+e.1) = ∅)
    (oppositeEmpty : supp 14 D (src D (sem_bar e)) = ∅)
    {x y z : Fin 14} (hx : x ∈ supp 14 D (src D e))
    (hy : y ∈ supp 14 D (src D e)) (hz : z ∈ supp 14 D (src D e))
    (hxy : Adj x y) (hxz : Adj x z) : y = z := by
  classical
  obtain ⟨f,hfe,hxcode,hneighbors⟩ := empty_opposite_other_exit h hD two e valid
    outEmpty oppositeEmpty hx
  have he_y : e ∈ sem_W 14 D y := sem_mem_W.mpr
    ⟨valid,hy,by rw [outEmpty]; simp⟩
  have he_z : e ∈ sem_W 14 D z := sem_mem_W.mpr
    ⟨valid,hz,by rw [outEmpty]; simp⟩
  have bar_ne : sem_bar f ≠ e := by
    intro equal
    have bad := (sem_mem_W.mp (hneighbors y hxy)).2.1
    have fx := (sem_mem_W.mp (by rw [hxcode]; simp : f ∈ sem_W 14 D x)).2.1
    have fe : f = sem_bar e := by rw [← equal,sem_bar_bar]
    rw [fe,oppositeEmpty] at fx
    exact Finset.notMem_empty _ fx
  have ycode : sem_W 14 D y = {e,sem_bar f} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro q hq
      simp only [Finset.mem_insert,Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact he_y
      · exact hneighbors y hxy
    · rw [Finset.card_pair bar_ne.symm]
      exact two y
  by_contra distinct
  obtain ⟨q,hq,hqz⟩ := sem_antichain sem_heawood_gr h.1 (sem_heawood_comp hD) distinct
  rw [ycode,Finset.mem_insert,Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · exact hqz hz
  · exact hqz (sem_mem_W.mp (hneighbors z hxz)).2.1

lemma empty_opposite_edge_support {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (two : ∀ x, (sem_W 14 D x).card ≤ 2) (e : ℕ × Bool)
    (valid : e.1 < D.length) (outEmpty : supp 14 D (14+e.1) = ∅)
    (oppositeEmpty : supp 14 D (src D (sem_bar e)) = ∅)
    {x y : Fin 14} (hx : x ∈ supp 14 D (src D e))
    (hy : y ∈ supp 14 D (src D e)) (hxy : Adj x y) :
    supp 14 D (src D e) = {x,y} := by
  classical
  obtain ⟨f,hfe,hxcode,hxn⟩ := empty_opposite_other_exit h hD two e valid
    outEmpty oppositeEmpty hx
  obtain ⟨g,hge,hycode,hyn⟩ := empty_opposite_other_exit h hD two e valid
    outEmpty oppositeEmpty hy
  have gf : g = sem_bar f := by
    have member := hxn y hxy
    rw [hycode,Finset.mem_insert,Finset.mem_singleton] at member
    rcases member with bad | good
    · have fe : f = sem_bar e := by rw [← bad,sem_bar_bar]
      have fx := (sem_mem_W.mp (by rw [hxcode]; simp : f ∈ sem_W 14 D x)).2.1
      rw [fe,oppositeEmpty] at fx
      exact (Finset.notMem_empty _ fx).elim
    · exact good.symm
  obtain ⟨r,s,hrs,hyr,hys,hrx,hsx⟩ := sem_hw_two_nbrs y x
  have carried : ∀ v, Adj y v → v ∈ supp 14 D (src D f) := by
    intro v hv
    have member := (sem_mem_W.mp (hyn v hv)).2.1
    simpa only [gf,sem_bar_bar] using member
  apply Finset.Subset.antisymm
  · intro a ha
    by_cases hax : a = x
    · simp [hax]
    have adjacent : ∀ v, v ≠ x → Adj y v → Adj v a := by
      intro v hvx hyv
      by_contra hva
      obtain ⟨q,hq,hqa,hqv⟩ := sem_hw_cover_free h hD hax.symm hvx.symm
        (fun hav => hva (adj_symm hav))
      rw [hxcode,Finset.mem_insert,Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact hqa ha
      · exact hqv (carried v hyv)
    have hay : a = y := sem_hw_common r s a y hrs hyr hys
      ((hc_adjB_iff _ _).mpr (adj_symm (adjacent r hrx ((hc_adjB_iff _ _).mp hyr))))
      ((hc_adjB_iff _ _).mpr (adj_symm (adjacent s hsx ((hc_adjB_iff _ _).mp hys))))
    simp [hay]
  · intro a ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> assumption

end PEqualNP.Outside.L_meta_6659_aux
