namespace PEqualNP.Outside.L_meta_6659_aux

lemma unproductive_other_exit {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (two : ∀ x, (sem_W 14 D x).card ≤ 2) (e : ℕ × Bool)
    (valid : e.1 < D.length) (outEmpty : supp 14 D (14+e.1) = ∅)
    {x : Fin 14} (unproductive : ∀ y, Adj x y → y ∉ supp 14 D (src D (sem_bar e)))
    (member : x ∈ supp 14 D (src D e)) :
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
    rw [equal] at bad
    exact unproductive _ (matching_adj.2 x).1 bad
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
    exact (unproductive y hxy bad).elim
  · exact hqy

lemma unproductive_no_common_neighbor {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (two : ∀ x, (sem_W 14 D x).card ≤ 2) (e : ℕ × Bool)
    (valid : e.1 < D.length) (outEmpty : supp 14 D (14+e.1) = ∅)
    {x a y : Fin 14} (hx : x ∈ supp 14 D (src D e))
    (ha : a ∈ supp 14 D (src D e)) (hxa : x ≠ a)
    (hxy : Adj x y) (hay : Adj a y)
    (noX : ∀ z, Adj x z → z ∉ supp 14 D (src D (sem_bar e)))
    (noA : ∀ z, Adj a z → z ∉ supp 14 D (src D (sem_bar e))) : False := by
  classical
  obtain ⟨f,hfe,hxcode,hxn⟩ := unproductive_other_exit h hD two e valid
    outEmpty noX hx
  obtain ⟨g,hge,hacode,han⟩ := unproductive_other_exit h hD two e valid
    outEmpty noA ha
  have hfg : f ≠ g := by
    intro equal
    obtain ⟨q,hq,hqa⟩ := sem_antichain sem_heawood_gr h.1 (sem_heawood_comp hD) hxa
    rw [hxcode,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact hqa ha
    · apply hqa
      have member : g ∈ sem_W 14 D a := by rw [hacode]; simp
      simpa only [equal] using (sem_mem_W.mp member).2.1
  have hbar : sem_bar f ≠ sem_bar g := by
    intro equal
    apply hfg
    have := congrArg sem_bar equal
    simpa only [sem_bar_bar] using this
  have ycode : sem_W 14 D y = {sem_bar f,sem_bar g} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro q hq
      simp only [Finset.mem_insert,Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact hxn y hxy
      · exact han y hay
    · rw [Finset.card_pair hbar]
      exact two y
  have geometry : ∀ x a y : Fin 14, x ≠ a → Adj x y → Adj a y →
      ∃ r s : Fin 14, r ≠ y ∧ s ≠ y ∧ Adj x r ∧ Adj a s ∧ ¬ Adj r s := by
    simp only [← hc_adjB_iff]
    decide +kernel
  obtain ⟨r,s,hry,hsy,hxr,has,hrs⟩ := geometry x a y hxa hxy hay
  obtain ⟨q,hq,hqr,hqs⟩ := sem_hw_cover_free h hD (Ne.symm hry) (Ne.symm hsy) hrs
  rw [ycode,Finset.mem_insert,Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · exact hqr (sem_mem_W.mp (hxn r hxr)).2.1
  · exact hqs (sem_mem_W.mp (han s has)).2.1

lemma shared_same_side_productive {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (two : ∀ x, (sem_W 14 D x).card ≤ 2) (e : ℕ × Bool)
    (valid : e.1 < D.length) (outEmpty : supp 14 D (14+e.1) = ∅)
    {x a : Fin 14} (hx : x ∈ supp 14 D (src D e))
    (ha : a ∈ supp 14 D (src D e)) (distinct : x ≠ a)
    (sameSide : decide (x.val < 7) = decide (a.val < 7)) :
    ∃ y : Fin 14, (Adj x y ∨ Adj a y) ∧ y ∈ supp 14 D (src D (sem_bar e)) := by
  classical
  by_contra missing
  have noX : ∀ y, Adj x y → y ∉ supp 14 D (src D (sem_bar e)) := by
    intro y hxy member
    exact missing ⟨y,Or.inl hxy,member⟩
  have noA : ∀ y, Adj a y → y ∉ supp 14 D (src D (sem_bar e)) := by
    intro y hay member
    exact missing ⟨y,Or.inr hay,member⟩
  have geometry : ∀ x a : Fin 14, x ≠ a →
      decide (x.val < 7) = decide (a.val < 7) → ∃ y : Fin 14, Adj x y ∧ Adj a y := by
    simp only [← hc_adjB_iff]
    decide +kernel
  obtain ⟨y,hxy,hay⟩ := geometry x a distinct sameSide
  exact unproductive_no_common_neighbor h hD two e valid outEmpty hx ha distinct hxy hay noX noA

end PEqualNP.Outside.L_meta_6659_aux
