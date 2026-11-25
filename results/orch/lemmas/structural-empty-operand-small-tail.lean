namespace PEqualNP.Outside.L_meta_6659_aux

lemma empty_opposite_no_common_neighbor {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (two : ∀ x, (sem_W 14 D x).card ≤ 2) (e : ℕ × Bool)
    (valid : e.1 < D.length) (outEmpty : supp 14 D (14+e.1) = ∅)
    (oppositeEmpty : supp 14 D (src D (sem_bar e)) = ∅)
    {x a y : Fin 14} (hx : x ∈ supp 14 D (src D e))
    (ha : a ∈ supp 14 D (src D e)) (hxa : x ≠ a)
    (hxy : Adj x y) (hay : Adj a y) : False := by
  classical
  obtain ⟨f,hfe,hxcode,hxn⟩ := empty_opposite_other_exit h hD two e valid
    outEmpty oppositeEmpty hx
  obtain ⟨g,hge,hacode,han⟩ := empty_opposite_other_exit h hD two e valid
    outEmpty oppositeEmpty ha
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

lemma empty_opposite_support_card {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (two : ∀ x, (sem_W 14 D x).card ≤ 2) (e : ℕ × Bool)
    (valid : e.1 < D.length) (outEmpty : supp 14 D (14+e.1) = ∅)
    (oppositeEmpty : supp 14 D (src D (sem_bar e)) = ∅) :
    (supp 14 D (src D e)).card ≤ 2 := by
  classical
  have geometry : ∀ x a : Fin 14, x ≠ a →
      decide (x.val < 7) = decide (a.val < 7) → ∃ y : Fin 14, Adj x y ∧ Adj a y := by
    simp only [← hc_adjB_iff]
    decide +kernel
  have injective : Set.InjOn (fun x : Fin 14 => decide (x.val < 7))
      (supp 14 D (src D e)) := by
    intro x hx a ha same
    by_contra distinct
    obtain ⟨y,hxy,hay⟩ := geometry x a distinct same
    exact empty_opposite_no_common_neighbor h hD two e valid outEmpty oppositeEmpty
      hx ha distinct hxy hay
  calc
    (supp 14 D (src D e)).card =
        ((supp 14 D (src D e)).image (fun x : Fin 14 => decide (x.val < 7))).card :=
      (Finset.card_image_of_injOn injective).symm
    _ ≤ (Finset.univ : Finset Bool).card := Finset.card_le_card (Finset.subset_univ _)
    _ = 2 := rfl

end PEqualNP.Outside.L_meta_6659_aux
