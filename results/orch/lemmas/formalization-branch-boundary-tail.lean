namespace PEqualNP.Outside.L_meta_6659_aux

lemma branch_boundary_value {n : ℕ} {D : Dag} {G : Fin n → Fin n → Prop}
    (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    (budget : totalSurplus n D ≤ (eligSet n D).card)
    (a : Fin n → Bool) (negative : ¬ sem_Edge G a)
    (maximal : ∀ i : Fin n, a i = false → sem_Edge G (sem_ins i a)) :
    ∀ w, 2 ≤ fanout D w → ∀ i ∈ supp n D w, val D a w = a i := by
  classical
  obtain ⟨b,hb⟩ := sem_exists_minBranch hG hS hC
  have pure := sem_minBranch_pure hb
  have sub : reservedUnits n D b ⊆ units n D :=
    (reserved_subset hS b pure).trans (Finset.filter_subset _ _)
  have all : reservedUnits n D b = units n D :=
    Finset.eq_of_subset_of_card_le sub (by rw [card_units,card_reserved b pure]; exact budget)
  intro w hw i hi
  have unit : (⟨w,0⟩ : Σ _ : ℕ, ℕ) ∈ units n D := by
    rw [mem_units]
    change w ∈ inner n D ∧ 0+1 < fanout D w
    exact ⟨sb_mem_inner.mpr (lt_of_fanout_pos hS (by omega)),by omega⟩
  rw [← all] at unit
  obtain ⟨x,hx,he⟩ := Finset.mem_image.mp unit
  have same : b x = w := congrArg Sigma.fst he
  have suppx : supp n D w = {x} := by rw [← same]; exact (pure x hx).2
  have ix : i = x := by simpa only [suppx,Finset.mem_singleton] using hi
  subst i
  cases ha : a x with
  | false =>
    rw [← same]
    exact (sem_dom_split hS hC a x (b x) (sem_chain_dom hS (hb x hx).2.2.1)
      negative (maximal x ha)).1
  | true =>
    exact sem_val_of_supp hS hi ha

end PEqualNP.Outside.L_meta_6659_aux
