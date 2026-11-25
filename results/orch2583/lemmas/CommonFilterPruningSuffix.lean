namespace PEqualNP.Outside.L_meta_2583.CommonFilter

variable {α β : Type} [DecidableEq α] [DecidableEq β]

lemma delete_left_count (E : Finset (α × β)) (S : Finset α)
    (hdeg : ∀ p ∈ S, (neighbors E p).card ≤ 1) :
    E.card ≤ (E.filter fun e => e.1 ∉ S).card + S.card := by
  have hremoved : (E.filter fun e => e.1 ∈ S).card ≤ S.card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro e he
      exact (Finset.mem_filter.mp he).2
    · intro e he f hf heq
      rcases e with ⟨p,l⟩
      rcases f with ⟨p',l'⟩
      dsimp at heq
      subst p'
      have hp : p ∈ S := (Finset.mem_filter.mp he).2
      have hl : l ∈ neighbors E p := (mem_neighbors E p l).mpr (Finset.mem_filter.mp he).1
      have hl' : l' ∈ neighbors E p := (mem_neighbors E p l').mpr (Finset.mem_filter.mp hf).1
      have he : l = l' := Finset.card_le_one.mp (hdeg p hp) l hl l' hl'
      rw [he]
  have hsub : E ⊆ (E.filter fun e => e.1 ∉ S) ∪ (E.filter fun e => e.1 ∈ S) := by
    intro e he
    by_cases hp : e.1 ∈ S <;> simp [he,hp]
  have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  omega

lemma filter_left_core (P1 P2 A S : Finset α) (L1 L2 B : Finset β) :
    ((Rect P1 A L1 B ∪ Rect P2 A L2 B).filter fun e => e.1 ∉ S) =
      Rect (P1 \ S) A L1 B ∪ Rect (P2 \ S) A L2 B := by
  ext e
  simp only [Rect,Finset.mem_filter,Finset.mem_product,Finset.mem_union,Finset.mem_sdiff]
  tauto

lemma prune_common_left (P1 P2 A : Finset α) (L1 L2 B : Finset β)
    (hp1 : P1.Nonempty) (hp2 : P2.Nonempty)
    (hfour : NoFour (Rect P1 A L1 B ∪ Rect P2 A L2 B)) :
    ∃ S : Finset α, S ⊆ P1 ∩ P2 ∧ S.card = (P1 ∩ P2).card - 1 ∧
      (P1 \ S).Nonempty ∧ (P2 \ S).Nonempty ∧
      (Rect P1 A L1 B ∪ Rect P2 A L2 B).card ≤
        (Rect (P1 \ S) A L1 B ∪ Rect (P2 \ S) A L2 B).card + S.card := by
  by_cases hi : (P1 ∩ P2).Nonempty
  · obtain ⟨p0,hp0,hothers⟩ : ∃ p0 ∈ P1 ∩ P2,
        ∀ p ∈ P1 ∩ P2, p ≠ p0 →
          (neighbors (Rect P1 A L1 B ∪ Rect P2 A L2 B) p).card ≤ 1 := by
      by_cases hh : ∃ p ∈ P1 ∩ P2,
          1 < (neighbors (Rect P1 A L1 B ∪ Rect P2 A L2 B) p).card
      · obtain ⟨p0,hp0,hdeg0⟩ := hh
        refine ⟨p0,hp0,?_⟩
        intro p hp hne
        by_contra! hdeg
        exact hne (common_heavy_unique P1 P2 A L1 L2 B hfour p p0
          (Finset.mem_inter.mp hp).1 (Finset.mem_inter.mp hp).2
          (Finset.mem_inter.mp hp0).1 (Finset.mem_inter.mp hp0).2 hdeg hdeg0)
      · obtain ⟨p0,hp0⟩ := hi
        refine ⟨p0,hp0,?_⟩
        intro p hp _
        by_contra! hdeg
        exact hh ⟨p,hp,hdeg⟩
    let S := (P1 ∩ P2).erase p0
    refine ⟨S,Finset.erase_subset _ _,?_,?_,?_,?_⟩
    · exact Finset.card_erase_of_mem hp0
    · exact ⟨p0,Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hp0).1,by simp [S]⟩⟩
    · exact ⟨p0,Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hp0).2,by simp [S]⟩⟩
    · have hd : ∀ p ∈ S,
          (neighbors (Rect P1 A L1 B ∪ Rect P2 A L2 B) p).card ≤ 1 := by
        intro p hp
        exact hothers p (Finset.mem_erase.mp hp).2 (Finset.mem_erase.mp hp).1
      have hc := delete_left_count (Rect P1 A L1 B ∪ Rect P2 A L2 B) S hd
      rw [filter_left_core] at hc
      exact hc
  · have he : P1 ∩ P2 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hi
    refine ⟨∅,by simp,by simp [he],?_,?_,?_⟩
    · simpa using hp1
    · simpa using hp2
    · simp

end PEqualNP.Outside.L_meta_2583.CommonFilter
