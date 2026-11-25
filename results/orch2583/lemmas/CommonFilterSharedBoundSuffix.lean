namespace PEqualNP.Outside.L_meta_2583.CommonFilter

variable {α β : Type} [DecidableEq α] [DecidableEq β]

def transpose (E : Finset (α × β)) : Finset (β × α) :=
  E.map (Equiv.prodComm α β).toEmbedding

lemma mem_transpose (E : Finset (α × β)) (p : α) (l : β) :
    (l,p) ∈ transpose E ↔ (p,l) ∈ E := by simp [transpose]

lemma transpose_card (E : Finset (α × β)) : (transpose E).card = E.card := by
  simp [transpose]

lemma noFour_transpose (E : Finset (α × β)) (hfour : NoFour E) : NoFour (transpose E) := by
  intro l l' p p' hll hpp h
  exact hfour p p' l l' hpp hll
    ⟨(mem_transpose E p l).mp h.1,(mem_transpose E p l').mp h.2.2.1,
      (mem_transpose E p' l).mp h.2.1,(mem_transpose E p' l').mp h.2.2.2⟩

lemma transpose_rectangles (P1 P2 A : Finset α) (L1 L2 B : Finset β) :
    transpose (Rect P1 A L1 B ∪ Rect P2 A L2 B) =
      Rect L1 B P1 A ∪ Rect L2 B P2 A := by
  ext ⟨l,p⟩
  rw [mem_transpose]
  simp only [Rect,Finset.mem_filter,Finset.mem_product,Finset.mem_union]
  tauto

lemma prune_common_right (P1 P2 A : Finset α) (L1 L2 B : Finset β)
    (hl1 : L1.Nonempty) (hl2 : L2.Nonempty)
    (hfour : NoFour (Rect P1 A L1 B ∪ Rect P2 A L2 B)) :
    ∃ T : Finset β, T ⊆ L1 ∩ L2 ∧ T.card = (L1 ∩ L2).card - 1 ∧
      (L1 \ T).Nonempty ∧ (L2 \ T).Nonempty ∧
      (Rect P1 A L1 B ∪ Rect P2 A L2 B).card ≤
        (Rect P1 A (L1 \ T) B ∪ Rect P2 A (L2 \ T) B).card + T.card := by
  have ht : NoFour (Rect L1 B P1 A ∪ Rect L2 B P2 A) := by
    rw [← transpose_rectangles]
    exact noFour_transpose _ hfour
  obtain ⟨T,ht,hcard,h1,h2,hcost⟩ := prune_common_left L1 L2 B P1 P2 A hl1 hl2 ht
  refine ⟨T,ht,hcard,h1,h2,?_⟩
  rw [← transpose_rectangles P1 P2 A L1 L2 B,
    ← transpose_rectangles P1 P2 A (L1 \ T) (L2 \ T) B,transpose_card,transpose_card] at hcost
  exact hcost

lemma filter_right_core (P1 P2 A : Finset α) (L1 L2 B T : Finset β) :
    ((Rect P1 A L1 B ∪ Rect P2 A L2 B).filter fun e => e.2 ∉ T) =
      Rect P1 A (L1 \ T) B ∪ Rect P2 A (L2 \ T) B := by
  ext e
  simp only [Rect,Finset.mem_filter,Finset.mem_product,Finset.mem_union,Finset.mem_sdiff]
  tauto

lemma shared_edges (P1 P2 A : Finset α) (L1 L2 B : Finset β)
    (hp1 : P1.Nonempty) (hp2 : P2.Nonempty) (hl1 : L1.Nonempty) (hl2 : L2.Nonempty)
    (hfour : NoFour (Rect P1 A L1 B ∪ Rect P2 A L2 B)) :
    (Rect P1 A L1 B ∪ Rect P2 A L2 B).card + 2 +
      ((P1 ∩ P2).card - 1) + ((L1 ∩ L2).card - 1) ≤
      P1.card + L1.card + P2.card + L2.card := by
  obtain ⟨S,hs,hscard,hp1',hp2',hcost1⟩ := prune_common_left P1 P2 A L1 L2 B hp1 hp2 hfour
  have hfour' : NoFour (Rect (P1 \ S) A L1 B ∪ Rect (P2 \ S) A L2 B) := by
    apply noFour_subset _ hfour
    rw [← filter_left_core]
    exact Finset.filter_subset _ _
  obtain ⟨T,ht,htcard,hl1',hl2',hcost2⟩ :=
    prune_common_right (P1 \ S) (P2 \ S) A L1 L2 B hl1 hl2 hfour'
  have hfour'' : NoFour (Rect (P1 \ S) A (L1 \ T) B ∪ Rect (P2 \ S) A (L2 \ T) B) := by
    apply noFour_subset _ hfour'
    rw [← filter_right_core]
    exact Finset.filter_subset _ _
  have hcost := (common_filter_cover (P1 \ S) (P2 \ S) A (L1 \ T) (L2 \ T) B
    hp1' hp2' hl1' hl2' hfour'').2
  have hp1c := Finset.card_sdiff_add_card_eq_card (hs.trans Finset.inter_subset_left)
  have hp2c := Finset.card_sdiff_add_card_eq_card (hs.trans Finset.inter_subset_right)
  have hl1c := Finset.card_sdiff_add_card_eq_card (ht.trans Finset.inter_subset_left)
  have hl2c := Finset.card_sdiff_add_card_eq_card (ht.trans Finset.inter_subset_right)
  omega

lemma shared_cover (P1 P2 A : Finset α) (L1 L2 B : Finset β)
    (hp1 : P1.Nonempty) (hp2 : P2.Nonempty) (hl1 : L1.Nonempty) (hl2 : L2.Nonempty)
    (hfour : NoFour (Rect P1 A L1 B ∪ Rect P2 A L2 B)) :
    (∀ p l, (p,l) ∈ Rect P1 A L1 B ∪ Rect P2 A L2 B → p ∈ A ∨ l ∈ B) ∧
    (Rect P1 A L1 B ∪ Rect P2 A L2 B).card + A.card + B.card + 2 +
      ((P1 ∩ P2).card - 1) + ((L1 ∩ L2).card - 1) ≤
      P1.card + L1.card + P2.card + L2.card + A.card + B.card := by
  refine ⟨(common_filter_cover P1 P2 A L1 L2 B hp1 hp2 hl1 hl2 hfour).1,?_⟩
  have := shared_edges P1 P2 A L1 L2 B hp1 hp2 hl1 hl2 hfour
  omega

end PEqualNP.Outside.L_meta_2583.CommonFilter
