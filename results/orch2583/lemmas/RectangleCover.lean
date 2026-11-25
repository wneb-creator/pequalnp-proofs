import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.RectangleCover

lemma rectangle_cover {N : ℕ} (I : Fin N → Fin N → Prop)
    (noC4 : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (A B : Finset (Fin N)) (inside : ∀ p ∈ A, ∀ l ∈ B, I p l) :
    ∃ P L : Finset (Fin N),
      (∀ e ∈ A ×ˢ B, e.1 ∈ P ∨ e.2 ∈ L) ∧
      (A ×ˢ B).card + P.card + L.card ≤ A.card + B.card := by
  by_cases ha : A = ∅
  · subst A
    exact ⟨∅, ∅, by simp, by simp⟩
  by_cases hb : B = ∅
  · subst B
    exact ⟨∅, ∅, by simp, by simp⟩
  have hapos : 0 < A.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr ha)
  have hbpos : 0 < B.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hb)
  by_cases hsmall : A.card ≤ 1
  · have hac : A.card = 1 := by omega
    refine ⟨A, ∅, ?_, ?_⟩
    · intro e he
      exact Or.inl (Finset.mem_product.mp he).1
    · simp [Finset.card_product, hac]
  · obtain ⟨p, hp, p', hp', hpp⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
    have hbsmall : B.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro l hl l' hl'
      by_contra hll
      exact noC4 p p' l l' hpp hll
        ⟨inside p hp l hl, inside p hp l' hl', inside p' hp' l hl, inside p' hp' l' hl'⟩
    have hbc : B.card = 1 := by omega
    refine ⟨∅, B, ?_, ?_⟩
    · intro e he
      exact Or.inr (Finset.mem_product.mp he).2
    · simp [Finset.card_product, hbc]

lemma two_rectangles_cover {N : ℕ} (I : Fin N → Fin N → Prop)
    (noC4 : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (A B C D : Finset (Fin N))
    (inside : ∀ e ∈ (A ×ˢ B) ∪ (C ×ˢ D), I e.1 e.2) :
    ∃ P L : Finset (Fin N),
      (∀ e ∈ (A ×ˢ B) ∪ (C ×ˢ D), e.1 ∈ P ∨ e.2 ∈ L) ∧
      ((A ×ˢ B) ∪ (C ×ˢ D)).card + P.card + L.card ≤
        A.card + B.card + C.card + D.card := by
  obtain ⟨P1, L1, h1, cost1⟩ := rectangle_cover I noC4 A B (by
    intro p hp l hl
    exact inside (p,l) (Finset.mem_union_left _ (Finset.mem_product.mpr ⟨hp,hl⟩)))
  obtain ⟨P2, L2, h2, cost2⟩ := rectangle_cover I noC4 C D (by
    intro p hp l hl
    exact inside (p,l) (Finset.mem_union_right _ (Finset.mem_product.mpr ⟨hp,hl⟩)))
  refine ⟨P1 ∪ P2, L1 ∪ L2, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact (h1 e he).imp (Finset.mem_union_left _) (Finset.mem_union_left _)
    · exact (h2 e he).imp (Finset.mem_union_right _) (Finset.mem_union_right _)
  · have ecard := Finset.card_union_le (A ×ˢ B) (C ×ˢ D)
    have pcard := Finset.card_union_le P1 P2
    have lcard := Finset.card_union_le L1 L2
    omega

lemma one_junk_block_cover {N : ℕ} (I : Fin N → Fin N → Prop)
    (noC4 : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (A Bp C Bl D : Finset (Fin N))
    (inside : ∀ e ∈ ((C ∪ (A ∩ Bp)) ×ˢ D) ∪ (A ×ˢ (D ∩ Bl)), I e.1 e.2) :
    ∃ P L : Finset (Fin N),
      (∀ e ∈ ((C ∪ (A ∩ Bp)) ×ˢ D) ∪ (A ×ˢ (D ∩ Bl)), e.1 ∈ P ∨ e.2 ∈ L) ∧
      (((C ∪ (A ∩ Bp)) ×ˢ D) ∪ (A ×ˢ (D ∩ Bl))).card + P.card + L.card ≤
        A.card + Bp.card + Bl.card + C.card + D.card := by
  obtain ⟨P,L,hcover,hcost⟩ := two_rectangles_cover I noC4 (C ∪ (A ∩ Bp)) D A (D ∩ Bl) inside
  refine ⟨P,L,hcover,?_⟩
  have h1 := Finset.card_union_le C (A ∩ Bp)
  have h2 : (A ∩ Bp).card ≤ Bp.card := Finset.card_le_card Finset.inter_subset_right
  have h3 : (D ∩ Bl).card ≤ Bl.card := Finset.card_le_card Finset.inter_subset_right
  omega

end PEqualNP.Outside.L_meta_2583_aux.RectangleCover
