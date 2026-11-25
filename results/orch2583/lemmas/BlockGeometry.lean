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

namespace PEqualNP.Outside.L_meta_2583_aux.BlockGeometry

lemma added_clause_orientation {N : ℕ}
    (Ap Al Bp Bl Cp Cl Dp Dl : Finset (Fin N))
    (hc : Cp.Nonempty ∨ Cl.Nonempty) (hd : Dp.Nonempty ∨ Dl.Nonempty)
    (point_false : ¬ (((Ap.Nonempty ∧ Bp.Nonempty) ∨ Cp.Nonempty) ∧ Dp.Nonempty))
    (line_false : ¬ (((Al.Nonempty ∧ Bl.Nonempty) ∨ Cl.Nonempty) ∧ Dl.Nonempty)) :
    (Cp.Nonempty ∧ Cl = ∅ ∧ Dp = ∅ ∧ Dl.Nonempty ∧ (Al = ∅ ∨ Bl = ∅)) ∨
    (Cl.Nonempty ∧ Cp = ∅ ∧ Dl = ∅ ∧ Dp.Nonempty ∧ (Ap = ∅ ∨ Bp = ∅)) := by
  classical
  simp only [Finset.nonempty_iff_ne_empty] at *
  tauto

lemma rectangle_small_side {N : ℕ} (I : Fin N → Fin N → Prop)
    (noC4 : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (A B : Finset (Fin N)) (inside : ∀ p ∈ A, ∀ l ∈ B, I p l) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_cases ha : A.card ≤ 1
  · exact Or.inl ha
  right
  obtain ⟨p,hp,p',hp',hpp⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
  rw [Finset.card_le_one]
  intro l hl l' hl'
  by_contra hll
  exact noC4 p p' l l' hpp hll
    ⟨inside p hp l hl, inside p hp l' hl', inside p' hp' l hl, inside p' hp' l' hl'⟩

lemma one_junk_large_side_intersections {N : ℕ} (I : Fin N → Fin N → Prop)
    (noC4 : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (A Bp C Bl D : Finset (Fin N)) (ha : 2 ≤ A.card) (hd : 2 ≤ D.card)
    (inside : ∀ e ∈ ((C ∪ (A ∩ Bp)) ×ˢ D) ∪ (A ×ˢ (D ∩ Bl)), I e.1 e.2) :
    (C ∪ (A ∩ Bp)).card ≤ 1 ∧ (D ∩ Bl).card ≤ 1 := by
  have h1 := rectangle_small_side I noC4 (C ∪ (A ∩ Bp)) D (by
    intro p hp l hl
    exact inside (p,l) (Finset.mem_union_left _ (Finset.mem_product.mpr ⟨hp,hl⟩)))
  have h2 := rectangle_small_side I noC4 A (D ∩ Bl) (by
    intro p hp l hl
    exact inside (p,l) (Finset.mem_union_right _ (Finset.mem_product.mpr ⟨hp,hl⟩)))
  omega

lemma one_junk_shared_support_small {N : ℕ} (I : Fin N → Fin N → Prop)
    (noC4 : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (A Bp C Bl D : Finset (Fin N)) (ha : 2 ≤ A.card) (hd : 2 ≤ D.card)
    (inside : ∀ e ∈ ((C ∪ (A ∩ Bp)) ×ˢ D) ∪ (A ×ˢ (D ∩ Bl)), I e.1 e.2) :
    C.card ≤ 1 ∧
    (∀ K : Finset (Fin N), K ⊆ A → K ⊆ Bp → K.card ≤ 1) ∧
    (∀ K : Finset (Fin N), K ⊆ D → K ⊆ Bl → K.card ≤ 1) := by
  obtain ⟨h1,h2⟩ := one_junk_large_side_intersections I noC4 A Bp C Bl D ha hd inside
  refine ⟨(Finset.card_le_card Finset.subset_union_left).trans h1, ?_, ?_⟩
  · intro K hka hkb
    apply (Finset.card_le_card (s := K) (t := C ∪ (A ∩ Bp)) ?_).trans h1
    intro p hp
    exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hka hp,hkb hp⟩)
  · intro K hkd hkb
    apply (Finset.card_le_card (s := K) (t := D ∩ Bl) ?_).trans h2
    intro l hl
    exact Finset.mem_inter.mpr ⟨hkd hl,hkb hl⟩

end PEqualNP.Outside.L_meta_2583_aux.BlockGeometry
