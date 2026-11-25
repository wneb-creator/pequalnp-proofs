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
