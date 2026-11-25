import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675_aux

lemma member_ne_of_card_two {α : Type*} [DecidableEq α]
    (S : Finset α) (hS : 2 ≤ S.card) (a : α) : ∃ b ∈ S, b ≠ a := by
  classical
  by_contra h
  have heq : ∀ b ∈ S, b = a := by
    intro b hb
    by_contra hba
    exact h ⟨b, hb, hba⟩
  have hcard : S.card ≤ 1 := Finset.card_le_one.mpr (by
    intro b hb c hc
    exact (heq b hb).trans (heq c hc).symm)
  omega

lemma reader_novel_column {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A Q : Finset (Fin p)) (B P : Finset (Fin l))
    (hQ : 2 ≤ Q.card) (hP : P.Nonempty)
    (hrow : ∀ a ∈ A, a ∈ Q → ∀ b ∈ B, (a, b) ∈ E)
    (hbase : ∀ q ∈ Q, ∀ t ∈ P, (q, t) ∈ E)
    (htriple : ∀ a ∈ A, ∀ b ∈ B, ∀ q ∈ Q, (a, b) ∈ E ∨ (q, b) ∈ E)
    (a : Fin p) (ha : a ∈ A) (haQ : a ∈ Q)
    (b : Fin l) (hb : b ∈ B) (hbP : b ∉ P) :
    ∀ a' ∈ A, (a', b) ∈ E := by
  obtain ⟨t, ht⟩ := hP
  obtain ⟨q, hq, hqa⟩ := member_ne_of_card_two Q hQ a
  have htb : t ≠ b := by
    intro h
    exact hbP (h ▸ ht)
  have hqb : (q, b) ∉ E := by
    intro h
    exact hfour a q t b hqa.symm htb
      ⟨hbase a haQ t ht, hrow a ha haQ b hb, hbase q hq t ht, h⟩
  intro a' ha'
  exact (htriple a' ha' b hb q hq).resolve_right hqb

lemma reader_novel_at_most_one {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A Q : Finset (Fin p)) (B P : Finset (Fin l))
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) (hQ : 2 ≤ Q.card) (hP : P.Nonempty)
    (hrow : ∀ a ∈ A, a ∈ Q → ∀ b ∈ B, (a, b) ∈ E)
    (hbase : ∀ q ∈ Q, ∀ t ∈ P, (q, t) ∈ E)
    (htriple : ∀ a ∈ A, ∀ b ∈ B, ∀ q ∈ Q, (a, b) ∈ E ∨ (q, b) ∈ E) :
    ((A ∩ Q) ×ˢ (B \ P)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro x hx y hy
  simp only [Finset.mem_product, Finset.mem_inter, Finset.mem_sdiff] at hx hy
  have hxcol := reader_novel_column E hfour A Q B P hQ hP hrow hbase htriple
    x.1 hx.1.1 hx.1.2 x.2 hx.2.1 hx.2.2
  have hycol := reader_novel_column E hfour A Q B P hQ hP hrow hbase htriple
    y.1 hy.1.1 hy.1.2 y.2 hy.2.1 hy.2.2
  obtain ⟨b, hb, hbx⟩ := member_ne_of_card_two B hB x.2
  have hxy : x.1 = y.1 := by
    by_contra h
    exact hfour x.1 y.1 x.2 b h hbx.symm
      ⟨hrow x.1 hx.1.1 hx.1.2 x.2 hx.2.1, hrow x.1 hx.1.1 hx.1.2 b hb,
       hrow y.1 hy.1.1 hy.1.2 x.2 hx.2.1, hrow y.1 hy.1.1 hy.1.2 b hb⟩
  obtain ⟨a, ha, hax⟩ := member_ne_of_card_two A hA x.1
  have hxy' : x.2 = y.2 := by
    by_contra h
    exact hfour x.1 a x.2 y.2 hax.symm h
      ⟨hxcol x.1 hx.1.1, hycol x.1 hx.1.1, hxcol a ha, hycol a ha⟩
  exact Prod.ext hxy hxy'

def rectangleCorners {p l : ℕ} (E : Finset (Fin p × Fin l))
    (A : Finset (Fin p)) (B : Finset (Fin l)) : Finset (Fin p × Fin l) :=
  (A.filter fun a => ∀ b ∈ B, (a, b) ∈ E) ×ˢ
    (B.filter fun b => ∀ a ∈ A, (a, b) ∈ E)

lemma rectangle_corners_at_most_one {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Finset (Fin p)) (B : Finset (Fin l))
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) :
    (rectangleCorners E A B).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  simp only [rectangleCorners, Finset.mem_product, Finset.mem_filter] at hx hy
  obtain ⟨b, hb, hbx⟩ := member_ne_of_card_two B hB x.2
  have hxy : x.1 = y.1 := by
    by_contra h
    exact hfour x.1 y.1 x.2 b h hbx.symm
      ⟨hx.1.2 x.2 hx.2.1, hx.1.2 b hb, hy.1.2 x.2 hx.2.1, hy.1.2 b hb⟩
  obtain ⟨a, ha, hax⟩ := member_ne_of_card_two A hA x.1
  have hxy' : x.2 = y.2 := by
    by_contra h
    exact hfour x.1 a x.2 y.2 hax.symm h
      ⟨hx.2.2 x.1 hx.1.1, hy.2.2 x.1 hx.1.1, hx.2.2 a ha, hy.2.2 a ha⟩
  exact Prod.ext hxy hxy'

lemma reader_novel_subset_corners {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A Q : Finset (Fin p)) (B P : Finset (Fin l))
    (hQ : 2 ≤ Q.card) (hP : P.Nonempty)
    (hrow : ∀ a ∈ A, a ∈ Q → ∀ b ∈ B, (a, b) ∈ E)
    (hbase : ∀ q ∈ Q, ∀ t ∈ P, (q, t) ∈ E)
    (htriple : ∀ a ∈ A, ∀ b ∈ B, ∀ q ∈ Q, (a, b) ∈ E ∨ (q, b) ∈ E) :
    (A ∩ Q) ×ˢ (B \ P) ⊆ rectangleCorners E A B := by
  intro x hx
  simp only [Finset.mem_product, Finset.mem_inter, Finset.mem_sdiff] at hx
  simp only [rectangleCorners, Finset.mem_product, Finset.mem_filter]
  exact ⟨⟨hx.1.1, hrow x.1 hx.1.1 hx.1.2⟩,
    hx.2.1, reader_novel_column E hfour A Q B P hQ hP hrow hbase htriple
      x.1 hx.1.1 hx.1.2 x.2 hx.2.1 hx.2.2⟩

lemma readers_share_at_most_one_novel_edge {p l : ℕ} {ι : Type*}
    [DecidableEq ι] (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Finset (Fin p)) (B : Finset (Fin l))
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card)
    (I : Finset ι) (Q : ι → Finset (Fin p)) (P : ι → Finset (Fin l))
    (hQ : ∀ i ∈ I, 2 ≤ (Q i).card) (hP : ∀ i ∈ I, (P i).Nonempty)
    (hrow : ∀ i ∈ I, ∀ a ∈ A, a ∈ Q i → ∀ b ∈ B, (a, b) ∈ E)
    (hbase : ∀ i ∈ I, ∀ q ∈ Q i, ∀ t ∈ P i, (q, t) ∈ E)
    (htriple : ∀ i ∈ I, ∀ a ∈ A, ∀ b ∈ B, ∀ q ∈ Q i,
      (a, b) ∈ E ∨ (q, b) ∈ E) :
    (I.biUnion fun i => (A ∩ Q i) ×ˢ (B \ P i)).card ≤ 1 := by
  apply le_trans (Finset.card_le_card ?_) (rectangle_corners_at_most_one E hfour A B hA hB)
  intro x hx
  obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
  exact reader_novel_subset_corners E hfour A (Q i) B (P i) (hQ i hi) (hP i hi)
    (hrow i hi) (hbase i hi) (htriple i hi) hxi

end PEqualNP.Outside.L_meta_4675_aux
