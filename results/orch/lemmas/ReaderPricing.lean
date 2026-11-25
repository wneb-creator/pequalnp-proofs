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

end PEqualNP.Outside.L_meta_4675_aux
