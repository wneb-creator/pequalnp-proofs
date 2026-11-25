import Mathlib

namespace PEqualNP.Outside.L_meta_4675.ReaderCharge

lemma nonstar_reader_shape {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A Q : Finset (Fin p)) (B P : Finset (Fin l))
    (hQ : 1 < Q.card) (hB : 1 < B.card)
    (hAQ : (A ∩ Q).Nonempty) (hP : P.Nonempty)
    (hbase : ∀ q ∈ Q, ∀ b ∈ P, (q, b) ∈ E)
    (hprod : ∀ a ∈ A, ∀ b ∈ B, ∀ q ∈ Q, (a, b) ∈ E ∨ (q, b) ∈ E)
    (hdirty : ∃ a ∈ A, ∃ b ∈ B, (a, b) ∉ E) :
    ∃ (b0 b1 : Fin l) (q0 : Fin p),
      b0 ≠ b1 ∧ P = {b0} ∧ B = {b0, b1} ∧ A ∩ Q = {q0} ∧
      (∀ a ∈ A, (a, b1) ∈ E) ∧ (∀ q ∈ Q, (q, b0) ∈ E) ∧
      (∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E ↔ b = b1 ∨ a = q0 ∧ b = b0) := by
  obtain ⟨a0, ha0, b0, hb0, hbad⟩ := hdirty
  obtain ⟨q0, hq0⟩ := hAQ
  obtain ⟨hq0A, hq0Q⟩ := Finset.mem_inter.mp hq0
  obtain ⟨q, hq, r, hr, hqr⟩ := Finset.one_lt_card.mp hQ
  have hQ0 : ∀ z ∈ Q, (z, b0) ∈ E := by
    intro z hz
    exact (hprod a0 ha0 b0 hb0 z hz).resolve_left hbad
  have hP0 : P = {b0} := by
    apply Finset.eq_singleton_iff_nonempty_unique_mem.mpr
    refine ⟨hP, ?_⟩
    intro b hb
    by_contra hbb
    exact hC4 q r b b0 hqr hbb
      ⟨hbase q hq b hb, hQ0 q hq, hbase r hr b hb, hQ0 r hr⟩
  have hother : ∀ b ∈ B, b ≠ b0 → ∀ a ∈ A, (a, b) ∈ E := by
    intro b hb hbb a ha
    by_contra hab
    have hqb := (hprod a ha b hb q hq).resolve_left hab
    have hrb := (hprod a ha b hb r hr).resolve_left hab
    exact hC4 q r b b0 hqr hbb ⟨hqb, hQ0 q hq, hrb, hQ0 r hr⟩
  have ha0q : a0 ≠ q0 := by
    intro he
    subst a0
    exact hbad (hQ0 q0 hq0Q)
  obtain ⟨b1, hb1, hb10⟩ : ∃ b1 ∈ B, b1 ≠ b0 := by
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hB
    by_cases hu0 : u = b0
    · exact ⟨v, hv, fun hv0 => huv (hu0.trans hv0.symm)⟩
    · exact ⟨u, hu, hu0⟩
  have hB01 : B = {b0, b1} := by
    apply Finset.Subset.antisymm
    · intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hb00 : b = b0
      · exact Or.inl hb00
      · right
        by_contra hb11
        exact hC4 a0 q0 b b1 ha0q hb11
          ⟨hother b hb hb00 a0 ha0, hother b1 hb1 hb10 a0 ha0,
            hother b hb hb00 q0 hq0A, hother b1 hb1 hb10 q0 hq0A⟩
    · exact Finset.insert_subset hb0 (Finset.singleton_subset_iff.mpr hb1)
  have hAQ0 : A ∩ Q = {q0} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨Finset.mem_inter.mpr ⟨hq0A, hq0Q⟩, ?_⟩
    intro a ha
    obtain ⟨haA, haQ⟩ := Finset.mem_inter.mp ha
    by_contra haq
    exact hC4 a q0 b0 b1 haq hb10.symm
      ⟨hQ0 a haQ, hother b1 hb1 hb10 a haA,
        hQ0 q0 hq0Q, hother b1 hb1 hb10 q0 hq0A⟩
  refine ⟨b0, b1, q0, hb10.symm, hP0, hB01, hAQ0,
    hother b1 hb1 hb10, hQ0, ?_⟩
  intro a ha b hb
  constructor
  · intro hab
    have hbb : b = b0 ∨ b = b1 := by simpa [hB01] using hb
    rcases hbb with hb0eq | hb1eq
    · right
      refine ⟨?_, hb0eq⟩
      rw [hb0eq] at hab
      by_contra haq
      exact hC4 a q0 b0 b1 haq hb10.symm
        ⟨hab, hother b1 hb1 hb10 a ha,
          hQ0 q0 hq0Q, hother b1 hb1 hb10 q0 hq0A⟩
    · exact Or.inl hb1eq
  · rintro (hb1eq | ⟨haq, hb0eq⟩)
    · rw [hb1eq]
      exact hother b1 hb1 hb10 a ha
    · rw [haq, hb0eq]
      exact hQ0 q0 hq0Q

end PEqualNP.Outside.L_meta_4675.ReaderCharge
