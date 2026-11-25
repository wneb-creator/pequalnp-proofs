import Mathlib

namespace PEqualNP.Outside.L_meta_4675.SharedSupport

lemma shared_support_card {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A Q : Finset (Fin p)) (P : Finset (Fin l)) (c : Fin p)
    (hc : c ∈ A) (hQ : Q.Nonempty) (hdis : Disjoint A Q)
    (hcarry : ∀ b ∈ P, (c, b) ∈ E)
    (hzero : ∀ q ∈ Q, ∀ b ∈ P, (q, b) ∈ E) : P.card ≤ 1 := by
  obtain ⟨q, hq⟩ := hQ
  have hcq : c ≠ q := by
    intro he
    subst q
    exact Finset.disjoint_left.mp hdis hc hq
  apply Finset.card_le_one.mpr
  intro b hb b' hb'
  by_contra hbb'
  exact hC4 c q b b' hcq hbb'
    ⟨hcarry b hb, hcarry b' hb', hzero q hq b hb, hzero q hq b' hb'⟩

lemma shared_support_alias {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A Q : Finset (Fin p)) (P : Finset (Fin l)) (c : Fin p)
    (hc : c ∈ A) (hQ : Q.Nonempty) (hdis : Disjoint A Q)
    (hcarry : ∀ b ∈ P, (c, b) ∈ E)
    (hzero : ∀ q ∈ Q, ∀ b ∈ P, (q, b) ∈ E) :
    P = ∅ ∨ ∃ b, P = {b} := by
  have hcard := shared_support_card E hC4 A Q P c hc hQ hdis hcarry hzero
  rcases P.eq_empty_or_nonempty with hP | ⟨b, hb⟩
  · exact Or.inl hP
  · exact Or.inr ⟨b, Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hb, fun b' hb' => Finset.card_le_one.mp hcard b' hb' b hb⟩⟩

lemma small_support_eval {l : ℕ} (P : Finset (Fin l)) (hP : P.card ≤ 1) :
    ∃ o : Option (Fin l), ∀ x : Fin l → Bool,
      decide (∃ b ∈ P, x b = true) = o.elim false x := by
  classical
  rcases P.eq_empty_or_nonempty with h | ⟨b, hb⟩
  · exact ⟨none, by simp [h]⟩
  · have he : P = {b} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hb, fun b' hb' => Finset.card_le_one.mp hP b' hb' b hb⟩
    exact ⟨some b, by simp [he]⟩

end PEqualNP.Outside.L_meta_4675.SharedSupport
