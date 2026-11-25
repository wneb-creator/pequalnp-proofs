import Mathlib.Data.Finset.Card

namespace PEqualNP.Outside.L_meta_4970

lemma star_centre_unique {p l : ℕ} {E : Finset (Fin p × Fin l)}
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {a a' : Fin p} {Q : Finset (Fin l)} (hQ : 2 ≤ Q.card)
    (ha : ∀ b ∈ Q, (a, b) ∈ E) (ha' : ∀ b ∈ Q, (a', b) ∈ E) : a = a' := by
  by_contra hne
  obtain ⟨b, hb, b', hb', hbb'⟩ := Finset.one_lt_card.mp
    (lt_of_lt_of_le (by decide : 1 < 2) hQ)
  exact hfour a a' b b' hne hbb' ⟨ha b hb, ha b' hb', ha' b hb, ha' b' hb'⟩

lemma reverse_star_centre_unique {p l : ℕ} {E : Finset (Fin p × Fin l)}
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {b b' : Fin l} {P : Finset (Fin p)} (hP : 2 ≤ P.card)
    (hb : ∀ a ∈ P, (a, b) ∈ E) (hb' : ∀ a ∈ P, (a, b') ∈ E) : b = b' := by
  by_contra hne
  obtain ⟨a, ha, a', ha', haa'⟩ := Finset.one_lt_card.mp
    (lt_of_lt_of_le (by decide : 1 < 2) hP)
  exact hfour a a' b b' haa' hne ⟨hb a ha, hb' a ha, hb a' ha', hb' a' ha'⟩

end PEqualNP.Outside.L_meta_4970
