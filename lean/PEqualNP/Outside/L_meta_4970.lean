import Mathlib.Data.Finset.Card

namespace PEqualNP.Outside.L_meta_4970

lemma star_centre_unique {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hE : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {a a' : Fin p} {Q : Finset (Fin l)} (hQ : 2 ≤ Q.card)
    (ha : ∀ b ∈ Q, (a, b) ∈ E) (ha' : ∀ b ∈ Q, (a', b) ∈ E) : a = a' := by
  by_cases h : a = a'
  · exact h
  · obtain ⟨b, hb, b', hb', hbb'⟩ := Finset.one_lt_card.mp
      (lt_of_lt_of_le (by decide : 1 < 2) hQ)
    exact False.elim (hE a a' b b' h hbb' ⟨ha b hb, ha b' hb', ha' b hb, ha' b' hb'⟩)

lemma distinct_centres_intersection_card {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hE : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {a a' : Fin p} {Q Q' : Finset (Fin l)} (haa' : a ≠ a')
    (ha : ∀ b ∈ Q, (a, b) ∈ E) (ha' : ∀ b ∈ Q', (a', b) ∈ E) :
    (Q ∩ Q').card ≤ 1 := by
  by_cases h : (Q ∩ Q').card ≤ 1
  · exact h
  · have hQ : 2 ≤ (Q ∩ Q').card := Nat.lt_of_not_ge h
    exact False.elim (haa' (star_centre_unique E hE hQ
      (fun b hb => ha b (Finset.mem_inter.mp hb).1)
      (fun b hb => ha' b (Finset.mem_inter.mp hb).2)))

lemma or_function_determines_leaves {α : Type*} [DecidableEq α]
    (Q R : Finset α)
    (h : ∀ x : α → Bool, decide (∃ b ∈ Q, x b = true) =
      decide (∃ b ∈ R, x b = true)) : Q = R := by
  ext b
  have hb := h (fun a => decide (a = b))
  simpa using hb

end PEqualNP.Outside.L_meta_4970
