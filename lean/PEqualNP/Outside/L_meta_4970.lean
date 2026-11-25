import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

namespace PEqualNP.Outside.L_meta_4970

lemma star_centre_unique {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {Q : Finset (Fin l)} (hQ : 2 ≤ Q.card) {a a' : Fin p}
    (ha : ∀ b ∈ Q, (a, b) ∈ E) (ha' : ∀ b ∈ Q, (a', b) ∈ E) : a = a' := by
  by_contra hne
  obtain ⟨b, hb, b', hb', hbb'⟩ := Finset.one_lt_card.mp (by omega : 1 < Q.card)
  exact hC4 a a' b b' hne hbb' ⟨ha b hb, ha b' hb', ha' b hb, ha' b' hb'⟩

lemma star_leaf_unique {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {P : Finset (Fin p)} (hP : 2 ≤ P.card) {b b' : Fin l}
    (hb : ∀ a ∈ P, (a, b) ∈ E) (hb' : ∀ a ∈ P, (a, b') ∈ E) : b = b' := by
  by_contra hne
  obtain ⟨a, ha, a', ha', haa'⟩ := Finset.one_lt_card.mp (by omega : 1 < P.card)
  exact hC4 a a' b b' haa' hne ⟨hb a ha, hb' a ha, hb a' ha', hb' a' ha'⟩

lemma pure_or_support_eq {α β : Type} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (S T : Finset α)
    (h : ∀ x : β → Bool,
      decide (∃ a ∈ S, x (f a) = true) = decide (∃ a ∈ T, x (f a) = true)) : S = T := by
  classical
  ext a
  have hi := h (fun b => decide (b = f a))
  simpa [hf.eq_iff] using hi

lemma below_pure_or_iff {α : Type} [Fintype α] [DecidableEq α]
    (S : Finset α) (f : (α → Bool) → Bool)
    (hf : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true) :
    (∀ x, f x = true → ∃ i ∈ S, x i = true) ↔
      f (fun i => decide (i ∉ S)) = false := by
  constructor
  · intro h
    cases hcomp : f (fun i => decide (i ∉ S)) with
    | false => rfl
    | true =>
      obtain ⟨i, hi, hni⟩ := h _ hcomp
      simp [hi] at hni
  · intro h x hx
    by_contra hn
    have hle : ∀ i, x i = true → decide (i ∉ S) = true := by
      intro i hi
      simp only [decide_eq_true_eq]
      intro his
      exact hn ⟨i, his, hi⟩
    have hc := hf x (fun i => decide (i ∉ S)) hle hx
    rw [h] at hc
    contradiction

lemma and_below_pure_or {α : Type} [Fintype α] [DecidableEq α]
    (S : Finset α) (f g : (α → Bool) → Bool)
    (hf : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (hg : ∀ x y, (∀ i, x i = true → y i = true) → g x = true → g y = true)
    (h : ∀ x, (f x && g x) = true → ∃ i ∈ S, x i = true) :
    (∀ x, f x = true → ∃ i ∈ S, x i = true) ∨
      (∀ x, g x = true → ∃ i ∈ S, x i = true) := by
  by_cases hfc : f (fun i => decide (i ∉ S)) = false
  · exact Or.inl ((below_pure_or_iff S f hf).mpr hfc)
  · right
    apply (below_pure_or_iff S g hg).mpr
    cases hgc : g (fun i => decide (i ∉ S)) with
    | false => rfl
    | true =>
      have hft : f (fun i => decide (i ∉ S)) = true := by
        cases he : f (fun i => decide (i ∉ S)) <;> simp_all
      obtain ⟨i, hi, hni⟩ := h (fun i => decide (i ∉ S)) (by rw [hft, hgc]; rfl)
      simp [hi] at hni

end PEqualNP.Outside.L_meta_4970
