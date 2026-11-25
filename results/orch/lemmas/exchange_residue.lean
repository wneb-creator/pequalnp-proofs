import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031_aux.ExchangeResidue

open PEqualNP.EdgeOwnership

lemma triple_edge {n : ℕ} (G : SimpleGraph (Fin n)) (a u v : Fin n)
    (huv : ¬ G.Adj u v)
    (h : ∃ i j, G.Adj i j ∧ (i = a ∨ i = u ∨ i = v) ∧ (j = a ∨ j = u ∨ j = v)) :
    G.Adj a u ∨ G.Adj a v := by
  obtain ⟨i, j, hij, hi, hj⟩ := h
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl
  all_goals first
    | exact Or.inl hij
    | exact Or.inr hij
    | exact Or.inl hij.symm
    | exact Or.inr hij.symm
    | exact False.elim (G.ne_of_adj hij rfl)
    | exact False.elim (huv hij)
    | exact False.elim (huv hij.symm)

lemma shared_nonedge_pair_splits {n : ℕ} (G : SimpleGraph (Fin n))
    (triangle_free : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (a d : Fin n) (had : G.Adj a d) (P : (Fin n → Bool) → Bool)
    (mono : ∀ x y, (∀ k, x k = true → y k = true) → P x = true → P y = true)
    (sound_a : ∀ x, P x = true → x a = true →
      ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)
    (sound_d : ∀ x, P x = true → x d = true →
      ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)
    (u v : Fin n) (huv : ¬ G.Adj u v) (hp : P (pairInput u v) = true) :
    (G.Adj a u ∧ G.Adj d v) ∨ (G.Adj a v ∧ G.Adj d u) := by
  have enlarged (c : Fin n) : P (fun k => decide (k = c ∨ k = u ∨ k = v)) = true := by
    apply mono (pairInput u v) _ _ hp
    intro k hk
    simp only [pairInput, decide_eq_true_eq] at hk ⊢
    exact Or.inr hk
  have ha : G.Adj a u ∨ G.Adj a v := by
    apply triple_edge G a u v huv
    obtain ⟨i, j, hij, hi, hj⟩ := sound_a _ (enlarged a) (by simp)
    exact ⟨i, j, hij, by simpa only [decide_eq_true_eq] using hi,
      by simpa only [decide_eq_true_eq] using hj⟩
  have hd : G.Adj d u ∨ G.Adj d v := by
    apply triple_edge G d u v huv
    obtain ⟨i, j, hij, hi, hj⟩ := sound_d _ (enlarged d) (by simp)
    exact ⟨i, j, hij, by simpa only [decide_eq_true_eq] using hi,
      by simpa only [decide_eq_true_eq] using hj⟩
  rcases ha with hau | hav
  · rcases hd with hdu | hdv
    · exact False.elim (triangle_free a d u had hdu hau.symm)
    · exact Or.inl ⟨hau, hdv⟩
  · rcases hd with hdu | hdv
    · exact Or.inr ⟨hav, hdu⟩
    · exact False.elim (triangle_free a d v had hdv hav.symm)

end PEqualNP.Outside.L_meta_1031_aux.ExchangeResidue
