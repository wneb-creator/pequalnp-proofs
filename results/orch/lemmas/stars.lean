import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970

lemma left_star_unique {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hcycle : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {a a' : Fin p} (Q : Finset (Fin l)) (hQ : 2 ≤ Q.card)
    (hleft : ∀ b ∈ Q, (a, b) ∈ E) (hright : ∀ b ∈ Q, (a', b) ∈ E) :
    a = a' := by
  obtain ⟨b, hb, b', hb', hne⟩ := Finset.one_lt_card.mp hQ
  by_contra ha
  exact hcycle a a' b b' ha hne ⟨hleft b hb, hleft b' hb', hright b hb, hright b' hb'⟩

lemma right_star_unique {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hcycle : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {b b' : Fin l} (P : Finset (Fin p)) (hP : 2 ≤ P.card)
    (hleft : ∀ a ∈ P, (a, b) ∈ E) (hright : ∀ a ∈ P, (a, b') ∈ E) :
    b = b' := by
  obtain ⟨a, ha, a', ha', hne⟩ := Finset.one_lt_card.mp hP
  by_contra hb
  exact hcycle a a' b b' hne hb ⟨hleft a ha, hright a ha, hleft a' ha', hright a' ha'⟩

lemma left_star_inter_card_le_one {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hcycle : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {a a' : Fin p} (ha : a ≠ a') (Q R : Finset (Fin l))
    (hQ : ∀ b ∈ Q, (a, b) ∈ E) (hR : ∀ b ∈ R, (a', b) ∈ E) :
    (Q ∩ R).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro b hb b' hb'
  by_contra hne
  exact hcycle a a' b b' ha hne
    ⟨hQ b (Finset.mem_inter.mp hb).1, hQ b' (Finset.mem_inter.mp hb').1,
      hR b (Finset.mem_inter.mp hb).2, hR b' (Finset.mem_inter.mp hb').2⟩

lemma ownership_cover {p l : ℕ} (E : Finset (Fin p × Fin l))
    (own : Fin p × Fin l → Fin (p + l))
    (hown : ∀ e ∈ E,
      own e = Fin.castAdd l e.1 ∨ own e = Fin.natAdd p e.2) :
    ∀ a b, (a, b) ∈ E →
      Fin.castAdd l a ∈ E.image own ∨ Fin.natAdd p b ∈ E.image own := by
  intro a b hab
  have hm : own (a, b) ∈ E.image own := Finset.mem_image_of_mem own hab
  rcases hown (a, b) hab with h | h
  · exact Or.inl (h ▸ hm)
  · exact Or.inr (h ▸ hm)

lemma ownership_ledger {α β : Type*} [DecidableEq β]
    (E : Finset α) (own : α → β) :
    (∑ v ∈ E.image own, ((E.filter (fun e => own e = v)).card - 1)) +
      (E.image own).card = E.card := by
  have hpos : ∀ v ∈ E.image own, 1 ≤ (E.filter (fun e => own e = v)).card := by
    intro v hv
    obtain ⟨e, he, hev⟩ := Finset.mem_image.mp hv
    exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hev⟩⟩
  calc
    (∑ v ∈ E.image own, ((E.filter (fun e => own e = v)).card - 1)) +
        (E.image own).card =
        ∑ v ∈ E.image own, ((E.filter (fun e => own e = v)).card - 1 + 1) := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
    _ = ∑ v ∈ E.image own, (E.filter (fun e => own e = v)).card := by
      apply Finset.sum_congr rfl
      intro v hv
      exact Nat.sub_add_cancel (hpos v hv)
    _ = E.card := (Finset.card_eq_sum_card_image own E).symm

end PEqualNP.Outside.L_meta_4970
