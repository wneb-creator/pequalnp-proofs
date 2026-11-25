import Mathlib

namespace PEqualNP.Outside.L_meta_4970

lemma right_stars_inter_card_le_one {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {a a' : Fin p} (haa' : a ≠ a') (Q Q' : Finset (Fin l))
    (hQ : ∀ b ∈ Q, (a, b) ∈ E) (hQ' : ∀ b ∈ Q', (a', b) ∈ E) :
    (Q ∩ Q').card ≤ 1 := by
  by_contra hlarge
  obtain ⟨b, hb, b', hb', hbb'⟩ := Finset.one_lt_card.mp (by omega : 1 < (Q ∩ Q').card)
  obtain ⟨hbQ, hbQ'⟩ := Finset.mem_inter.mp hb
  obtain ⟨hb'Q, hb'Q'⟩ := Finset.mem_inter.mp hb'
  exact hC4 a a' b b' haa' hbb' ⟨hQ b hbQ, hQ b' hb'Q, hQ' b hbQ', hQ' b' hb'Q'⟩

lemma left_stars_inter_card_le_one {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {b b' : Fin l} (hbb' : b ≠ b') (P P' : Finset (Fin p))
    (hP : ∀ a ∈ P, (a, b) ∈ E) (hP' : ∀ a ∈ P', (a, b') ∈ E) :
    (P ∩ P').card ≤ 1 := by
  by_contra hlarge
  obtain ⟨a, ha, a', ha', haa'⟩ := Finset.one_lt_card.mp (by omega : 1 < (P ∩ P').card)
  obtain ⟨haP, haP'⟩ := Finset.mem_inter.mp ha
  obtain ⟨ha'P, ha'P'⟩ := Finset.mem_inter.mp ha'
  exact hC4 a a' b b' haa' hbb' ⟨hP a haP, hP' a haP', hP a' ha'P, hP' a' ha'P'⟩

def starLeafFamily {p l : ℕ} (Q : Fin p → Finset (Fin l))
    (P : Fin l → Finset (Fin p)) : Fin p ⊕ Fin l → Finset (Fin (p + l))
  | .inl a => (Q a).image (Fin.natAdd p)
  | .inr b => (P b).image (Fin.castAdd l)

lemma starLeafFamily_separated {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (Q : Fin p → Finset (Fin l)) (P : Fin l → Finset (Fin p))
    (hQ : ∀ a b, b ∈ Q a → (a, b) ∈ E)
    (hP : ∀ b a, a ∈ P b → (a, b) ∈ E) :
    ∀ c d, c ≠ d → (starLeafFamily Q P c ∩ starLeafFamily Q P d).card ≤ 1 := by
  have hinjR : Function.Injective (Fin.natAdd p : Fin l → Fin (p + l)) := by
    intro a b h
    apply Fin.ext
    have hv := congrArg Fin.val h
    simpa using hv
  have hinjL : Function.Injective (Fin.castAdd l : Fin p → Fin (p + l)) := by
    intro a b h
    exact Fin.castAdd_inj.mp h
  have hcross : ∀ (a : Fin p) (b : Fin l),
      Disjoint ((Q a).image (Fin.natAdd p)) ((P b).image (Fin.castAdd l)) := by
    intro a b
    apply Finset.disjoint_left.mpr
    intro i hiR hiL
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hiR
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hiL
    have heq := congrArg Fin.val (hv.trans hu.symm)
    have huLt := u.isLt
    simp only [Fin.val_natAdd, Fin.val_castAdd] at heq
    omega
  intro c d hcd
  cases c with
  | inl a =>
    cases d with
    | inl a' =>
      change ((Q a).image (Fin.natAdd p) ∩ (Q a').image (Fin.natAdd p)).card ≤ 1
      rw [← Finset.image_inter _ _ hinjR, Finset.card_image_of_injective _ hinjR]
      exact right_stars_inter_card_le_one E hC4 (fun h => hcd (congrArg Sum.inl h))
        (Q a) (Q a') (hQ a) (hQ a')
    | inr b =>
      change ((Q a).image (Fin.natAdd p) ∩ (P b).image (Fin.castAdd l)).card ≤ 1
      rw [Finset.disjoint_iff_inter_eq_empty.mp (hcross a b)]
      simp
  | inr b =>
    cases d with
    | inl a =>
      change ((P b).image (Fin.castAdd l) ∩ (Q a).image (Fin.natAdd p)).card ≤ 1
      rw [Finset.disjoint_iff_inter_eq_empty.mp (hcross a b).symm]
      simp
    | inr b' =>
      change ((P b).image (Fin.castAdd l) ∩ (P b').image (Fin.castAdd l)).card ≤ 1
      rw [← Finset.image_inter _ _ hinjL, Finset.card_image_of_injective _ hinjL]
      exact left_stars_inter_card_le_one E hC4 (fun h => hcd (congrArg Sum.inr h))
        (P b) (P b') (hP b) (hP b')

end PEqualNP.Outside.L_meta_4970
