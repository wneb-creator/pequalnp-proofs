import Mathlib

namespace PEqualNP.Outside.L_meta_4675

lemma rectangle_star {p l : ℕ} (E : Finset (Fin p × Fin l))
    (h4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Finset (Fin p)) (B : Finset (Fin l))
    (ha : A.Nonempty) (hb : B.Nonempty)
    (hab : ∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E) :
    (∃ a : Fin p, ∀ a' ∈ A, a' = a) ∨
      (∃ b : Fin l, ∀ b' ∈ B, b' = b) := by
  by_cases hA : A.card ≤ 1
  · obtain ⟨a, ha⟩ := ha
    exact Or.inl ⟨a, fun a' ha' => Finset.card_le_one.mp hA a' ha' a ha⟩
  · have hB : B.card ≤ 1 := by
      by_contra hB
      obtain ⟨a, ha, a', ha', haa'⟩ := Finset.one_lt_card.mp (show 1 < A.card by omega)
      obtain ⟨b, hb, b', hb', hbb'⟩ := Finset.one_lt_card.mp (show 1 < B.card by omega)
      exact h4 a a' b b' haa' hbb'
        ⟨hab a ha b hb, hab a ha b' hb', hab a' ha' b hb, hab a' ha' b' hb'⟩
    obtain ⟨b, hb⟩ := hb
    exact Or.inr ⟨b, fun b' hb' => Finset.card_le_one.mp hB b' hb' b hb⟩

lemma rectangle_center {p l : ℕ} (E : Finset (Fin p × Fin l))
    (h4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Finset (Fin p)) (B : Finset (Fin l))
    (ha : A.Nonempty) (hb : B.Nonempty)
    (hab : ∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E) :
    ∃ c : Fin (p + l), ∀ a ∈ A, ∀ b ∈ B,
      Fin.castAdd l a = c ∨ Fin.natAdd p b = c := by
  rcases rectangle_star E h4 A B ha hb hab with ⟨a, ha⟩ | ⟨b, hb⟩
  · exact ⟨Fin.castAdd l a, fun a' ha' _ _ => Or.inl (congrArg (Fin.castAdd l) (ha a' ha'))⟩
  · exact ⟨Fin.natAdd p b, fun _ _ b' hb' => Or.inr (congrArg (Fin.natAdd p) (hb b' hb'))⟩

lemma rectangle_cover {p l k : ℕ} (E : Finset (Fin p × Fin l))
    (h4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Fin k → Finset (Fin p)) (B : Fin k → Finset (Fin l))
    (ha : ∀ i, (A i).Nonempty) (hb : ∀ i, (B i).Nonempty)
    (hab : ∀ i, ∀ a ∈ A i, ∀ b ∈ B i, (a, b) ∈ E)
    (cover : ∀ a b, (a, b) ∈ E → ∃ i, a ∈ A i ∧ b ∈ B i) :
    ∃ S : Finset (Fin (p + l)),
      (∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      S.card ≤ k := by
  classical
  choose c hc using fun i => rectangle_center E h4 (A i) (B i) (ha i) (hb i) (hab i)
  refine ⟨Finset.univ.image c, ?_, ?_⟩
  · intro a b hab
    obtain ⟨i, hai, hbi⟩ := cover a b hab
    rcases hc i a hai b hbi with h | h
    · exact Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h.symm⟩)
    · exact Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h.symm⟩)
  · exact (Finset.card_image_le).trans (by simp)

end PEqualNP.Outside.L_meta_4675
