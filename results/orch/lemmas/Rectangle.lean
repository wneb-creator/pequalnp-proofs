import Mathlib

namespace PEqualNP.Outside.L_meta_4675_aux

lemma rectangle_card_one {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Finset (Fin p)) (B : Finset (Fin l))
    (hrect : ∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_cases hA : A.card ≤ 1
  · exact Or.inl hA
  · right
    obtain ⟨a, ha, a', ha', haa'⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
    apply Finset.card_le_one.mpr
    intro b hb b' hb'
    by_contra hbb'
    exact hC4 a a' b b' haa' hbb'
      ⟨hrect a ha b hb, hrect a ha b' hb', hrect a' ha' b hb, hrect a' ha' b' hb'⟩

lemma rectangle_center {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Finset (Fin p)) (B : Finset (Fin l))
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hrect : ∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E) :
    ∃ c : Fin (p + l), ∀ a ∈ A, ∀ b ∈ B,
      Fin.castAdd l a = c ∨ Fin.natAdd p b = c := by
  rcases rectangle_card_one E hC4 A B hrect with h | h
  · obtain ⟨a, ha⟩ := hA
    refine ⟨Fin.castAdd l a, ?_⟩
    intro a' ha' b hb
    exact Or.inl (congrArg (Fin.castAdd l) (Finset.card_le_one.mp h a' ha' a ha))
  · obtain ⟨b, hb⟩ := hB
    refine ⟨Fin.natAdd p b, ?_⟩
    intro a ha b' hb'
    exact Or.inr (congrArg (Fin.natAdd p) (Finset.card_le_one.mp h b' hb' b hb))

lemma rectangle_card_eq_sum {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Finset (Fin p)) (B : Finset (Fin l))
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hrect : ∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E) :
    (A ×ˢ B).card + 1 = A.card + B.card := by
  have ha := Finset.card_pos.mpr hA
  have hb := Finset.card_pos.mpr hB
  rw [Finset.card_product]
  rcases rectangle_card_one E hC4 A B hrect with h | h
  · have he : A.card = 1 := by omega
    simp [he, Nat.add_comm]
  · have he : B.card = 1 := by omega
    simp [he]

lemma rectangle_family_cover {p l m : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Fin m → Finset (Fin p)) (B : Fin m → Finset (Fin l))
    (hA : ∀ i, (A i).Nonempty) (hB : ∀ i, (B i).Nonempty)
    (hrect : ∀ i a, a ∈ A i → ∀ b, b ∈ B i → (a, b) ∈ E)
    (hcover : ∀ a b, (a, b) ∈ E → ∃ i, a ∈ A i ∧ b ∈ B i) :
    ∃ S : Finset (Fin (p + l)),
      (∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      S.card ≤ m ∧
      E.card + S.card ≤ ∑ i, ((A i).card + (B i).card) := by
  classical
  have hc : ∀ i, ∃ c : Fin (p + l), ∀ a ∈ A i, ∀ b ∈ B i,
      Fin.castAdd l a = c ∨ Fin.natAdd p b = c :=
    fun i => rectangle_center E hC4 (A i) (B i) (hA i) (hB i) (hrect i)
  choose c hc using hc
  let S := Finset.univ.image c
  have hS : S.card ≤ m := by
    exact (Finset.card_image_le).trans (by simp)
  have hE : E.card ≤ ∑ i, (A i ×ˢ B i).card := by
    calc
      E.card ≤ (Finset.univ.biUnion fun i => A i ×ˢ B i).card := by
        apply Finset.card_le_card
        intro e he
        obtain ⟨i, hiA, hiB⟩ := hcover e.1 e.2 he
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_product.mpr ⟨hiA, hiB⟩⟩
      _ ≤ ∑ i, (A i ×ˢ B i).card := Finset.card_biUnion_le
  have heq : (∑ i, (A i ×ˢ B i).card) + m =
      ∑ i, ((A i).card + (B i).card) := by
    calc
      _ = ∑ i : Fin m, ((A i ×ˢ B i).card + 1) := by simp [Finset.sum_add_distrib]
      _ = _ := Finset.sum_congr rfl (fun i _ =>
        rectangle_card_eq_sum E hC4 (A i) (B i) (hA i) (hB i) (hrect i))
  refine ⟨S, ?_, hS, ?_⟩
  · intro a b he
    obtain ⟨i, hiA, hiB⟩ := hcover a b he
    have hci : c i ∈ S := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    rcases hc i a hiA b hiB with h | h
    · exact Or.inl (h.symm ▸ hci)
    · exact Or.inr (h.symm ▸ hci)
  · omega

end PEqualNP.Outside.L_meta_4675_aux
