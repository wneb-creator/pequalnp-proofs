import PEqualNP.Defs
import Mathlib.Tactic.Push

namespace PEqualNP.Outside.L_meta_4675_aux

lemma rectangle_subsingleton {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Finset (Fin p)) (B : Finset (Fin l))
    (hrect : ∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E) :
    (∀ a ∈ A, ∀ a' ∈ A, a = a') ∨ (∀ b ∈ B, ∀ b' ∈ B, b = b') := by
  classical
  by_cases hA : ∀ a ∈ A, ∀ a' ∈ A, a = a'
  · exact Or.inl hA
  · right
    push_neg at hA
    obtain ⟨a, ha, a', ha', haa'⟩ := hA
    intro b hb b' hb'
    by_contra hbb'
    exact hfour a a' b b' haa' hbb'
      ⟨hrect a ha b hb, hrect a ha b' hb',
       hrect a' ha' b hb, hrect a' ha' b' hb'⟩

lemma rectangle_card_le_one {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Finset (Fin p)) (B : Finset (Fin l))
    (hrect : ∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  rcases rectangle_subsingleton E hfour A B hrect with hA | hB
  · exact Or.inl (Finset.card_le_one.mpr hA)
  · exact Or.inr (Finset.card_le_one.mpr hB)

lemma rectangle_singleton {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Finset (Fin p)) (B : Finset (Fin l))
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hrect : ∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E) :
    (∃ a, A = {a}) ∨ (∃ b, B = {b}) := by
  rcases rectangle_card_le_one E hfour A B hrect with ha | hb
  · left
    exact Finset.card_eq_one.mp (by have := hA.card_pos; omega)
  · right
    exact Finset.card_eq_one.mp (by have := hB.card_pos; omega)

lemma rectangle_cost {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Finset (Fin p)) (B : Finset (Fin l))
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hrect : ∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E) :
    (A ×ˢ B).card = A.card + B.card - 1 := by
  rcases rectangle_singleton E hfour A B hA hB hrect with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · simp
  · simp

lemma rectangle_has_centre {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Finset (Fin p)) (B : Finset (Fin l))
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hrect : ∀ a ∈ A, ∀ b ∈ B, (a, b) ∈ E) :
    ∃ c : Fin (p + l), ∀ a ∈ A, ∀ b ∈ B,
      Fin.castAdd l a = c ∨ Fin.natAdd p b = c := by
  rcases rectangle_singleton E hfour A B hA hB hrect with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · refine ⟨Fin.castAdd l a, ?_⟩
    intro a' ha' b hb
    have : a' = a := Finset.mem_singleton.mp ha'
    exact Or.inl (congrArg (Fin.castAdd l) this)
  · refine ⟨Fin.natAdd p b, ?_⟩
    intro a ha b' hb'
    have : b' = b := Finset.mem_singleton.mp hb'
    exact Or.inr (congrArg (Fin.natAdd p) this)


lemma rectangle_family_cover {p l : ℕ} {ι : Type*} [DecidableEq ι]
    (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (I : Finset ι) (A : ι → Finset (Fin p)) (B : ι → Finset (Fin l))
    (hA : ∀ i ∈ I, (A i).Nonempty) (hB : ∀ i ∈ I, (B i).Nonempty)
    (hrect : ∀ i ∈ I, ∀ a ∈ A i, ∀ b ∈ B i, (a, b) ∈ E) :
    ∃ S : Finset (Fin (p + l)),
      (∀ i ∈ I, ∀ a ∈ A i, ∀ b ∈ B i,
        Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      (I.biUnion fun i => A i ×ˢ B i).card + S.card ≤
        ∑ i ∈ I, ((A i).card + (B i).card) := by
  classical
  revert hA hB hrect
  induction I using Finset.induction_on with
  | empty =>
    intro hA hB hrect
    exact ⟨∅, by simp, by simp⟩
  | @insert i I hi ih =>
    intro hA hB hrect
    obtain ⟨S, hScover, hScost⟩ := ih
      (fun j hj => hA j (Finset.mem_insert_of_mem hj))
      (fun j hj => hB j (Finset.mem_insert_of_mem hj))
      (fun j hj => hrect j (Finset.mem_insert_of_mem hj))
    have hai := hA i (Finset.mem_insert_self i I)
    have hbi := hB i (Finset.mem_insert_self i I)
    have hri := hrect i (Finset.mem_insert_self i I)
    obtain ⟨c, hc⟩ := rectangle_has_centre E hfour (A i) (B i) hai hbi hri
    refine ⟨insert c S, ?_, ?_⟩
    · intro j hj a ha b hb
      rcases Finset.mem_insert.mp hj with rfl | hj
      · rcases hc a ha b hb with h | h
        · exact Or.inl (Finset.mem_insert.mpr (Or.inl h))
        · exact Or.inr (Finset.mem_insert.mpr (Or.inl h))
      · rcases hScover j hj a ha b hb with h | h
        · exact Or.inl (Finset.mem_insert_of_mem h)
        · exact Or.inr (Finset.mem_insert_of_mem h)
    · have hR : ((insert i I).biUnion fun j => A j ×ˢ B j).card ≤
          (A i ×ˢ B i).card + (I.biUnion fun j => A j ×ˢ B j).card := by
        rw [Finset.biUnion_insert]
        exact Finset.card_union_le _ _
      have hS : (insert c S).card ≤ S.card + 1 := Finset.card_insert_le _ _
      have hcost : (A i ×ˢ B i).card + 1 = (A i).card + (B i).card := by
        rw [rectangle_cost E hfour (A i) (B i) hai hbi hri]
        have ha := hai.card_pos
        omega
      rw [Finset.sum_insert hi]
      omega

lemma rectangle_cover_bound {p l : ℕ} {ι : Type*} [DecidableEq ι]
    (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (I : Finset ι) (A : ι → Finset (Fin p)) (B : ι → Finset (Fin l))
    (hA : ∀ i ∈ I, (A i).Nonempty) (hB : ∀ i ∈ I, (B i).Nonempty)
    (hrect : ∀ i ∈ I, ∀ a ∈ A i, ∀ b ∈ B i, (a, b) ∈ E)
    (hcover : ∀ a b, (a, b) ∈ E → ∃ i ∈ I, a ∈ A i ∧ b ∈ B i) :
    ∃ S : Finset (Fin (p + l)),
      (∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      E.card + S.card ≤ ∑ i ∈ I, ((A i).card + (B i).card) := by
  classical
  obtain ⟨S, hScover, hScost⟩ := rectangle_family_cover E hfour I A B hA hB hrect
  refine ⟨S, ?_, ?_⟩
  · intro a b hab
    obtain ⟨i, hi, ha, hb⟩ := hcover a b hab
    exact hScover i hi a ha b hb
  · have hsub : E ⊆ I.biUnion (fun i => A i ×ˢ B i) := by
      intro e he
      obtain ⟨i, hi, ha, hb⟩ := hcover e.1 e.2 he
      exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_product.mpr ⟨ha, hb⟩⟩
    exact le_trans (Nat.add_le_add_right (Finset.card_le_card hsub) S.card) hScost

end PEqualNP.Outside.L_meta_4675_aux
