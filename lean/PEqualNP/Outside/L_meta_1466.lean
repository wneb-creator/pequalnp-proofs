import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1466

lemma step (q N : ℕ) (L : Fin N → Finset (Fin N)) (X A : Finset (Fin N))
    (hq : 2 ≤ q) (hc : ∀ i, (L i).card = q + 1)
    (hi : ∀ i j, i ≠ j → (L i ∩ L j).card = 1)
    (hX : 15 * q ≤ X.card + 8) (hj : A.card ≤ 6)
    (h2 : ∀ i, (L i ∩ A).card ≤ 2) :
    ∃ x ∈ X, x ∉ A ∧ ∀ i, (L i ∩ insert x A).card ≤ 2 := by
  classical
  have hTcard : (Finset.univ.filter (fun i => (L i ∩ A).card = 2)).card ≤ 15 := by
    have h1 : (Finset.univ.filter (fun i => (L i ∩ A).card = 2)).card
        ≤ (A.powersetCard 2).card := by
      apply Finset.card_le_card_of_injOn (fun i => L i ∩ A)
      · intro i hi'
        have := (Finset.mem_filter.mp (Finset.mem_coe.mp hi')).2
        exact Finset.mem_coe.mpr
          (Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, this⟩)
      · intro i hi' j _ hij
        by_contra hne
        have hi2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hi')).2
        have hij' : L i ∩ A = L j ∩ A := hij
        have hsub : L i ∩ A ⊆ L i ∩ L j := by
          intro x hx
          have hx' : x ∈ L j ∩ A := by rw [← hij']; exact hx
          exact Finset.mem_inter.mpr
            ⟨(Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx').1⟩
        have := Finset.card_le_card hsub
        rw [hi2, hi i j hne] at this
        omega
    rw [Finset.card_powersetCard] at h1
    have h3 : A.card.choose 2 ≤ Nat.choose 6 2 := Nat.choose_le_choose 2 hj
    have h4 : Nat.choose 6 2 = 15 := by decide
    omega
  have hBcard : (A ∪ (Finset.univ.filter (fun i => (L i ∩ A).card = 2)).biUnion
      (fun i => L i \ A)).card ≤ 6 + 15 * (q - 1) := by
    have h1 : ((Finset.univ.filter (fun i => (L i ∩ A).card = 2)).biUnion
        (fun i => L i \ A)).card
        ≤ (Finset.univ.filter (fun i => (L i ∩ A).card = 2)).card * (q - 1) := by
      apply Finset.card_biUnion_le_card_mul
      intro i hi'
      have hi2 := (Finset.mem_filter.mp hi').2
      have := Finset.card_sdiff_add_card_inter (L i) A
      rw [hc i, hi2] at this
      omega
    have h2' := Finset.card_union_le A
      ((Finset.univ.filter (fun i => (L i ∩ A).card = 2)).biUnion (fun i => L i \ A))
    have h3 : (Finset.univ.filter (fun i => (L i ∩ A).card = 2)).card * (q - 1)
        ≤ 15 * (q - 1) := Nat.mul_le_mul_right _ hTcard
    omega
  have hlt : (A ∪ (Finset.univ.filter (fun i => (L i ∩ A).card = 2)).biUnion
      (fun i => L i \ A)).card < X.card := by omega
  obtain ⟨x, hxX, hxB⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hxA : x ∉ A := fun h => hxB (Finset.mem_union_left _ h)
  refine ⟨x, hxX, hxA, fun i => ?_⟩
  by_cases hxi : x ∈ L i
  · have hiT : (L i ∩ A).card ≠ 2 := by
      intro h
      apply hxB
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩,
        Finset.mem_sdiff.mpr ⟨hxi, hxA⟩⟩
    have h1 : (L i ∩ A).card ≤ 1 := by have := h2 i; omega
    have hsub : L i ∩ insert x A ⊆ insert x (L i ∩ A) := by
      intro y hy
      rw [Finset.mem_inter, Finset.mem_insert] at hy
      rw [Finset.mem_insert, Finset.mem_inter]
      tauto
    have h3 := Finset.card_le_card hsub
    have h4 := Finset.card_insert_le x (L i ∩ A)
    omega
  · have h5 : L i ∩ insert x A = L i ∩ A := by
      ext y
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h | h⟩
        · exact absurd (h ▸ h1) hxi
        · exact ⟨h1, h⟩
      · rintro ⟨h1, h⟩
        exact ⟨h1, Or.inr h⟩
    rw [h5]
    exact h2 i

lemma build (q N : ℕ) (L : Fin N → Finset (Fin N)) (X : Finset (Fin N))
    (hq : 2 ≤ q) (hc : ∀ i, (L i).card = q + 1)
    (hi : ∀ i j, i ≠ j → (L i ∩ L j).card = 1)
    (hX : 15 * q ≤ X.card + 8) (j : ℕ) (hj : j ≤ 7) :
    ∃ A : Finset (Fin N), A ⊆ X ∧ A.card = j ∧ ∀ i, (L i ∩ A).card ≤ 2 := by
  classical
  induction j with
  | zero => exact ⟨∅, Finset.empty_subset _, rfl, fun i => by simp⟩
  | succ j ih =>
    obtain ⟨A, hAX, hAc, hA2⟩ := ih (by omega)
    obtain ⟨x, hxX, hxA, hx2⟩ := step q N L X A hq hc hi hX (by omega) hA2
    refine ⟨insert x A, ?_, ?_, hx2⟩
    · intro y hy
      rcases Finset.mem_insert.mp hy with h | h
      · exact h ▸ hxX
      · exact hAX h
    · rw [Finset.card_insert_of_notMem hxA, hAc]

end PEqualNP.Outside.L_meta_1466

theorem PEqualNP.Outside.L_meta_1466 : ∀ (q : ℕ) (L : Fin (q ^ 2 + q + 1) → Finset (Fin (q ^ 2 + q + 1)))
    (X : Finset (Fin (q ^ 2 + q + 1))),
    2 ≤ q → (∀ i, (L i).card = q + 1) → (∀ i j, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin (q ^ 2 + q + 1), p ≠ p' → ∃ i, p ∈ L i ∧ p' ∈ L i) →
    15 * q ≤ X.card + 8 →
    ∃ A : Finset (Fin (q ^ 2 + q + 1)), A ⊆ X ∧ A.card = 7 ∧ ∀ i, (L i ∩ A).card ≤ 2 := by
  intro q L X hq hc hi _ hX
  exact PEqualNP.Outside.L_meta_1466.build q _ L X hq hc hi hX 7 le_rfl
