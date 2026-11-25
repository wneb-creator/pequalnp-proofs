import Mathlib

namespace PEqualNP.Outside.L_meta_2602_aux

lemma small_cover_classification
    (P L : Finset (Fin 13))
    (cover : ∀ p l : Fin 13,
      (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) → p ∈ P ∨ l ∈ L)
    (size : P.card + L.card ≤ 13) :
    (P = Finset.univ ∧ L = ∅) ∨ (P = ∅ ∧ L = Finset.univ) := by
  classical
  have union : P ∪ L = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro p
    exact Finset.mem_union.mpr (cover p p (Or.inl rfl))
  have inter : P ∩ L = ∅ := by
    apply Finset.card_eq_zero.mp
    have h := Finset.card_union_add_card_inter P L
    rw [union] at h
    have hu : (Finset.univ : Finset (Fin 13)).card = 13 := by simp
    omega
  have disjoint : ∀ p : Fin 13, p ∈ P → p ∈ L → False := by
    intro p hp hl
    have h : p ∈ P ∩ L := Finset.mem_inter.mpr ⟨hp, hl⟩
    rw [inter] at h
    exact Finset.not_mem_empty p h
  have step : ∀ p : Fin 13, p ∈ P → p + 1 ∈ P := by
    intro p hp
    rcases cover (p + 1) p (Or.inr (Or.inl rfl)) with h | h
    · exact h
    · exact (disjoint p hp h).elim
  by_cases nonempty : P.Nonempty
  · obtain ⟨p, hp⟩ := nonempty
    have iterate : ∀ n : ℕ, p + (n : Fin 13) ∈ P := by
      intro n
      induction n with
      | zero => simpa using hp
      | succ n ih => simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using step _ ih
    have allP : P = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro q
      have h := iterate (q - p).val
      have hcast : ((q - p).val : Fin 13) = q - p := by simp
      rw [hcast] at h
      have heq : p + (q - p) = q := by abel
      exact heq ▸ h
    left
    refine ⟨allP, ?_⟩
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q hq
    exact disjoint q (by rw [allP]; exact Finset.mem_univ q) hq
  · right
    have emptyP : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp nonempty
    refine ⟨emptyP, ?_⟩
    simpa only [emptyP, Finset.empty_union] using union

end PEqualNP.Outside.L_meta_2602_aux
