import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2870_aux

private lemma context_point_ne_line {n : ℕ} (p l : Fin n) :
    Fin.castAdd n p ≠ Fin.natAdd n l := by
  intro h
  have hval := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
  have hp := p.isLt
  omega

private lemma context_line_count_le {n : ℕ} (t : Finset (Fin (n+n))) :
    Fintype.card {l : Fin n // Fin.natAdd n l ∈ t} ≤ t.card := by
  classical
  have h := Fintype.card_le_of_injective
    (fun l : {l : Fin n // Fin.natAdd n l ∈ t} =>
      (⟨Fin.natAdd n l.1, l.2⟩ : ↥t)) (by
        intro a b hab
        apply Subtype.ext
        have hval := congrArg (fun x : ↥t => x.1.val) hab
        apply Fin.ext
        simp only [Fin.val_natAdd] at hval
        omega)
  simpa using h

lemma mixed_singleton_context (q n : ℕ) (I : Fin n → Fin n → Prop)
    (A B F : Finset (Finset (Fin (n+n)))) (hq : 2 ≤ q)
    (point : ∃ p : Fin n, ({Fin.castAdd n p} : Finset (Fin (n+n))) ∈ A)
    (line : ∃ l : Fin n, ({Fin.natAdd n l} : Finset (Fin (n+n))) ∈ A)
    (product : ∀ a ∈ A, ∀ b ∈ B, a ∪ b ∈ F)
    (sound : ∀ t ∈ F, Fintype.card {l : Fin n // Fin.natAdd n l ∈ t} ≤ q →
      ∃ p l, I p l ∧ Fin.castAdd n p ∈ t ∧ Fin.natAdd n l ∈ t)
    (p l : Fin n) (v : Finset (Fin (n+n))) (hv : v ∈ B)
    (sub : v ⊆ {Fin.castAdd n p, Fin.natAdd n l}) :
    v = {Fin.castAdd n p, Fin.natAdd n l} := by
  classical
  obtain ⟨p₀, hp₀⟩ := point
  obtain ⟨l₀, hl₀⟩ := line
  have hasPoint : Fin.castAdd n p ∈ v := by
    by_contra missing
    have onlyLines : ({Fin.natAdd n l₀} : Finset (Fin (n+n))) ∪ v ⊆
        {Fin.natAdd n l₀, Fin.natAdd n l} := by
      intro i hi
      rcases Finset.mem_union.mp hi with hi | hi
      · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hi))
      · rcases Finset.mem_insert.mp (sub hi) with h | h
        · exact False.elim (missing (h ▸ hi))
        · exact Finset.mem_insert.mpr (Or.inr h)
    have small : Fintype.card {r : Fin n // Fin.natAdd n r ∈
        ({Fin.natAdd n l₀} : Finset (Fin (n+n))) ∪ v} ≤ q :=
      (context_line_count_le _).trans ((Finset.card_le_card onlyLines).trans
        (Finset.card_le_two.trans hq))
    obtain ⟨a, b, _, ha, _⟩ := sound _ (product _ hl₀ _ hv) small
    rcases Finset.mem_insert.mp (onlyLines ha) with h | h
    · exact context_point_ne_line a l₀ h
    · exact context_point_ne_line a l (Finset.mem_singleton.mp h)
  have hasLine : Fin.natAdd n l ∈ v := by
    by_contra missing
    have onlyPoints : ({Fin.castAdd n p₀} : Finset (Fin (n+n))) ∪ v ⊆
        {Fin.castAdd n p₀, Fin.castAdd n p} := by
      intro i hi
      rcases Finset.mem_union.mp hi with hi | hi
      · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hi))
      · rcases Finset.mem_insert.mp (sub hi) with h | h
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h))
        · exact False.elim (missing ((Finset.mem_singleton.mp h) ▸ hi))
    have small : Fintype.card {r : Fin n // Fin.natAdd n r ∈
        ({Fin.castAdd n p₀} : Finset (Fin (n+n))) ∪ v} ≤ q :=
      (context_line_count_le _).trans ((Finset.card_le_card onlyPoints).trans
        (Finset.card_le_two.trans hq))
    obtain ⟨a, b, _, _, hb⟩ := sound _ (product _ hp₀ _ hv) small
    rcases Finset.mem_insert.mp (onlyPoints hb) with h | h
    · exact context_point_ne_line p₀ b h.symm
    · exact context_point_ne_line p b (Finset.mem_singleton.mp h).symm
  apply Finset.Subset.antisymm sub
  intro i hi
  rcases Finset.mem_insert.mp hi with h | h
  · exact h ▸ hasPoint
  · exact (Finset.mem_singleton.mp h) ▸ hasLine

end PEqualNP.Outside.L_meta_2870_aux
