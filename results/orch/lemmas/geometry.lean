import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3451_aux

lemma universal_row_other_unique (N : ℕ) (I : Fin N → Fin N → Prop)
    (h4 : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (p p' : Fin N) (hp : ∀ l, I p l) (hne : p ≠ p')
    (l l' : Fin N) (hpl : I p' l) (hpl' : I p' l') : l = l' := by
  by_contra hl
  exact h4 p p' l l' hne hl ⟨hp l, hp l', hpl, hpl'⟩

lemma universal_column_other_unique (N : ℕ) (I : Fin N → Fin N → Prop)
    (h4 : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (l l' : Fin N) (hl : ∀ p, I p l) (hne : l ≠ l')
    (p p' : Fin N) (hpl : I p l') (hpl' : I p' l') : p = p' := by
  by_contra hp
  exact h4 p p' l l' hp hne ⟨hl p, hpl, hl p', hpl'⟩

lemma universal_row_column_edges (N : ℕ) (I : Fin N → Fin N → Prop)
    (h4 : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (p0 l0 : Fin N) (hp0 : ∀ l, I p0 l) (hl0 : ∀ p, I p l0)
    (p l : Fin N) : I p l ↔ p = p0 ∨ l = l0 := by
  constructor
  · intro h
    by_cases hp : p = p0
    · exact Or.inl hp
    · right
      by_contra hl
      exact h4 p0 p l0 l (Ne.symm hp) (Ne.symm hl)
        ⟨hp0 l0, hp0 l, hl0 p, h⟩
  · rintro (rfl | rfl)
    · exact hp0 l
    · exact hl0 p

end PEqualNP.Outside.L_meta_3451_aux
