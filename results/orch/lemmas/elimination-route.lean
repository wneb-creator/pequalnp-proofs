import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2685.EliminationRoute

lemma leaf_zero {Np Nl : ℕ} (I : Fin Np → Fin Nl → Prop) [DecidableRel I]
    (p0 : Fin Np) (x : Fin Np → Bool) (y : Fin Nl → Bool) :
    decide (∃ p l, I p l ∧ Function.update x p0 false p = true ∧ y l = true) =
      decide (∃ p l, I p l ∧ p ≠ p0 ∧ x p = true ∧ y l = true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨p, l, hp, hx, hy⟩
    have hne : p ≠ p0 := by
      rintro rfl
      simp at hx
    exact ⟨p, l, hp, hne, by simpa [Function.update_of_ne hne] using hx, hy⟩
  · rintro ⟨p, l, hp, hne, hx, hy⟩
    exact ⟨p, l, hp, by simpa [Function.update_of_ne hne] using hx, hy⟩

lemma leaf_one {Np Nl : ℕ} (I : Fin Np → Fin Nl → Prop) [DecidableRel I]
    (p0 : Fin Np) (l0 : Fin Nl) (edge : I p0 l0)
    (leaf : ∀ l, I p0 l → l = l0) (x : Fin Np → Bool) (y : Fin Nl → Bool) :
    decide (∃ p l, I p l ∧ Function.update x p0 true p = true ∧ y l = true) =
      (y l0 || decide (∃ p l, I p l ∧ l ≠ l0 ∧ x p = true ∧ y l = true)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Bool.or_eq_true]
  constructor
  · rintro ⟨p, l, hp, hx, hy⟩
    by_cases hl : l = l0
    · exact Or.inl (hl ▸ hy)
    · right
      have hne : p ≠ p0 := by
        rintro rfl
        exact hl (leaf l hp)
      exact ⟨p, l, hp, hl, by simpa [Function.update_of_ne hne] using hx, hy⟩
  · rintro (hy | ⟨p, l, hp, hl, hx, hy⟩)
    · exact ⟨p0, l0, edge, by simp, hy⟩
    · have hne : p ≠ p0 := by
        rintro rfl
        exact hl (leaf l hp)
      exact ⟨p, l, hp, by simpa [Function.update_of_ne hne] using hx, hy⟩

lemma duplicate_leaf_cover {Np Nl : ℕ} (I : Fin Np → Fin Nl → Prop)
    (p0 p1 : Fin Np) (l0 : Fin Nl) (distinct : p0 ≠ p1)
    (edge : I p1 l0) (leaf0 : ∀ l, I p0 l → l = l0)
    (leaf1 : ∀ l, I p1 l → l = l0)
    (A : Finset (Fin Np)) (B : Finset (Fin Nl))
    (cover : ∀ p l, I p l → p ≠ p0 → p ∈ A ∨ l ∈ B) :
    ∃ (A' : Finset (Fin Np)) (B' : Finset (Fin Nl)),
      (∀ p l, I p l → p ∈ A' ∨ l ∈ B') ∧
      A'.card + B'.card ≤ A.card + B.card := by
  classical
  by_cases hb : l0 ∈ B
  · refine ⟨A, B, ?_, le_rfl⟩
    intro p l hp
    by_cases h : p = p0
    · exact Or.inr ((leaf0 l (h ▸ hp)) ▸ hb)
    · exact cover p l hp h
  · have ha : p1 ∈ A := (cover p1 l0 edge distinct.symm).resolve_right hb
    refine ⟨A.erase p1, insert l0 B, ?_, ?_⟩
    · intro p l hp
      by_cases hp0 : p = p0
      · right
        have h := leaf0 l (hp0 ▸ hp)
        simp [h]
      by_cases hp1 : p = p1
      · right
        have h := leaf1 l (hp1 ▸ hp)
        simp [h]
      rcases cover p l hp hp0 with h | h
      · exact Or.inl (Finset.mem_erase.mpr ⟨hp1, h⟩)
      · exact Or.inr (Finset.mem_insert_of_mem h)
    · have he := Finset.card_erase_add_one ha
      rw [Finset.card_insert_of_notMem hb]
      omega

end PEqualNP.Outside.L_meta_2685.EliminationRoute
