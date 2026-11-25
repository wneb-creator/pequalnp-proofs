import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_2583.RectangleFamilies

variable {n m : Nat} {ι κ : Type}
variable (I : Fin n → Fin m → Prop) [DecidableRel I]
variable (P : ι → Finset (Fin n)) (L : κ → Finset (Fin m))

def HitsPointClauses (X : Finset (Fin n)) : Prop := ∀ i, ∃ p ∈ X, p ∈ P i

def HitsLineClauses (Y : Finset (Fin m)) : Prop := ∀ j, ∃ l ∈ Y, l ∈ L j

def BelowIncidence : Prop := ∀ X Y,
  HitsPointClauses P X → HitsLineClauses L Y → ∃ p ∈ X, ∃ l ∈ Y, I p l

lemma point_clause (below : BelowIncidence I P L) (p : Fin n) (common : ∀ i, p ∈ P i) :
    ∃ j, ∀ l ∈ L j, I p l := by
  classical
  by_contra! no
  let Y := Finset.univ.filter (fun l => ¬ I p l)
  have points : HitsPointClauses P {p} := fun i => ⟨p, by simp, common i⟩
  have lines : HitsLineClauses L Y := by
    intro j
    obtain ⟨l, hl, bad⟩ := no j
    exact ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, bad⟩, hl⟩
  obtain ⟨r, hr, l, hl, edge⟩ := below {p} Y points lines
  have rp := Finset.mem_singleton.mp hr
  subst r
  exact (Finset.mem_filter.mp hl).2 edge

lemma line_clause (below : BelowIncidence I P L) (l : Fin m) (common : ∀ j, l ∈ L j) :
    ∃ i, ∀ p ∈ P i, I p l := by
  have transposed : BelowIncidence (fun l p => I p l) L P := by
    intro Y X lineHit pointHit
    obtain ⟨p, hp, l, hl, edge⟩ := below X Y pointHit lineHit
    exact ⟨l, hl, p, hp, edge⟩
  exact point_clause (fun l p => I p l) L P transposed l common

lemma common_cross (below : BelowIncidence I P L) (p : Fin n) (l : Fin m)
    (point : ∀ i, p ∈ P i) (line : ∀ j, l ∈ L j) : I p l := by
  obtain ⟨j, hj⟩ := point_clause I P L below p point
  exact hj l (line j)

lemma star_envelope
    (noFour : ∀ p p' : Fin n, ∀ l l' : Fin m, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (below : BelowIncidence I P L)
    (useful : ∃ p : Fin n, ∃ l : Fin m, (∀ i, p ∈ P i) ∧ (∀ j, l ∈ L j)) :
    (∃ p : Fin n, ∃ j : κ,
      (∀ p' : Fin n, (∀ i, p' ∈ P i) → p' = p) ∧ (∀ l ∈ L j, I p l)) ∨
    (∃ l : Fin m, ∃ i : ι,
      (∀ l' : Fin m, (∀ j, l' ∈ L j) → l' = l) ∧ (∀ p ∈ P i, I p l)) := by
  classical
  obtain ⟨p, l, hp, hl⟩ := useful
  by_cases singleton : ∀ p' : Fin n, (∀ i, p' ∈ P i) → p' = p
  · obtain ⟨j, hj⟩ := point_clause I P L below p hp
    exact Or.inl ⟨p, j, singleton, hj⟩
  · push_neg at singleton
    obtain ⟨p', hp', diff⟩ := singleton
    have singleLine : ∀ l' : Fin m, (∀ j, l' ∈ L j) → l' = l := by
      intro l' hl'
      by_contra different
      exact noFour p p' l l' (Ne.symm diff) (Ne.symm different)
        ⟨common_cross I P L below p l hp hl,
          common_cross I P L below p l' hp hl',
          common_cross I P L below p' l hp' hl,
          common_cross I P L below p' l' hp' hl'⟩
    obtain ⟨i, hi⟩ := line_clause I P L below l hl
    exact Or.inr ⟨l, i, singleLine, hi⟩

lemma point_envelope_preserves (p : Fin n) (j : κ)
    (singleton : ∀ p' : Fin n, (∀ i, p' ∈ P i) → p' = p) :
    ∀ p' : Fin n, ∀ l : Fin m, (∀ i, p' ∈ P i) → (∀ j, l ∈ L j) → p' = p ∧ l ∈ L j := by
  intro p' l hp hl
  exact ⟨singleton p' hp, hl j⟩

lemma line_envelope_preserves (l : Fin m) (i : ι)
    (singleton : ∀ l' : Fin m, (∀ j, l' ∈ L j) → l' = l) :
    ∀ p : Fin n, ∀ l' : Fin m, (∀ i, p ∈ P i) → (∀ j, l' ∈ L j) → l' = l ∧ p ∈ P i := by
  intro p l' hp hl
  exact ⟨singleton l' hl, hp i⟩

end PEqualNP.Outside.L_meta_2583.RectangleFamilies
