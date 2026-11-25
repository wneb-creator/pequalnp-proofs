import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012.FourClause

open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

lemma five_witness_clause_obstruction {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Fin 4 → Finset (Fin n)) (W : Fin 5 → Finset (Fin n)) (a b : Fin 3 → Fin n)
    (hsafe : ∀ x : Fin n → Bool,
      (∀ c : Fin 4, ∃ u ∈ A c, x u = true) → graphFun G ∅ x = true)
    (hindependent : ∀ r : Fin 5, ∀ u ∈ W r, ∀ v ∈ W r, ¬ G.Adj u v)
    (haccept : ∀ c : Fin 4, ∀ i : Fin 3, a i ∈ A c ∨ b i ∈ A c)
    (hconflict : ∀ r s : Fin 5, r ≠ s →
      ∃ i : Fin 3, (a i ∈ W r ∧ b i ∈ W s) ∨ (a i ∈ W s ∧ b i ∈ W r)) : False := by
  classical
  have hmiss : ∀ r : Fin 5, ∃ c : Fin 4, Disjoint (A c) (W r) := by
    intro r
    by_contra hnone
    push Not at hnone
    let x : Fin n → Bool := fun u => decide (u ∈ W r)
    have hall : ∀ c : Fin 4, ∃ u ∈ A c, x u = true := by
      intro c
      obtain ⟨u, huA, huW⟩ := Finset.not_disjoint_iff.mp (hnone c)
      exact ⟨u, huA, by simpa [x] using huW⟩
    have hf := hsafe x hall
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq] at hf
    obtain ⟨u, v, huv, hu, hv⟩ := hf
    exact hindependent r u (by simpa [x] using hu) v (by simpa [x] using hv) huv
  choose f hf using hmiss
  have hinj : Function.Injective f := by
    intro r s hrs
    by_contra hne
    obtain ⟨i, hi⟩ := hconflict r s hne
    have hfr := Finset.disjoint_left.mp (hf r)
    have hfs := Finset.disjoint_left.mp (hf s)
    rcases haccept (f r) i with ha | hb
    · rcases hi with ⟨har, _⟩ | ⟨has, _⟩
      · exact hfr ha har
      · exact hfs (hrs ▸ ha) has
    · rcases hi with ⟨_, hbs⟩ | ⟨_, hbr⟩
      · exact hfs (hrs ▸ hb) hbs
      · exact hfr hb hbr
  have hcard := Fintype.card_le_of_injective f hinj
  simp at hcard

end PEqualNP.Outside.L_meta_5012.FourClause
