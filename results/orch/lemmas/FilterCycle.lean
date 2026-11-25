import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1772_aux.Cycle

lemma clause_bound {n r : ℕ} (G : SimpleGraph (Fin n))
    (clauses : Fin r → Finset (Fin n))
    (hclauses : ∀ X : Finset (Fin n),
      (∃ u ∈ X, ∃ v ∈ X, G.Adj u v) ↔ ∀ k, (X ∩ clauses k).Nonempty)
    {ι : Type} [Fintype ι] (inputs : ι → Finset (Fin n))
    (hnegative : ∀ i, ¬ ∃ u ∈ inputs i, ∃ v ∈ inputs i, G.Adj u v)
    (hseparate : ∀ i j, i ≠ j →
      ∃ u ∈ inputs i ∪ inputs j, ∃ v ∈ inputs i ∪ inputs j, G.Adj u v) :
    Fintype.card ι ≤ r := by
  classical
  have missing : ∀ i, ∃ k, ¬ (inputs i ∩ clauses k).Nonempty := by
    intro i
    apply not_forall.mp
    intro h
    exact hnegative i ((hclauses (inputs i)).mpr h)
  choose witness absent using missing
  have injective : Function.Injective witness := by
    intro i j same
    by_contra different
    have unionHit := (hclauses (inputs i ∪ inputs j)).mp (hseparate i j different)
    obtain ⟨v, hv⟩ := unionHit (witness i)
    obtain ⟨either, inClause⟩ := Finset.mem_inter.mp hv
    rcases Finset.mem_union.mp either with hi | hj
    · exact absent i ⟨v, Finset.mem_inter.mpr ⟨hi, inClause⟩⟩
    · exact absent j ⟨v, Finset.mem_inter.mpr ⟨hj, same ▸ inClause⟩⟩
  simpa using Fintype.card_le_of_injective witness injective

lemma five_cycle_needs_five_clauses {n r : ℕ} (G : SimpleGraph (Fin n))
    (clauses : Fin r → Finset (Fin n))
    (hclauses : ∀ X : Finset (Fin n),
      (∃ u ∈ X, ∃ v ∈ X, G.Adj u v) ↔ ∀ k, (X ∩ clauses k).Nonempty)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (vertices : Fin 5 → Fin n)
    (hcycle : ∀ i, G.Adj (vertices i) (vertices (i + 1))) : 5 ≤ r := by
  classical
  let inputs : Fin 5 → Finset (Fin n) := fun i => {vertices i, vertices (i + 2)}
  have negative : ∀ i, ¬ ∃ u ∈ inputs i, ∃ v ∈ inputs i, G.Adj u v := by
    rintro i ⟨u, hu, v, hv, huv⟩
    have cross : ¬ G.Adj (vertices i) (vertices (i + 2)) := by
      intro bad
      apply htri _ _ _ (hcycle i) _ bad.symm
      simpa only [add_assoc, show (1 : Fin 5) + 1 = 2 from rfl] using hcycle (i + 1)
    have hu' : u = vertices i ∨ u = vertices (i + 2) := by simpa [inputs] using hu
    have hv' : v = vertices i ∨ v = vertices (i + 2) := by simpa [inputs] using hv
    rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
    · exact huv.ne rfl
    · exact cross huv
    · exact cross huv.symm
    · exact huv.ne rfl
  have pattern : ∀ i j : Fin 5, i ≠ j →
      ∃ k, k ∈ ({i, i + 2} : Finset (Fin 5)) ∪ {j, j + 2} ∧
        k + 1 ∈ ({i, i + 2} : Finset (Fin 5)) ∪ {j, j + 2} := by decide
  have separate : ∀ i j, i ≠ j →
      ∃ u ∈ inputs i ∪ inputs j, ∃ v ∈ inputs i ∪ inputs j, G.Adj u v := by
    intro i j distinct
    obtain ⟨k, hk, hk'⟩ := pattern i j distinct
    have member (w : Fin 5) (hw : w ∈ ({i, i + 2} : Finset (Fin 5)) ∪ {j, j + 2}) :
        vertices w ∈ inputs i ∪ inputs j := by
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with (rfl | rfl) | (rfl | rfl) <;> simp [inputs]
    exact ⟨vertices k, member k hk, vertices (k + 1), member (k + 1) hk', hcycle k⟩
  simpa using clause_bound G clauses hclauses inputs negative separate

end PEqualNP.Outside.L_meta_1772_aux.Cycle
