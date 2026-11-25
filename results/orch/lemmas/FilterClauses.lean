import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1772_aux

lemma clause_fooling_bound {n r : ℕ} (G : SimpleGraph (Fin n))
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

lemma two_disjoint_edges_need_four_clauses {n r : ℕ} (G : SimpleGraph (Fin n))
    (clauses : Fin r → Finset (Fin n))
    (hclauses : ∀ X : Finset (Fin n),
      (∃ u ∈ X, ∃ v ∈ X, G.Adj u v) ↔ ∀ k, (X ∩ clauses k).Nonempty)
    {a b c d : Fin n} (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : ¬ G.Adj a c) (had : ¬ G.Adj a d)
    (hbc : ¬ G.Adj b c) (hbd : ¬ G.Adj b d) : 4 ≤ r := by
  classical
  let left : Bool → Fin n := fun t => if t then a else b
  let right : Bool → Fin n := fun t => if t then c else d
  let inputs : Bool × Bool → Finset (Fin n) := fun i => {left i.1, right i.2}
  have negative : ∀ i, ¬ ∃ u ∈ inputs i, ∃ v ∈ inputs i, G.Adj u v := by
    rintro ⟨i, j⟩ ⟨u, hu, v, hv, huv⟩
    have cross : ¬ G.Adj (left i) (right j) := by
      cases i <;> cases j <;> simp_all [left, right]
    have hu' : u = left i ∨ u = right j := by simpa [inputs] using hu
    have hv' : v = left i ∨ v = right j := by simpa [inputs] using hv
    rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
    · exact huv.ne rfl
    · exact cross huv
    · exact cross huv.symm
    · exact huv.ne rfl
  have separate : ∀ i j, i ≠ j →
      ∃ u ∈ inputs i ∪ inputs j, ∃ v ∈ inputs i ∪ inputs j, G.Adj u v := by
    rintro ⟨i₁, i₂⟩ ⟨j₁, j₂⟩ distinct
    by_cases first : i₁ = j₁
    · have second : i₂ ≠ j₂ := by
        intro h
        apply distinct
        exact Prod.ext first h
      refine ⟨c, ?_, d, ?_, hcd⟩ <;>
        cases i₂ <;> cases j₂ <;> simp_all [inputs, right]
    · refine ⟨a, ?_, b, ?_, hab⟩ <;>
        cases i₁ <;> cases j₁ <;> simp_all [inputs, left]
  simpa using clause_fooling_bound G clauses hclauses inputs negative separate

end PEqualNP.Outside.L_meta_1772_aux
