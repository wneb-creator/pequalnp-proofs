import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2962_aux.Matching

open PEqualNP.MetaComplexity.NestedCover

variable {n m : ℕ} (G : SimpleGraph (Fin n))

theorem residual_matching_bound (D : Finset (Sym2 (Fin n)))
    (a b : Fin m → Fin n) (R : Finset (Fin n))
    (hadj : ∀ i, G.Adj (a i) (b i))
    (hmatch : ∀ i j, a i = a j ∨ a i = b j ∨ b i = a j ∨ b i = b j → i = j)
    (hR : (G.deleteEdges (D : Set (Sym2 (Fin n)))).IsVertexCover
      (R : Set (Fin n))) :
    m ≤ (Finset.univ.filter (fun i => s(a i, b i) ∈ D)).card + R.card := by
  classical
  let K : Finset (Fin m) := Finset.univ.filter fun i => s(a i, b i) ∈ D
  let Q : Finset (Fin m) := Finset.univ \ K
  let pick : Fin m → Fin n := fun i => if a i ∈ R then a i else b i
  have hpick : ∀ i ∈ Q, pick i ∈ R := by
    intro i hi
    have he : s(a i, b i) ∉ D := by
      simpa [Q, K] using (Finset.mem_sdiff.mp hi).2
    have hab : (G.deleteEdges (D : Set (Sym2 (Fin n)))).Adj (a i) (b i) := by
      rw [SimpleGraph.deleteEdges_adj]
      exact ⟨hadj i, he⟩
    have hc := hR hab
    by_cases ha : a i ∈ R
    · simp [pick, ha]
    · rcases hc with h | h
      · exact (ha h).elim
      · simpa [pick, ha] using h
  have hinj : ∀ i ∈ Q, ∀ j ∈ Q, pick i = pick j → i = j := by
    intro i _ j _ heq
    apply hmatch i j
    by_cases hi : a i ∈ R <;> by_cases hj : a j ∈ R <;>
      simp only [pick, hi, hj, if_true, if_false] at heq
    · exact Or.inl heq
    · exact Or.inr (Or.inl heq)
    · exact Or.inr (Or.inr (Or.inl heq))
    · exact Or.inr (Or.inr (Or.inr heq))
  have hcard : Q.card ≤ R.card := Finset.card_le_card_of_injOn pick hpick hinj
  have hpartition : Q.card + K.card = m := by
    simpa [Q] using (Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ K))
  change m ≤ K.card + R.card
  omega

theorem matching_charge_sufficient (D : Finset (Sym2 (Fin n)))
    (a b : Fin m → Fin n) (T R : Finset (Fin n)) (budget : ℕ)
    (hadj : ∀ i, G.Adj (a i) (b i))
    (hmatch : ∀ i j, a i = a j ∨ a i = b j ∨ b i = a j ∨ b i = b j → i = j)
    (hR : (G.deleteEdges (D : Set (Sym2 (Fin n)))).IsVertexCover
      (R : Set (Fin n)))
    (hdual : T.card ≤ m)
    (hcharge : D.card + (Finset.univ.filter (fun i => s(a i, b i) ∈ D)).card ≤ budget) :
    D.card + T.card ≤ budget + R.card := by
  have h := residual_matching_bound G D a b R hadj hmatch hR
  omega

end PEqualNP.Outside.L_meta_2962_aux.Matching
