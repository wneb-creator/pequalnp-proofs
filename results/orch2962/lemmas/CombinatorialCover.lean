import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2962_aux.Combinatorial

open PEqualNP.MetaComplexity.NestedCover

variable {n : ℕ} (G : SimpleGraph (Fin n))

def CoversDeleted (D : Finset (Sym2 (Fin n))) (S : Finset (Fin n)) : Prop :=
  ∀ u v, G.Adj u v → s(u, v) ∈ D → u ∈ S ∨ v ∈ S

theorem cover_union (D : Finset (Sym2 (Fin n))) (S R : Finset (Fin n))
    (hS : CoversDeleted G D S)
    (hR : (G.deleteEdges (D : Set (Sym2 (Fin n)))).IsVertexCover
      (R : Set (Fin n))) : G.IsVertexCover ((S ∪ R : Finset (Fin n)) : Set (Fin n)) := by
  intro u v huv
  by_cases he : s(u, v) ∈ D
  · rcases hS u v huv he with hu | hv
    · exact Or.inl (Finset.mem_union_left R hu)
    · exact Or.inr (Finset.mem_union_left R hv)
  · have hdel : (G.deleteEdges (D : Set (Sym2 (Fin n)))).Adj u v := by
      rw [SimpleGraph.deleteEdges_adj]
      exact ⟨huv, he⟩
    rcases hR hdel with hu | hv
    · exact Or.inl (Finset.mem_union_right S hu)
    · exact Or.inr (Finset.mem_union_right S hv)

theorem cover_extension_bound (D : Finset (Sym2 (Fin n)))
    (T R S : Finset (Fin n)) (hT : IsMinCover G T)
    (hR : (G.deleteEdges (D : Set (Sym2 (Fin n)))).IsVertexCover
      (R : Set (Fin n)))
    (hS : CoversDeleted G D S) : T.card ≤ S.card + R.card := by
  exact (hT.2 (S ∪ R) (cover_union G D S R hS hR)).trans
    (Finset.card_union_le S R)

theorem core_budget_sufficient (D : Finset (Sym2 (Fin n)))
    (T R S : Finset (Fin n)) (budget : ℕ) (hT : IsMinCover G T)
    (hR : (G.deleteEdges (D : Set (Sym2 (Fin n)))).IsVertexCover
      (R : Set (Fin n)))
    (hS : CoversDeleted G D S) (hbudget : D.card + S.card ≤ budget) :
    D.card + T.card ≤ budget + R.card := by
  have h := cover_extension_bound G D T R S hT hR hS
  omega

theorem relative_cover_union (D : Finset (Sym2 (Fin n))) (S R : Finset (Fin n))
    (hS : ∀ u v, G.Adj u v → s(u, v) ∈ D →
      u ∉ R → v ∉ R → u ∈ S ∨ v ∈ S)
    (hR : (G.deleteEdges (D : Set (Sym2 (Fin n)))).IsVertexCover
      (R : Set (Fin n))) : G.IsVertexCover ((S ∪ R : Finset (Fin n)) : Set (Fin n)) := by
  intro u v huv
  by_cases hu : u ∈ R
  · exact Or.inl (Finset.mem_union_right S hu)
  by_cases hv : v ∈ R
  · exact Or.inr (Finset.mem_union_right S hv)
  have he : s(u, v) ∈ D := by
    by_contra he
    have hdel : (G.deleteEdges (D : Set (Sym2 (Fin n)))).Adj u v := by
      rw [SimpleGraph.deleteEdges_adj]
      exact ⟨huv, he⟩
    exact (hR hdel).elim hu hv
  rcases hS u v huv he hu hv with h | h
  · exact Or.inl (Finset.mem_union_left R h)
  · exact Or.inr (Finset.mem_union_left R h)

theorem relative_core_budget_sufficient (D : Finset (Sym2 (Fin n)))
    (T R S : Finset (Fin n)) (budget : ℕ) (hT : IsMinCover G T)
    (hR : (G.deleteEdges (D : Set (Sym2 (Fin n)))).IsVertexCover
      (R : Set (Fin n)))
    (hS : ∀ u v, G.Adj u v → s(u, v) ∈ D →
      u ∉ R → v ∉ R → u ∈ S ∨ v ∈ S)
    (hbudget : D.card + S.card ≤ budget) : D.card + T.card ≤ budget + R.card := by
  have h := (hT.2 (S ∪ R) (relative_cover_union G D S R hS hR)).trans
    (Finset.card_union_le S R)
  omega

end PEqualNP.Outside.L_meta_2962_aux.Combinatorial
