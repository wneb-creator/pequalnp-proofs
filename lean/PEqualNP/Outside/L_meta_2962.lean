import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.VertexCover

namespace PEqualNP.Outside.L_meta_2962_aux

lemma cover_extension {n : ℕ} (G : SimpleGraph (Fin n))
    (D : Finset (Sym2 (Fin n))) (S T' : Finset (Fin n))
    (coverD : ∀ u v : Fin n, G.Adj u v → s(u, v) ∈ D → u ∈ S ∨ v ∈ S)
    (coverRest : (G.deleteEdges (D : Set (Sym2 (Fin n)))).IsVertexCover
      (T' : Set (Fin n))) :
    G.IsVertexCover ((S ∪ T' : Finset (Fin n)) : Set (Fin n)) := by
  intro u v edge
  by_cases deleted : s(u, v) ∈ D
  · rcases coverD u v edge deleted with h | h
    · exact Or.inl (Finset.mem_union.mpr (Or.inl h))
    · exact Or.inr (Finset.mem_union.mpr (Or.inl h))
  · have rest : (G.deleteEdges (D : Set (Sym2 (Fin n)))).Adj u v :=
      SimpleGraph.deleteEdges_adj.mpr ⟨edge, deleted⟩
    rcases coverRest rest with h | h
    · exact Or.inl (Finset.mem_union.mpr (Or.inr h))
    · exact Or.inr (Finset.mem_union.mpr (Or.inr h))

lemma minimum_cover_delete_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (D : Finset (Sym2 (Fin n))) (S T T' : Finset (Fin n))
    (minimal : ∀ V : Finset (Fin n), G.IsVertexCover (V : Set (Fin n)) → T.card ≤ V.card)
    (coverD : ∀ u v : Fin n, G.Adj u v → s(u, v) ∈ D → u ∈ S ∨ v ∈ S)
    (coverRest : (G.deleteEdges (D : Set (Sym2 (Fin n)))).IsVertexCover
      (T' : Set (Fin n))) :
    T.card ≤ S.card + T'.card := by
  exact (minimal (S ∪ T') (cover_extension G D S T' coverD coverRest)).trans
    (Finset.card_union_le S T')

lemma core_cover_of_certificate {n : ℕ} (G : SimpleGraph (Fin n))
    (D : Finset (Sym2 (Fin n))) (U : Finset ℕ) (mc : ℕ)
    (S T T' : Finset (Fin n))
    (minimal : ∀ V : Finset (Fin n), G.IsVertexCover (V : Set (Fin n)) → T.card ≤ V.card)
    (coverD : ∀ u v : Fin n, G.Adj u v → s(u, v) ∈ D → u ∈ S ∨ v ∈ S)
    (coverRest : (G.deleteEdges (D : Set (Sym2 (Fin n)))).IsVertexCover
      (T' : Set (Fin n)))
    (cost : D.card + S.card ≤ U.card + mc) :
    D.card + T.card ≤ U.card + mc + T'.card := by
  calc
    D.card + T.card ≤ D.card + (S.card + T'.card) :=
      Nat.add_le_add_left (minimum_cover_delete_bound G D S T T' minimal coverD coverRest) _
    _ = D.card + S.card + T'.card := (Nat.add_assoc _ _ _).symm
    _ ≤ U.card + mc + T'.card := Nat.add_le_add_right cost _

end PEqualNP.Outside.L_meta_2962_aux
