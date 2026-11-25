import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.VertexCover
import PEqualNP.Defs

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

lemma exists_edge_cover_card_le {α : Type*} [DecidableEq α]
    (D : Finset (Sym2 α)) :
    ∃ S : Finset α, S.card ≤ D.card ∧
      ∀ u v : α, s(u, v) ∈ D → u ∈ S ∨ v ∈ S := by
  classical
  induction D using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp⟩
  | @insert e D he ih =>
    obtain ⟨S, hcard, hcover⟩ := ih
    induction e using Sym2.inductionOn with
    | _ a b =>
      refine ⟨insert a S, ?_, ?_⟩
      · have h := Finset.card_insert_le a S
        rw [Finset.card_insert_of_notMem he]
        omega
      · intro u v huv
        rcases Finset.mem_insert.mp huv with huv | huv
        · rcases Sym2.eq_iff.mp huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inl (Finset.mem_insert_self _ _)
          · exact Or.inr (Finset.mem_insert_self _ _)
        · rcases hcover u v huv with h | h
          · exact Or.inl (Finset.mem_insert_of_mem h)
          · exact Or.inr (Finset.mem_insert_of_mem h)

lemma core_cover_singleton_incidence {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit)
    (T T' : Finset (Fin n))
    (small : ∀ j ∈ PEqualNP.Core.maximalCores G C,
      (PEqualNP.TopForm.gammaE G C j).card ≤ 1)
    (hT : PEqualNP.MetaComplexity.NestedCover.IsMinCover G T)
    (hT' : PEqualNP.MetaComplexity.NestedCover.IsMinCover
      (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion
        (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T') :
    ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T.card ≤
      ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).card +
        (PEqualNP.Core.maximalCores G C).card + T'.card := by
  classical
  let M := PEqualNP.Core.maximalCores G C
  let D := M.biUnion (PEqualNP.TopForm.gammaE G C)
  let U := M.biUnion (PEqualNP.Core.coneSet n C)
  have hD : D.card ≤ M.card := by
    calc
      D.card ≤ ∑ j ∈ M, (PEqualNP.TopForm.gammaE G C j).card := Finset.card_biUnion_le
      _ ≤ ∑ j ∈ M, 1 := Finset.sum_le_sum fun j hj => small j hj
      _ = M.card := by simp
  have hM : M.card ≤ U.card := by
    apply Finset.card_le_card
    intro j hj
    exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_insert_self _ _⟩
  obtain ⟨S, hS, coverS⟩ := exists_edge_cover_card_le D
  apply core_cover_of_certificate G D U M.card S T T' hT.2
  · exact fun u v _ huv => coverS u v huv
  · exact hT'.1
  · omega

end PEqualNP.Outside.L_meta_2962_aux
