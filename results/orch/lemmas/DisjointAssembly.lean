import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.VertexCover

namespace PEqualNP.Outside.L_meta_2962_aux

lemma disjoint_cost_assembly {ι α β γ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (I : Finset ι) (D : ι → Finset α) (S : ι → Finset β) (U : ι → Finset γ)
    (disjoint : (I : Set ι).PairwiseDisjoint U)
    (localCost : ∀ i ∈ I, (D i).card + (S i).card ≤ (U i).card + 1) :
    (I.biUnion D).card + (I.biUnion S).card ≤ (I.biUnion U).card + I.card := by
  calc
    (I.biUnion D).card + (I.biUnion S).card ≤
        (∑ i ∈ I, (D i).card) + ∑ i ∈ I, (S i).card :=
      Nat.add_le_add Finset.card_biUnion_le Finset.card_biUnion_le
    _ = ∑ i ∈ I, ((D i).card + (S i).card) := (Finset.sum_add_distrib).symm
    _ ≤ ∑ i ∈ I, ((U i).card + 1) := Finset.sum_le_sum localCost
    _ = (I.biUnion U).card + I.card := by
      rw [Finset.sum_add_distrib, Finset.card_biUnion disjoint]
      simp

lemma union_covers_deleted {n : ℕ} {ι : Type*}
    (G : SimpleGraph (Fin n)) (I : Finset ι)
    (D : ι → Finset (Sym2 (Fin n))) (S : ι → Finset (Fin n))
    (localCover : ∀ i ∈ I, ∀ u v : Fin n,
      G.Adj u v → s(u, v) ∈ D i → u ∈ S i ∨ v ∈ S i) :
    ∀ u v : Fin n, G.Adj u v → s(u, v) ∈ I.biUnion D →
      u ∈ I.biUnion S ∨ v ∈ I.biUnion S := by
  intro u v edge deleted
  rcases Finset.mem_biUnion.mp deleted with ⟨i, hi, hedge⟩
  rcases localCover i hi u v edge hedge with hu | hv
  · exact Or.inl (Finset.mem_biUnion.mpr ⟨i, hi, hu⟩)
  · exact Or.inr (Finset.mem_biUnion.mpr ⟨i, hi, hv⟩)

lemma cover_bound_of_disjoint_local_certificates {n : ℕ} {ι : Type*}
    (G : SimpleGraph (Fin n)) (I : Finset ι)
    (D : ι → Finset (Sym2 (Fin n))) (S : ι → Finset (Fin n))
    (U : ι → Finset ℕ) (T T' : Finset (Fin n))
    (minimal : ∀ V : Finset (Fin n),
      G.IsVertexCover (V : Set (Fin n)) → T.card ≤ V.card)
    (disjoint : (I : Set ι).PairwiseDisjoint U)
    (localCost : ∀ i ∈ I, (D i).card + (S i).card ≤ (U i).card + 1)
    (localCover : ∀ i ∈ I, ∀ u v : Fin n,
      G.Adj u v → s(u, v) ∈ D i → u ∈ S i ∨ v ∈ S i)
    (coverRest : (G.deleteEdges (I.biUnion D : Set (Sym2 (Fin n)))).IsVertexCover
      (T' : Set (Fin n))) :
    (I.biUnion D).card + T.card ≤ (I.biUnion U).card + I.card + T'.card := by
  have cover : G.IsVertexCover ((I.biUnion S ∪ T' : Finset (Fin n)) : Set (Fin n)) := by
    intro u v edge
    by_cases deleted : s(u, v) ∈ I.biUnion D
    · rcases union_covers_deleted G I D S localCover u v edge deleted with hu | hv
      · exact Or.inl (Finset.mem_union.mpr (Or.inl hu))
      · exact Or.inr (Finset.mem_union.mpr (Or.inl hv))
    · rcases coverRest (SimpleGraph.deleteEdges_adj.mpr ⟨edge, deleted⟩) with hu | hv
      · exact Or.inl (Finset.mem_union.mpr (Or.inr hu))
      · exact Or.inr (Finset.mem_union.mpr (Or.inr hv))
  have bound : T.card ≤ (I.biUnion S).card + T'.card :=
    (minimal _ cover).trans (Finset.card_union_le _ _)
  calc
    (I.biUnion D).card + T.card ≤
        (I.biUnion D).card + ((I.biUnion S).card + T'.card) :=
      Nat.add_le_add_left bound _
    _ = (I.biUnion D).card + (I.biUnion S).card + T'.card := (Nat.add_assoc _ _ _).symm
    _ ≤ (I.biUnion U).card + I.card + T'.card :=
      Nat.add_le_add_right (disjoint_cost_assembly I D S U disjoint localCost) _

end PEqualNP.Outside.L_meta_2962_aux
