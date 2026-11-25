import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3566.Graph10

open PEqualNP.MetaComplexity.CoverPromise

theorem matching_card_le_cover {n k : ℕ} (G : SimpleGraph (Fin n))
    (l r : Fin k → Fin n) (hl : Function.Injective l) (hr : Function.Injective r)
    (hdisj : ∀ i j, l i ≠ r j) (hedge : ∀ i, G.Adj (l i) (r i))
    (S : Finset (Fin n)) (hS : IsVertexCover G S) : k ≤ S.card := by
  classical
  let f : Fin k → Fin n := fun i => if l i ∈ S then l i else r i
  have hfmem (i : Fin k) : f i ∈ S := by
    by_cases hi : l i ∈ S
    · simp [f, hi]
    · simpa [f, hi] using (hS (l i) (r i) (hedge i)).resolve_left hi
  have hfinj : Function.Injective f := by
    intro i j hij
    by_cases hi : l i ∈ S <;> by_cases hj : l j ∈ S
    · exact hl (by simpa [f, hi, hj] using hij)
    · exact False.elim (hdisj i j (by simpa [f, hi, hj] using hij))
    · exact False.elim (hdisj j i (by simpa [f, hi, hj] using hij.symm))
    · exact hr (by simpa [f, hi, hj] using hij)
  have hcard := Finset.card_le_card_of_injOn (s := Finset.univ) (t := S) f
    (fun i _ => hfmem i) (fun i _ j _ h => hfinj h)
  simpa using hcard

abbrev graph10 : SimpleGraph (Fin 10) :=
  PEqualNP.EdgeOwnership.edgeGraph 10
    [(0, 4), (0, 5), (1, 6), (1, 7), (2, 4), (2, 6),
     (3, 5), (3, 7), (9, 0), (9, 1), (9, 8)]

def left10 (i : Fin 5) : Fin 10 := ![0, 1, 2, 3, 8] i

def right10 (i : Fin 5) : Fin 10 := ![4, 7, 6, 5, 9] i

theorem left10_injective : Function.Injective left10 := by
  decide

theorem right10_injective : Function.Injective right10 := by
  decide

theorem matching_disjoint : ∀ i j, left10 i ≠ right10 j := by
  decide

theorem matching_edges : ∀ i, graph10.Adj (left10 i) (right10 i) := by
  decide

theorem cover_lower (S : Finset (Fin 10)) (hS : IsVertexCover graph10 S) :
    5 ≤ S.card :=
  matching_card_le_cover graph10 left10 right10 left10_injective right10_injective
    matching_disjoint matching_edges S hS

theorem bipartite :
    ∃ c : Fin 10 → Bool, ∀ u v, graph10.Adj u v → c u ≠ c v := by
  refine ⟨fun u => decide (u.val < 4 ∨ u.val = 8), ?_⟩
  decide

theorem no_four_cycle : PEqualNP.TopForm.NoFourCycle graph10 := by
  decide

theorem edge_card : graph10.edgeFinset.card = 11 := by
  decide

def cover10 : Finset (Fin 10) := Finset.univ.filter fun i => i.val < 4 ∨ i.val = 8

theorem cover10_is_cover : IsVertexCover graph10 cover10 := by
  unfold IsVertexCover
  decide

theorem cover10_card : cover10.card = 5 := by
  decide

end PEqualNP.Outside.L_meta_3566.Graph10

