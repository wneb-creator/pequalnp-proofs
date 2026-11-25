import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3566.Graph11

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

abbrev graph11 : SimpleGraph (Fin 11) :=
  PEqualNP.EdgeOwnership.edgeGraph 11
    [(0, 5), (1, 5), (2, 5), (0, 6), (3, 6), (4, 6),
     (1, 7), (3, 7), (1, 8), (4, 8), (2, 9), (3, 9), (2, 10), (4, 10)]

def left11 (i : Fin 5) : Fin 11 := ⟨i.val, by omega⟩

def right11 (i : Fin 5) : Fin 11 := ![5, 7, 9, 6, 8] i

theorem left11_injective : Function.Injective left11 := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun v : Fin 11 => v.val) h

theorem right11_injective : Function.Injective right11 := by
  decide

theorem matching_disjoint : ∀ i j, left11 i ≠ right11 j := by
  decide

theorem matching_edges : ∀ i, graph11.Adj (left11 i) (right11 i) := by
  decide

theorem cover_lower (S : Finset (Fin 11)) (hS : IsVertexCover graph11 S) :
    5 ≤ S.card :=
  matching_card_le_cover graph11 left11 right11 left11_injective right11_injective
    matching_disjoint matching_edges S hS

theorem bipartite :
    ∃ c : Fin 11 → Bool, ∀ u v, graph11.Adj u v → c u ≠ c v := by
  refine ⟨fun u => decide (u.val < 5), ?_⟩
  decide

theorem no_four_cycle : PEqualNP.TopForm.NoFourCycle graph11 := by
  decide

theorem edge_card : graph11.edgeFinset.card = 14 := by
  decide

def cover11 : Finset (Fin 11) := Finset.univ.filter fun i => i.val < 5

theorem cover11_is_cover : IsVertexCover graph11 cover11 := by
  unfold IsVertexCover
  decide

theorem cover11_card : cover11.card = 5 := by
  decide

end PEqualNP.Outside.L_meta_3566.Graph11

