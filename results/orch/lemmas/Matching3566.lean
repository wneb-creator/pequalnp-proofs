import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3566

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

abbrev heawood : SimpleGraph (Fin 14) :=
  PEqualNP.EdgeOwnership.edgeGraph 14
    [(0, 7), (1, 7), (3, 7), (1, 8), (2, 8), (4, 8),
     (2, 9), (3, 9), (5, 9), (3, 10), (4, 10), (6, 10),
     (4, 11), (5, 11), (0, 11), (5, 12), (6, 12), (1, 12),
     (6, 13), (0, 13), (2, 13)]

def heawoodLeft (i : Fin 7) : Fin 14 := ⟨i.val, by omega⟩

def heawoodRight (i : Fin 7) : Fin 14 := ⟨7 + i.val, by omega⟩

theorem heawoodLeft_injective : Function.Injective heawoodLeft := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun v : Fin 14 => v.val) h

theorem heawoodRight_injective : Function.Injective heawoodRight := by
  intro i j h
  apply Fin.ext
  have hval := congrArg Fin.val h
  simp only [heawoodRight] at hval
  omega

theorem heawood_matching_disjoint : ∀ i j, heawoodLeft i ≠ heawoodRight j := by
  intro i j h
  have hval := congrArg Fin.val h
  simp only [heawoodLeft, heawoodRight] at hval
  omega

theorem heawood_matching_edges : ∀ i, heawood.Adj (heawoodLeft i) (heawoodRight i) := by
  decide

theorem heawood_cover_lower (S : Finset (Fin 14)) (hS : IsVertexCover heawood S) :
    7 ≤ S.card :=
  matching_card_le_cover heawood heawoodLeft heawoodRight
    heawoodLeft_injective heawoodRight_injective heawood_matching_disjoint
    heawood_matching_edges S hS

theorem heawood_bipartite :
    ∃ c : Fin 14 → Bool, ∀ u v, heawood.Adj u v → c u ≠ c v := by
  refine ⟨fun u => decide (u.val < 7), ?_⟩
  decide

theorem heawood_no_four_cycle : PEqualNP.TopForm.NoFourCycle heawood := by
  decide

theorem heawood_edge_card : heawood.edgeFinset.card = 21 := by
  decide

def heawoodCover : Finset (Fin 14) := Finset.univ.filter fun i => i.val < 7

theorem heawood_cover : IsVertexCover heawood heawoodCover := by
  unfold IsVertexCover
  decide

theorem heawood_cover_card : heawoodCover.card = 7 := by
  decide

end PEqualNP.Outside.L_meta_3566
