import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1532 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (U : Finset (Sym2 (Fin n))) (x : Fin n), (∀ e ∈ U, x ∈ e) →
    ∀ (K'' : Finset (Fin n)), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K'' →
    ∀ (K : Finset (Fin n)), PEqualNP.MetaComplexity.NestedCover.IsMinCover G K →
    K.card ≤ K''.card + 1 := by
  classical
  intro n G U x hU K'' hK'' K hK
  have hc'' : ∀ v w : Fin n, (G.deleteEdges ↑U).Adj v w → v ∈ K'' ∨ w ∈ K'' := by
    intro v w h
    have := hK''.1 h
    simpa using this
  have hcov : G.IsVertexCover ((insert x K'' : Finset (Fin n)) : Set (Fin n)) := by
    intro v w hvw
    by_cases he : s(v, w) ∈ U
    · have hx := hU _ he
      rw [Sym2.mem_iff] at hx
      rcases hx with rfl | rfl
      · left; simp
      · right; simp
    · have hadj : (G.deleteEdges ↑U).Adj v w := by
        rw [SimpleGraph.deleteEdges_adj]
        exact ⟨hvw, by simpa using he⟩
      rcases hc'' v w hadj with h | h
      · left; simp [h]
      · right; simp [h]
  have := hK.2 (insert x K'') hcov
  exact this.trans (Finset.card_insert_le x K'')
