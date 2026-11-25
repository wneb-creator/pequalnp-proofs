import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9811.StarOutside

lemma incident_edges_avoiding_neighbor {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (b z : Fin n) (U : Finset (Sym2 (Fin n)))
    (hdegree : G.degree b ≤ 3) (hbz : G.Adj b z)
    (hgraph : U ⊆ G.edgeFinset)
    (hincident : ∀ e ∈ U, b ∈ e)
    (havoid : ∀ e ∈ U, z ∉ e) : U.card ≤ 2 := by
  classical
  have he : s(b, z) ∈ G.incidenceFinset b := by
    simp [G.incidenceFinset_eq_filter, hbz]
  have hnot : s(b, z) ∉ U := by
    intro h
    exact havoid _ h (by simp)
  have hsub : insert s(b, z) U ⊆ G.incidenceFinset b := by
    intro e heU
    rcases Finset.mem_insert.mp heU with rfl | heU
    · exact he
    · rw [G.incidenceFinset_eq_filter]
      exact Finset.mem_filter.mpr ⟨hgraph heU, hincident e heU⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot, G.card_incidenceFinset_eq_degree] at hcard
  omega

end PEqualNP.Outside.L_meta_9811.StarOutside
