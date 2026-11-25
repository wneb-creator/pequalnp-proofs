import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_650_aux.ResidualCoverCounting

set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem edge_cover_small {n : ℕ} (U : Finset (Sym2 (Fin n))) :
    ∃ S : Finset (Fin n), S.card ≤ U.card ∧
      ∀ u v, s(u,v) ∈ U → u ∈ S ∨ v ∈ S := by
  classical
  induction U using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp⟩
  | @insert e U hnew ih =>
    obtain ⟨S, hS, cover⟩ := ih
    induction e using Sym2.ind with
    | _ u v =>
      refine ⟨insert u S, ?_, ?_⟩
      · have h := Finset.card_insert_le u S
        rw [Finset.card_insert_of_notMem hnew]
        omega
      · intro a b hab
        rcases Finset.mem_insert.mp hab with heq | hU
        · rcases Sym2.eq_iff.mp heq with ⟨ha, hb⟩ | ⟨ha, hb⟩
          · exact Or.inl (by simp [ha])
          · exact Or.inr (by simp [hb])
        · rcases cover a b hU with ha | hb
          · exact Or.inl (Finset.mem_insert_of_mem ha)
          · exact Or.inr (Finset.mem_insert_of_mem hb)

theorem cover_delete_any {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (U : Finset (Sym2 (Fin n))) (K : Finset (Fin n))
    (cover : (G.deleteEdges ↑U).IsVertexCover ↑K) :
    ∃ T : Finset (Fin n), G.IsVertexCover ↑T ∧ T.card ≤ K.card + U.card := by
  classical
  obtain ⟨S, hS, hcover⟩ := edge_cover_small U
  refine ⟨K ∪ S, ?_, (Finset.card_union_le K S).trans (by omega)⟩
  intro a b hab
  by_cases hu : s(a,b) ∈ U
  · rcases hcover a b hu with ha | hb
    · exact Or.inl (Finset.mem_union_right K ha)
    · exact Or.inr (Finset.mem_union_right K hb)
  · rcases cover (SimpleGraph.deleteEdges_adj.mpr ⟨hab, hu⟩) with ha | hb
    · exact Or.inl (Finset.mem_union_left S ha)
    · exact Or.inr (Finset.mem_union_left S hb)

theorem deleted_cover_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (d : ℕ) (degree : ∀ v : Fin n,
      (G.edgeFinset.filter fun e => v ∈ e).card ≤ d)
    (U : Finset (Sym2 (Fin n))) (K : Finset (Fin n))
    (cover : (G.deleteEdges ↑U).IsVertexCover ↑K) :
    G.edgeFinset.card ≤ U.card + d * K.card := by
  classical
  let incident := fun v : Fin n => G.edgeFinset.filter fun e => v ∈ e
  have sub : G.edgeFinset ⊆ U ∪ K.biUnion incident := by
    intro e he
    by_cases hu : e ∈ U
    · exact Finset.mem_union_left _ hu
    · apply Finset.mem_union_right
      induction e using Sym2.ind with
      | _ a b =>
        have hab := SimpleGraph.mem_edgeFinset.mp he
        have hd : (G.deleteEdges ↑U).Adj a b := SimpleGraph.deleteEdges_adj.mpr ⟨hab, hu⟩
        rcases cover hd with ha | hb
        · exact Finset.mem_biUnion.mpr ⟨a, ha, by simp [incident, he]⟩
        · exact Finset.mem_biUnion.mpr ⟨b, hb, by simp [incident, he]⟩
  have h1 := Finset.card_le_card sub
  have h2 := Finset.card_union_le U (K.biUnion incident)
  have h3 := Finset.card_biUnion_le
    (s := K) (t := incident)
  have h4 : (∑ v ∈ K, (incident v).card) ≤ d * K.card := by
    calc
      (∑ v ∈ K, (incident v).card) ≤ ∑ _v ∈ K, d :=
        Finset.sum_le_sum (fun v hv => degree v)
      _ = d * K.card := by simp [Nat.mul_comm]
  omega

end PEqualNP.Outside.L_meta_650_aux.ResidualCoverCounting
