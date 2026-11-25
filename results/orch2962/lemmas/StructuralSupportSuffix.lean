namespace PEqualNP.Outside.L_meta_2962.Structural
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma gamma_endpoint_port (ao : IsAO2 n C) {e : Sym2 (Fin n)}
    (he : e ∈ (maximalCores G C).biUnion (gammaE G C)) (u : Fin n) (hu : u ∈ e) :
    ∃ i ∈ (maximalCores G C).biUnion (coneSet n C), ∃ b : Fin 2,
      opnd C i b = u.val := by
  obtain ⟨j,hj,hje⟩ := Finset.mem_biUnion.mp he
  obtain ⟨_,a,b,rfl,hv⟩ := Finset.mem_filter.mp hje
  simp only [Sym2.mem_iff] at hu
  rcases hu with hu | hu
  · subst u
    exact accepted_edge_endpoint_port ao hj a b hv
  · subst u
    apply accepted_edge_endpoint_port ao hj b a
    have heq : pairInput b a = pairInput a b := by funext t; simp [pairInput, or_comm]
    simpa only [heq] using hv

lemma supported_vertices_bound (ao : IsAO2 n C) (S : Finset (Fin n))
    (hs : ∀ u ∈ S, ∃ e ∈ (maximalCores G C).biUnion (gammaE G C), u ∈ e) :
    S.card ≤ ((maximalCores G C).biUnion (coneSet n C)).card +
      (maximalCores G C).card := by
  classical
  let U := (maximalCores G C).biUnion (coneSet n C)
  let P := (U ×ˢ (Finset.univ : Finset (Fin 2))).filter fun p => opnd C p.1 p.2 < n
  have hsub : S.image Fin.val ⊆ P.image (fun p => opnd C p.1 p.2) := by
    intro v hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨e,he,hue⟩ := hs u hu
    obtain ⟨i,hi,b,hb⟩ := gamma_endpoint_port ao he u hue
    exact Finset.mem_image.mpr ⟨(i,b), by simp [P,U,hi,hb], hb⟩
  have hS : (S.image Fin.val).card = S.card := Finset.card_image_of_injective S Fin.val_injective
  have hp : (P.image (fun p => opnd C p.1 p.2)).card ≤ P.card := Finset.card_image_le
  have h := Finset.card_le_card hsub
  have bound := core_input_ports (G := G) ao
  change P.card ≤ U.card + (maximalCores G C).card at bound
  rw [hS] at h
  exact (h.trans hp).trans bound

end PEqualNP.Outside.L_meta_2962.Structural
