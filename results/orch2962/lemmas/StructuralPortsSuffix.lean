namespace PEqualNP.Outside.L_meta_2962.Structural
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma input_port_count (U M : Finset ℕ) (hmu : M ⊆ U)
    (hread : ∀ i ∈ U \ M, ∃ j ∈ U, ∃ b : Fin 2, opnd C j b = n + i) :
    ((U ×ˢ (Finset.univ : Finset (Fin 2))).filter fun p => opnd C p.1 p.2 < n).card
      ≤ U.card + M.card := by
  classical
  let P := U ×ˢ (Finset.univ : Finset (Fin 2))
  let B := P.filter fun p => opnd C p.1 p.2 < n
  let I := P.filter fun p => ¬opnd C p.1 p.2 < n
  have hsub : U \ M ⊆ I.image (fun p => opnd C p.1 p.2 - n) := by
    intro i hi
    obtain ⟨j,hj,b,hb⟩ := hread i hi
    exact Finset.mem_image.mpr ⟨(j,b), by simp [I,P,hj,hb], by simp [hb]⟩
  have hcard : (U \ M).card ≤ I.card := (Finset.card_le_card hsub).trans (Finset.card_image_le)
  have hsum : B.card + I.card = 2 * U.card := by
    rw [show B.card + I.card = P.card from Finset.card_filter_add_card_filter_not (s := P) (fun p => opnd C p.1 p.2 < n)]
    simp [P, Nat.mul_comm]
  have hdiff := Finset.card_sdiff_add_card_eq_card hmu
  change B.card ≤ U.card + M.card
  omega

lemma cone_union_reader (ao : IsAO2 n C) {i : ℕ}
    (hi : i ∈ (maximalCores G C).biUnion (coneSet n C) \ maximalCores G C) :
    ∃ j ∈ (maximalCores G C).biUnion (coneSet n C), ∃ b : Fin 2,
      opnd C j b = n + i := by
  obtain ⟨hi,hnm⟩ := Finset.mem_sdiff.mp hi
  obtain ⟨c,hc,hic⟩ := Finset.mem_biUnion.mp hi
  have hcl := (mem_maximal.mp hc).1.1
  have hh : InCone n C i c := by
    rcases (mem_coneSet_iff n C c hcl i).mp hic with he | hh
    · exact False.elim (hnm (he ▸ hc))
    · exact hh
  obtain ⟨j,hj,hij⟩ := InCone_has_reader n C hcl hh
  have hjl : j < C.gates.length := Finset.mem_range.mp (coneSet_subset_range n C c hcl hj)
  obtain ⟨b,hb,he⟩ := List.getElem_of_mem hij
  have hbl : b < 2 := by rw [ao.2.2 _ (by rw [gateAt_eq_getElem C j hjl]; exact List.getElem_mem hjl)] at hb; exact hb
  refine ⟨j, Finset.mem_biUnion.mpr ⟨c,hc,hj⟩, ⟨b,hbl⟩, ?_⟩
  simpa [opnd, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb] using he

lemma core_input_ports (ao : IsAO2 n C) :
    ((((maximalCores G C).biUnion (coneSet n C)) ×ˢ (Finset.univ : Finset (Fin 2))).filter
      fun p => opnd C p.1 p.2 < n).card ≤
        ((maximalCores G C).biUnion (coneSet n C)).card + (maximalCores G C).card := by
  exact input_port_count _ _ maximal_subset_union (fun _ hi => cone_union_reader ao hi)

end PEqualNP.Outside.L_meta_2962.Structural
