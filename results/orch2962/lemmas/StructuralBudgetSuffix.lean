namespace PEqualNP.Outside.L_meta_2962.Structural
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma port_budget_identity (U M : Finset ℕ) (hmu : M ⊆ U)
    (hread : ∀ i ∈ U \ M, ∃ j ∈ U, ∃ b : Fin 2, opnd C j b = n + i) :
    U.card + M.card =
      ((U ×ˢ (Finset.univ : Finset (Fin 2))).filter fun p => opnd C p.1 p.2 < n).card +
      (((U ×ˢ (Finset.univ : Finset (Fin 2))).filter fun p => ¬opnd C p.1 p.2 < n).card -
        (U \ M).card) := by
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
    rw [show B.card + I.card = P.card from
      Finset.card_filter_add_card_filter_not (s := P) (fun p => opnd C p.1 p.2 < n)]
    simp [P, Nat.mul_comm]
  have hdiff := Finset.card_sdiff_add_card_eq_card hmu
  change U.card + M.card = B.card + (I.card - (U \ M).card)
  omega

lemma core_port_budget_identity (ao : IsAO2 n C) :
    let U := (maximalCores G C).biUnion (coneSet n C)
    let M := maximalCores G C
    U.card + M.card =
      ((U ×ˢ (Finset.univ : Finset (Fin 2))).filter fun p => opnd C p.1 p.2 < n).card +
      (((U ×ˢ (Finset.univ : Finset (Fin 2))).filter fun p => ¬opnd C p.1 p.2 < n).card -
        (U \ M).card) := by
  exact port_budget_identity _ _ maximal_subset_union (fun _ hi => cone_union_reader ao hi)

end PEqualNP.Outside.L_meta_2962.Structural
