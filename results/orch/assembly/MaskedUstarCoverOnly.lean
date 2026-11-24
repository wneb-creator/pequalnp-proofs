namespace PEqualNP.Outside.L_meta_1477.MaskedFamilyLowerBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership OneJunk Structural StructuralMasks MaskGrouping

lemma masked_ustar_cover {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : P2.AO n C) (g : Fin t → ℕ)
    (hgj : ∀ i, g i ∈ junk G C)
    (hpure : ∀ i, ∀ b : Fin 2, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (opnd C (g i) b) (n + k))
    (hdis : ∀ i, Disjoint (side (n := n) C (g i) 0) (side C (g i) 1))
    (hmask : ∀ u v : Fin n, s(u,v) ∈ Ustar G C →
      ∃ i : Fin t, ∃ c ∈ wmax G C (g i), (c = u ∨ c = v) ∧
        gateVal n C (g i) (pairInput u v) = true) :
    ∀ e ∈ Ustar G C, e ∉ PEqualNP.TopForm.starEdges G C ∧
      ∃ i : Fin t, ∃ c ∈ cleanCenters G (side (n := n) C (g i) 0) (side C (g i) 1),
        e ∈ MaskGrouping.starEdges (side (n := n) C (g i) 0) (side C (g i) 1) c := by
  intro e
  induction e using Sym2.inductionOn with
  | hf u v =>
    intro he
    obtain ⟨i,c,hc,hce,hfire⟩ := hmask u v he
    obtain ⟨hi,hop,_⟩ := (P1.junk_iff G C (g i)).mp (hgj i)
    have hprod := ActualCommonMasks.pure_product_value C hAO (g i) hi hop (hpure i)
    have hclean : CleanMask G (side (n := n) C (g i) 0) (side C (g i) 1) c := by
      have hcm := Finset.mem_filter.mp hc |>.2
      intro x hx hcx
      have hval : gateVal n C (g i) x = true := by rw [hprod]; exact hx
      have hf := hcm x hval hcx
      simpa only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_true_eq] using hf
    have hadj : G.Adj u v := by
      have hmem := (Finset.mem_sdiff.mp he).1
      exact (G.mem_edgeSet).mp ((SimpleGraph.mem_edgeFinset).mp hmem)
    have hfire' : productValue (side (n := n) C (g i) 0) (side C (g i) 1)
        (pairInput u v) = true := by rw [← hprod]; exact hfire
    have hpair : pairInput u v c = true := by
      simpa only [pairInput, decide_eq_true_eq] using hce
    obtain ⟨hcenter,hstar⟩ := MaskGrouping.effective_mask_pair_covered G _ _ (hdis i)
      u v c hadj hfire' hpair hclean
    exact ⟨(Finset.mem_sdiff.mp he).2, i, c, hcenter, hstar⟩

end PEqualNP.Outside.L_meta_1477.MaskedFamilyLowerBound
