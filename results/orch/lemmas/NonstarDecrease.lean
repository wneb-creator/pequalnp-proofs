namespace PEqualNP.Outside.L_meta_4675.NonstarDecrease

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.TwoColour PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_4675.Pruning
open PEqualNP.Outside.L_meta_4675.ReaderPartition
open PEqualNP.Outside.L_meta_4675.RestoreStar
open PEqualNP.Outside.L_meta_4675.NonstarExplicit

lemma nonstar_repair_decreases (p l q r aWire j : ℕ) (side : Fin 2) (C : Circuit)
    (G : SimpleGraph (Fin (p+l))) [DecidableRel G.Adj]
    (E : Finset (Fin p × Fin l)) (A Q : Finset (Fin p)) (B P : Finset (Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (hAO : IsAO2 (p+l) C) (colour : ℕ → Bool) (hz : tCount (p+l) C colour = 0)
    (hcompute : ∀ x, circuitFun (p+l) C x = edgeValue E x)
    (hOldC : circuitFun (p+l) C = graphFun G ∅)
    (hqr : q < r) (hr : r < C.gates.length) (hread : p+l+q ∈ C.gates[r].inputs)
    (haWire : aWire < p+l+q)
    (hfactor : ∀ x : Fin (p+l) → Bool,
      (C.wires (List.ofFn x)).getD aWire false = decide (∃ a ∈ A, x (Fin.castAdd l a) = true))
    (hrectangle : ∀ x : Fin (p+l) → Bool,
      (C.wires (List.ofFn x)).getD (p+l+q) false = true ↔
        (∃ a ∈ A, x (Fin.castAdd l a) = true) ∧ (∃ b ∈ B, x (Fin.natAdd p b) = true))
    (hQ : 1 < Q.card) (hB : 1 < B.card) (hAQ : (A∩Q).Nonempty) (hP : P.Nonempty)
    (hdirty : ∃ a ∈ A, ∃ b ∈ B, (a,b) ∉ E)
    (hqand : (gateAt C q).op = GateOp.and) (hj : j < C.gates.length)
    (hjq : j ≠ q) (hjand : (gateAt C j).op = GateOp.and)
    (houtput : OrReaches (p+l) C C.output j)
    (hPpath : ∀ b ∈ P, Fin.natAdd p b ∈ orIn (p+l) C (opnd C j side))
    (hQpath : ∀ a ∈ Q, Fin.castAdd l a ∈ orIn (p+l) C (opnd C j (1-side)))
    (hreader : ∀ x : Fin (p+l) → Bool,
      (C.wires (List.ofFn x)).getD (p+l+j) false = true ↔
        (((∃ a ∈ A, x (Fin.castAdd l a) = true) ∧ (∃ b ∈ B, x (Fin.natAdd p b) = true)) ∨
          (∃ b ∈ P, x (Fin.natAdd p b) = true)) ∧ (∃ a ∈ Q, x (Fin.castAdd l a) = true)) :
    ∃ b1 : Fin l, (∀ a ∈ A, (a,b1) ∈ E) ∧
      let D := PEqualNP.Outside.L_meta_4675.StarAppendOptional.restoreStar (p+l)
        (pruned (p+l) q C) aWire (Fin.natAdd p b1).val
      IsAO2 (p+l) D ∧ tCount (p+l) D colour = 0 ∧ D.size ≤ C.size ∧
        circuitFun (p+l) D = circuitFun (p+l) C ∧ (junk G D).card < (junk G C).card := by
  have hqdirty : IsDirtyAnd (p+l) G C q := by
    obtain ⟨a,ha,b,hb,hab⟩ := hdirty
    let x := splitInput (pairVal a b)
    refine ⟨hqand,by omega,x,?_,?_⟩
    · change (C.wires (List.ofFn x)).getD (p+l+q) false = true
      apply (hrectangle x).mpr
      exact ⟨⟨a,ha,by simp [x,splitInput,pairVal]⟩,⟨b,hb,by simp [x,splitInput,pairVal]⟩⟩
    · rw [← hOldC,hcompute]
      simp [edgeValue,x,splitInput,pairVal,hab]
  obtain ⟨b1,hcol,hDA,hzD,hsD,hfD⟩ :=
    PEqualNP.Outside.L_meta_4675.NonstarPaths.nonstar_repair_from_paths
      p l q r aWire j side C E A Q B P hC4 hAO colour hz hcompute hqr hr hread haWire
      hfactor hrectangle hQ hB hAQ hP hdirty hqand hj hjq hjand houtput hPpath hQpath hreader
  refine ⟨b1,hcol,hDA,hzD,hsD,hfD,?_⟩
  exact PEqualNP.Outside.L_meta_4675.JunkDrop.prune_restore_junk_card_lt (p+l) q G C
    aWire (Fin.natAdd p b1).val hAO hqdirty hDA (hfD.trans hOldC)

end PEqualNP.Outside.L_meta_4675.NonstarDecrease
