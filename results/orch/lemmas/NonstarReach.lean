namespace PEqualNP.Outside.L_meta_4675.NonstarReach

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.TwoColour PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_4675.Pruning
open PEqualNP.Outside.L_meta_4675.ReaderPartition
open PEqualNP.Outside.L_meta_4675.RestoreStar
open PEqualNP.Outside.L_meta_4675.NonstarExplicit

lemma nonstar_reach_decreases (p l q r aWire j : ℕ) (side : Fin 2) (C : Circuit)
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
    (hGreach : OrReaches (p+l) C (opnd C j side) q) :
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
  have hreader : ∀ x : Fin (p+l) → Bool,
      (((∃ a ∈ A, x (Fin.castAdd l a) = true) ∧ (∃ b ∈ B, x (Fin.natAdd p b) = true)) ∨
        (∃ b ∈ P, x (Fin.natAdd p b) = true)) ∧ (∃ a ∈ Q, x (Fin.castAdd l a) = true) →
      PEqualNP.BlindGate.wireValue C (p+l) x (p+l+j) = true := by
    intro x hx
    obtain ⟨hleft,a,ha,hxa⟩ := hx
    have hv := PEqualNP.Outside.L_meta_4675.MaskingNext.orIn_true (p+l) C hAO x
      (opnd C j (1-side)) (Fin.castAdd l a) (hQpath a ha) hxa
    have hu : PEqualNP.BlindGate.wireValue C (p+l) x (opnd C j side) = true := by
      rcases hleft with hg | ⟨b,hb,hxb⟩
      · exact PEqualNP.Outside.L_meta_4675.MaskingNext.orReaches_true (p+l) C hAO x q
          ((hrectangle x).mpr hg) _ hGreach
      · exact PEqualNP.Outside.L_meta_4675.MaskingNext.orIn_true (p+l) C hAO x
          (opnd C j side) (Fin.natAdd p b) (hPpath b hb) hxb
    have hmem : gateAt C j ∈ C.gates := by
      rw [PEqualNP.Outside.L_meta_4675.MaskingNext.gateAt_eq_getElem C j hj]
      exact List.getElem_mem hj
    obtain ⟨u,v,huv⟩ := List.length_eq_two.mp (hAO.2.2 _ hmem)
    rw [PEqualNP.Outside.L_meta_4675.MaskingNext.wireValue_gate (p+l) C x j hj hAO.2.1,
      hjand,huv]
    fin_cases side
    · simpa [opnd,huv,GateOp.eval] using And.intro hu hv
    · simpa [opnd,huv,GateOp.eval,and_comm] using And.intro hu hv
  have hconditions := (PEqualNP.Outside.L_meta_4675.ReaderSemantics.reader_below_iff E A Q B P).mp
    (by
      intro y hy
      have hv := hreader (splitInput y) (by
        simpa [PEqualNP.Outside.L_meta_4675.ReaderSemantics.readerValue,
          PEqualNP.Outside.L_meta_4675.ReaderSemantics.pointsOn,
          PEqualNP.Outside.L_meta_4675.ReaderSemantics.linesOn,splitInput] using hy)
      have hout := PEqualNP.Outside.L_meta_4675.MaskingNext.orReaches_true
        (p+l) C hAO (splitInput y) j hv C.output houtput
      change circuitFun (p+l) C (splitInput y) = true at hout
      rw [hcompute] at hout
      simpa [edgeValue,PEqualNP.Outside.L_meta_4675.ReaderSemantics.graphValue,splitInput] using hout)
  have hbasePreserved : ∀ a ∈ Q, ∀ b ∈ P,
      (forcedValues (p+l) q C (List.ofFn (splitInput (pairVal a b)))).getD C.output false = true := by
    intro a ha b hb
    let x := splitInput (pairVal a b)
    have hxa : x (Fin.castAdd l a) = true := by simp [x,splitInput,pairVal]
    have hxb : x (Fin.natAdd p b) = true := by simp [x,splitInput,pairVal]
    fin_cases side
    · exact forced_output_of_reader_pair (p+l) q C hAO hqand j hj hjq hjand houtput x
        (Fin.natAdd p b) (Fin.castAdd l a) (hPpath b hb) (by simpa using hQpath a ha) hxb hxa
    · exact forced_output_of_reader_pair (p+l) q C hAO hqand j hj hjq hjand houtput x
        (Fin.castAdd l a) (Fin.natAdd p b) (by simpa using hQpath a ha) (hPpath b hb) hxa hxb
  obtain ⟨b1,hcol,hDA,hzD,hsD,hfD⟩ :=
    nonstar_prune_restore p l q r aWire C E A Q B P hC4 hAO colour hz hcompute
      hqr hr hread haWire hfactor hrectangle hQ hB hAQ hP hconditions.1 hconditions.2 hdirty hbasePreserved
  refine ⟨b1,hcol,hDA,hzD,hsD,hfD,?_⟩
  exact PEqualNP.Outside.L_meta_4675.JunkDrop.prune_restore_junk_card_lt (p+l) q G C
    aWire (Fin.natAdd p b1).val hAO hqdirty hDA (hfD.trans hOldC)

end PEqualNP.Outside.L_meta_4675.NonstarReach
