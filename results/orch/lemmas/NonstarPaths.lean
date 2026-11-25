namespace PEqualNP.Outside.L_meta_4675.NonstarPaths

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.TwoColour PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_4675.Pruning
open PEqualNP.Outside.L_meta_4675.ReaderPartition
open PEqualNP.Outside.L_meta_4675.RestoreStar
open PEqualNP.Outside.L_meta_4675.NonstarExplicit

lemma nonstar_repair_from_paths (p l q r aWire j : ℕ) (side : Fin 2) (C : Circuit)
    (E : Finset (Fin p × Fin l)) (A Q : Finset (Fin p)) (B P : Finset (Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (hAO : IsAO2 (p+l) C) (colour : ℕ → Bool) (hz : tCount (p+l) C colour = 0)
    (hcompute : ∀ x, circuitFun (p+l) C x = edgeValue E x)
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
        circuitFun (p+l) D = circuitFun (p+l) C := by
  have hconditions := (PEqualNP.Outside.L_meta_4675.ReaderSemantics.reader_below_iff E A Q B P).mp
    (by
      intro y hy
      have hv : PEqualNP.BlindGate.wireValue C (p+l) (splitInput y) (p+l+j) = true :=
        (hreader (splitInput y)).mpr (by
          simpa [PEqualNP.Outside.L_meta_4675.ReaderSemantics.readerValue,
            PEqualNP.Outside.L_meta_4675.ReaderSemantics.pointsOn,
            PEqualNP.Outside.L_meta_4675.ReaderSemantics.linesOn, splitInput] using hy)
      have hout := PEqualNP.Outside.L_meta_4675.MaskingNext.orReaches_true
        (p+l) C hAO (splitInput y) j hv C.output houtput
      change circuitFun (p+l) C (splitInput y) = true at hout
      rw [hcompute] at hout
      simpa [edgeValue, PEqualNP.Outside.L_meta_4675.ReaderSemantics.graphValue, splitInput] using hout)
  apply nonstar_prune_restore p l q r aWire C E A Q B P hC4 hAO colour hz hcompute
    hqr hr hread haWire hfactor hrectangle hQ hB hAQ hP hconditions.1 hconditions.2 hdirty
  intro a ha b hb
  let x := splitInput (pairVal a b)
  have hxa : x (Fin.castAdd l a) = true := by simp [x, splitInput, pairVal]
  have hxb : x (Fin.natAdd p b) = true := by simp [x, splitInput, pairVal]
  fin_cases side
  · exact forced_output_of_reader_pair (p+l) q C hAO hqand j hj hjq hjand houtput x
      (Fin.natAdd p b) (Fin.castAdd l a) (hPpath b hb) (by simpa using hQpath a ha) hxb hxa
  · exact forced_output_of_reader_pair (p+l) q C hAO hqand j hj hjq hjand houtput x
      (Fin.castAdd l a) (Fin.natAdd p b) (by simpa using hQpath a ha) (hPpath b hb) hxa hxb

end PEqualNP.Outside.L_meta_4675.NonstarPaths
