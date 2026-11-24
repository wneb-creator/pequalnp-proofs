namespace PEqualNP.Outside.L_meta_1477.ActualCleanCenters

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership OneJunk Structural StructuralMasks MaskGrouping

lemma effective_centers_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (A B : Finset (Fin n)) (hdis : Disjoint A B)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hprod : ∀ x : Fin n → Bool, gateVal n C g x = productValue A B x) :
    FirstLayerEffective.effectiveCenters G C g = cleanCenters G A B := by
  classical
  ext c
  rw [MaskGrouping.centers_exact_effective G A B hdis hA hB c]
  simp only [FirstLayerEffective.effectiveCenters, Finset.mem_filter, wmax, Finset.mem_univ,
    true_and, hprod, CleanMask, EffectiveMask, graphFun, Finset.notMem_empty, false_and,
    exists_false, decide_false, Bool.false_or, decide_eq_true_eq, pairInput]
  aesop

lemma pure_effective_centers_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : P2.AO n C) (g : ℕ) (hg : g < C.gates.length)
    (hop : (gateAt C g).op = GateOp.and)
    (hpure : ∀ b : Fin 2, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (opnd C g b) (n + k))
    (hdis : Disjoint (side (n := n) C g 0) (side C g 1))
    (hA : (side (n := n) C g 0).Nonempty) (hB : (side (n := n) C g 1).Nonempty) :
    FirstLayerEffective.effectiveCenters G C g =
      cleanCenters G (side (n := n) C g 0) (side C g 1) :=
  effective_centers_eq G C g _ _ hdis hA hB (ActualCommonMasks.pure_product_value C hAO g hg hop hpure)

lemma two_clean_centers_of_effective {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hAO : P2.AO n C) (g : ℕ) (hg : g < C.gates.length)
    (hop : (gateAt C g).op = GateOp.and)
    (hpure : ∀ b : Fin 2, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ P2.OrR n C (opnd C g b) (n + k))
    (hdis : Disjoint (side (n := n) C g 0) (side C g 1))
    (hA : 2 ≤ (side (n := n) C g 0).card) (hB : 2 ≤ (side (n := n) C g 1).card)
    (heff : 2 ≤ (FirstLayerEffective.effectiveCenters G C g).card) :
    (cleanCenters G (side (n := n) C g 0) (side C g 1)).card = 2 := by
  have hAne : (side (n := n) C g 0).Nonempty := Finset.card_pos.mp (by omega)
  have hBne : (side (n := n) C g 1).Nonempty := Finset.card_pos.mp (by omega)
  rw [pure_effective_centers_eq G C hAO g hg hop hpure hdis hAne hBne] at heff
  exact Nat.le_antisymm (cleanCenters_card_le_two G hG _ _ hA hB) heff

end PEqualNP.Outside.L_meta_1477.ActualCleanCenters
