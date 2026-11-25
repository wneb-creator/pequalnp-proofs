import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CircuitMoves

theorem PEqualNP.Outside.R_meta_2585_46
    (normalize : ∀ (n : ℕ) (C : Circuit), PEqualNP.TopForm.IsAO2 n C →
      ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ circuitFun n D = circuitFun n C ∧
        D.size ≤ C.size ∧ ∀ g < D.gates.length, WireBelowOutput n D (n + g) →
          ∀ j < D.gates.length, n + g ∈ (gateAt D j).inputs →
            (gateAt D j).op = GateOp.or ∧ WireBelowOutput n D (n + j))
    (charge : ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I] (C : Circuit),
      (∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' →
        ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      PEqualNP.TopForm.IsAO2 (P + L) C →
      (∀ z : Fin (P + L) → Bool, circuitFun (P + L) C z =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) →
      (∀ g < C.gates.length, WireBelowOutput (P + L) C (P + L + g) →
        ∀ j < C.gates.length, P + L + g ∈ (gateAt C j).inputs →
          (gateAt C j).op = GateOp.or ∧ WireBelowOutput (P + L) C (P + L + j)) →
      ∃ A : Finset (Fin P), ∃ B : Finset (Fin L),
        (∀ p l, I p l → p ∈ A ∨ l ∈ B) ∧
          (PEqualNP.ReadTwo.incid I).card + A.card + B.card - 1 ≤ C.size)
    (synthesize : ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I]
      (A : Finset (Fin P)) (B : Finset (Fin L)), (∀ p l, I p l → p ∈ A ∨ l ∈ B) →
      ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (P + L) D ∧
        (∀ z : Fin (P + L) → Bool, circuitFun (P + L) D z =
          decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
            z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) ∧
        D.size ≤ (PEqualNP.ReadTwo.incid I).card + A.card + B.card - 1 ∧
        PEqualNP.ReadK.IsReadK (P + L) D 1) :
    ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (P + L) C → (∀ z : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) C z = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (P + L) D ∧ (∀ y : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) D y = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ y (Fin.castAdd L p) = true ∧ y (Fin.natAdd P l) = true)) ∧ D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (P + L) D 1 := by
  intro P L I inst C hfour hC hf
  obtain ⟨D, hD, heq, hsize, hnorm⟩ := normalize (P + L) C hC
  have hfun : ∀ z : Fin (P + L) → Bool, circuitFun (P + L) D z =
      decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
        z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true) := by
    intro z
    rw [heq]
    exact hf z
  obtain ⟨A, B, hcover, hcost⟩ := charge P L I D hfour hD hfun hnorm
  obtain ⟨E, hE, hfunE, hcostE, hread⟩ := synthesize P L I A B hcover
  exact ⟨E, hE, hfunE, hcostE.trans (hcost.trans hsize), hread⟩
