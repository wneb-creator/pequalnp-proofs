import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2585.LeastNormalized

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2585.EdgeInvisible
open PEqualNP.Outside.L_meta_2585.normalization

lemma exists_least_normalized_essential (P L : ℕ)
    (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 (P + L) C)
    (hne : ∃ p l, I p l)
    (hfun : ∀ x : Fin (P + L) → Bool,
      circuitFun (P + L) C x =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true)) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (P + L) D ∧
      D.size ≤ C.size ∧ circuitFun (P + L) D = circuitFun (P + L) C ∧
      (∀ E : Circuit, PEqualNP.TopForm.IsAO2 (P + L) E →
        circuitFun (P + L) E = circuitFun (P + L) C → D.size ≤ E.size) ∧
      (∀ m < D.gates.length, ∀ a b : ℕ,
        D.gates[m]? = some ⟨GateOp.or, [a, b]⟩ →
        (PEqualNP.CircuitMoves.WireBelowOutput (P + L) D a ↔
          PEqualNP.CircuitMoves.WireBelowOutput (P + L) D b)) ∧
      (∀ (pre post : List Gate) (g : Gate), D.gates = pre ++ g :: post →
        ∃ p : Fin P, ∃ l : Fin L, I p l ∧
          circuitFun (P + L) (offGate pre post D.output)
            (fun i => decide (i = Fin.castAdd L p ∨ i = Fin.natAdd P l)) = false) := by
  classical
  let good : Circuit → Prop := fun E =>
    PEqualNP.TopForm.IsAO2 (P + L) E ∧ circuitFun (P + L) E = circuitFun (P + L) C
  have hex : ∃ k : ℕ, ∃ E : Circuit, good E ∧ E.size = k :=
    ⟨C.size, C, ⟨hAO, rfl⟩, rfl⟩
  obtain ⟨E, hE, hsizeE⟩ := Nat.find_spec hex
  have hminE : ∀ A : Circuit, good A → E.size ≤ A.size := by
    intro A hA
    rw [hsizeE]
    exact Nat.find_min' hex ⟨A, hA, rfl⟩
  have hEf : ∀ x : Fin (P + L) → Bool,
      circuitFun (P + L) E x =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true) := by
    intro x
    rw [hE.2]
    exact hfun x
  obtain ⟨D, hD, hs, hDf, hnorm⟩ := normalized_incidence P L I E hE.1
    (incidence_output_lt P L I E hne hEf) hEf
  have hsame : circuitFun (P + L) D = circuitFun (P + L) C := by
    funext x
    rw [hDf, hfun]
  have hminD : ∀ A : Circuit, PEqualNP.TopForm.IsAO2 (P + L) A →
      circuitFun (P + L) A = circuitFun (P + L) C → D.size ≤ A.size := by
    intro A hA hAf
    rw [hs]
    exact hminE A ⟨hA, hAf⟩
  refine ⟨D, hD, hminD C hAO rfl, hsame, hminD, hnorm, ?_⟩
  intro pre post g hgs
  have hsplit : atGate pre post g D.output = D := by
    unfold atGate
    rw [← hgs]
  apply PEqualNP.Outside.L_meta_2585.EdgeEssential.least_gate_output_essential
    P L I pre post g D.output
  · rw [hsplit]
    exact hD
  · exact hne
  · rw [hsplit]
    exact hDf
  · intro A hA hAf
    rw [hsplit]
    apply hminD A hA
    funext x
    rw [hAf, hfun]

end PEqualNP.Outside.L_meta_2585.LeastNormalized
