import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2585.K5ReadOne

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma small_witness_contradicts_posted
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 15 C)
    (hcomp : ∀ z : Fin 15 → Bool, PEqualNP.MetaComplexity.circuitFun 15 C z =
      decide (∃ p : Fin 5, ∃ l : Fin 10, I p l ∧
        z (Fin.castAdd 10 p) = true ∧ z (Fin.natAdd 5 l) = true))
    (hsmall : C.size < 24)
    (hposted : ∀ (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (P + L) C → (∀ z : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) C z = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (P + L) D ∧ (∀ y : Fin (P + L) → Bool, PEqualNP.MetaComplexity.circuitFun (P + L) D y = decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧ y (Fin.castAdd L p) = true ∧ y (Fin.natAdd P l) = true)) ∧ D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (P + L) D 1) : False := by
  have hc4 : ∀ p p' : Fin 5, ∀ l l' : Fin 10,
      p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l') := by decide
  obtain ⟨D, hD, hDf, hs, hread⟩ := hposted 5 10 I C hc4 hAO hcomp
  have hlower := read_one_lower_bound D hD hDf hread
  omega

end PEqualNP.Outside.L_meta_2585.K5ReadOne
