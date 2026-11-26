import PEqualNP.Defs

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_2796_1
    (hBuild : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (201 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → x1 % (2 : ℕ) = (0 : ℕ) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x2 + x2) x10 ∧ PEqualNP.ReadK.IsReadK (x2 + x2) x10 (2 : ℕ) ∧ x10.size ≤ (2 : ℕ) * x2)
    (hSound : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (201 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → x1 % (2 : ℕ) = (0 : ℕ) → ∀ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x2 + x2) x10 → PEqualNP.ReadK.IsReadK (x2 + x2) x10 (2 : ℕ) → x10.size ≤ (2 : ℕ) * x2 → ∀ (x11 : Fin (x2 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x2 + x2) x10 x11 = Bool.true → ∃ (x12 : Fin x2) (x13 : Fin x2), x3 x12 x13 ∧ x11 (Fin.castAdd x2 x12) = Bool.true ∧ x11 (Fin.natAdd x2 x13) = Bool.true)
    (hComplete : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (201 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → x1 % (2 : ℕ) = (0 : ℕ) → ∀ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x2 + x2) x10 → PEqualNP.ReadK.IsReadK (x2 + x2) x10 (2 : ℕ) → x10.size ≤ (2 : ℕ) * x2 → ∀ (x11 : Fin (x2 + x2) → Bool), (∃ (x12 : Fin x2) (x13 : Fin x2), x3 x12 x13 ∧ x11 (Fin.castAdd x2 x12) = Bool.true ∧ x11 (Fin.natAdd x2 x13) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x10 x11 = Bool.true) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3], (201 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) → x1 % (2 : ℕ) = (0 : ℕ) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x2 + x2) x10 ∧ (∀ (x11 : Fin (x2 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x2 + x2) x10 x11 = Decidable.decide (∃ (x12 : Fin x2) (x13 : Fin x2), x3 x12 x13 ∧ x11 (Fin.castAdd x2 x12) = Bool.true ∧ x11 (Fin.natAdd x2 x13) = Bool.true)) ∧ PEqualNP.ReadK.IsReadK (x2 + x2) x10 (2 : ℕ) ∧ x10.size ≤ (2 : ℕ) * x2 := by
  intro x1 x2 x3 _ hq hN hCard hUniq hEven
  obtain ⟨x10, hAO2, hRead, hSize⟩ := hBuild x1 x2 x3 hq hN hCard hUniq hEven
  refine ⟨x10, hAO2, ?_, hRead, hSize⟩
  intro x11
  let P : Prop := ∃ (x12 : Fin x2) (x13 : Fin x2), x3 x12 x13 ∧ x11 (Fin.castAdd x2 x12) = Bool.true ∧ x11 (Fin.natAdd x2 x13) = Bool.true
  have hS : P → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x10 x11 = Bool.true := by
    intro hP
    exact hComplete x1 x2 x3 hq hN hCard hUniq hEven x10 hAO2 hRead hSize x11 hP
  have hT : PEqualNP.MetaComplexity.circuitFun (x2 + x2) x10 x11 = Bool.true → P := by
    intro hTrue
    exact hSound x1 x2 x3 hq hN hCard hUniq hEven x10 hAO2 hRead hSize x11 hTrue
  cases hVal : PEqualNP.MetaComplexity.circuitFun (x2 + x2) x10 x11 with
  | false =>
      have hNotP : ¬ P := by
        intro hP
        have hTrue : PEqualNP.MetaComplexity.circuitFun (x2 + x2) x10 x11 = Bool.true := hS hP
        have : Bool.false = Bool.true := hVal.symm.trans hTrue
        cases this
      have hDec : Decidable.decide P = Bool.false := by
        by_cases hP : P
        · exact False.elim (hNotP hP)
        · simp [hP]
      exact Eq.symm hDec
  | true =>
      have hP : P := hT hVal
      have hDec : Decidable.decide P = Bool.true := by simp [hP]
      exact Eq.symm hDec
