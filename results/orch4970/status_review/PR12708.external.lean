import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4970_7
    (h1 : ∀ (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' → ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) → PEqualNP.TopForm.IsAO2 (p + l) C → (∀ x : Fin (p + l) → Bool, PEqualNP.MetaComplexity.circuitFun (p + l) C x = decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) → PEqualNP.TwoColour.tCount (p + l) C (fun i => decide (p ≤ i)) = 0 → (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E → (∃ (j : ℕ) (Q : Finset (Fin l)), j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ Q.card ∧ b ∈ Q ∧ (∀ b' ∈ Q, (a, b') ∈ E) ∧ ∀ x : Fin (p + l) → Bool, (C.wires (List.ofFn x)).getD (p + l + j) false = decide (∃ b' ∈ Q, x (Fin.natAdd p b') = true)) ∨ (∃ (j : ℕ) (P : Finset (Fin p)), j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ P.card ∧ a ∈ P ∧ (∀ a' ∈ P, (a', b) ∈ E) ∧ ∀ x : Fin (p + l) → Bool, (C.wires (List.ofFn x)).getD (p + l + j) false = decide (∃ a' ∈ P, x (Fin.castAdd l a') = true))) → ∃ (S : Finset (Fin (p + l))) (A O : List PEqualNP.CircuitLowerBounds.Gate),
      (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      (∀ g ∈ A, g.op = PEqualNP.CircuitLowerBounds.GateOp.and) ∧
      (∀ g ∈ O, g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      (A ++ O).Perm C.gates ∧
      S.card ≤ A.length)
    (h2 : ∀ (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' → ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) → PEqualNP.TopForm.IsAO2 (p + l) C → (∀ x : Fin (p + l) → Bool, PEqualNP.MetaComplexity.circuitFun (p + l) C x = decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) → PEqualNP.TwoColour.tCount (p + l) C (fun i => decide (p ≤ i)) = 0 → (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E → (∃ (j : ℕ) (Q : Finset (Fin l)), j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ Q.card ∧ b ∈ Q ∧ (∀ b' ∈ Q, (a, b') ∈ E) ∧ ∀ x : Fin (p + l) → Bool, (C.wires (List.ofFn x)).getD (p + l + j) false = decide (∃ b' ∈ Q, x (Fin.natAdd p b') = true)) ∨ (∃ (j : ℕ) (P : Finset (Fin p)), j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ P.card ∧ a ∈ P ∧ (∀ a' ∈ P, (a', b) ∈ E) ∧ ∀ x : Fin (p + l) → Bool, (C.wires (List.ofFn x)).getD (p + l + j) false = decide (∃ a' ∈ P, x (Fin.castAdd l a') = true))) → ∀ (A O : List PEqualNP.CircuitLowerBounds.Gate),
      (∀ g ∈ A, g.op = PEqualNP.CircuitLowerBounds.GateOp.and) →
      (∀ g ∈ O, g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      (A ++ O).Perm C.gates →
      E.card ≤ O.length + 1)
    : ∀ (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' → ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) → PEqualNP.TopForm.IsAO2 (p + l) C → (∀ x : Fin (p + l) → Bool, PEqualNP.MetaComplexity.circuitFun (p + l) C x = decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) → PEqualNP.TwoColour.tCount (p + l) C (fun i => decide (p ≤ i)) = 0 → (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E → (∃ (j : ℕ) (Q : Finset (Fin l)), j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ Q.card ∧ b ∈ Q ∧ (∀ b' ∈ Q, (a, b') ∈ E) ∧ ∀ x : Fin (p + l) → Bool, (C.wires (List.ofFn x)).getD (p + l + j) false = decide (∃ b' ∈ Q, x (Fin.natAdd p b') = true)) ∨ (∃ (j : ℕ) (P : Finset (Fin p)), j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ P.card ∧ a ∈ P ∧ (∀ a' ∈ P, (a', b) ∈ E) ∧ ∀ x : Fin (p + l) → Bool, (C.wires (List.ofFn x)).getD (p + l + j) false = decide (∃ a' ∈ P, x (Fin.castAdd l a') = true))) → ∃ S : Finset (Fin (p + l)), (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧ E.card + S.card ≤ C.size + 1 := by
  intro p l E C hcyc hAO2 hfun ht hstar
  obtain ⟨S, A, O, hcov, hA, hO, hperm, hSc⟩ := h1 p l E C hcyc hAO2 hfun ht hstar
  have hE : E.card ≤ O.length + 1 := h2 p l E C hcyc hAO2 hfun ht hstar A O hA hO hperm
  refine ⟨S, hcov, ?_⟩
  have hlen : A.length + O.length = C.gates.length := by
    have h := hperm.length_eq
    simpa using h
  have hsize : C.size = C.gates.length := rfl
  omega
