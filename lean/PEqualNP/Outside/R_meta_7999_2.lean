import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7999_2 :
    (∀ x1 : PEqualNP.CircuitLowerBounds.Circuit,
      x1.size ≤ (27 : ℕ) →
      PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →
      (∀ x4 < x1.size,
        PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠
          PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →
      PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ) =
        { op := PEqualNP.CircuitLowerBounds.GateOp.and,
          inputs := [(0 : ℕ), (7 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } →
      (∀ (x6 : Fin (14 : ℕ) → Bool),
        x1.eval (List.ofFn x6) = Bool.true ↔
          ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)),
            (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨
              x7 = x8 + (3 : Fin (7 : ℕ))) ∧
            x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧
            x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →
      ¬PEqualNP.ReadK.IsSingleRead x1 (14 : ℕ)
        (fun (x7 : ℕ) => Decidable.decide ((7 : ℕ) ≤ x7))
        [((0 : ℕ), (7 : ℕ))] →
      False) →
    (∀ x1 : PEqualNP.CircuitLowerBounds.Circuit,
      x1.size ≤ (27 : ℕ) →
      PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →
      (∀ x4 < x1.size,
        PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠
          PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →
      PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ) =
        { op := PEqualNP.CircuitLowerBounds.GateOp.and,
          inputs := [(0 : ℕ), (11 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } →
      (∀ (x6 : Fin (14 : ℕ) → Bool),
        x1.eval (List.ofFn x6) = Bool.true ↔
          ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)),
            (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨
              x7 = x8 + (3 : Fin (7 : ℕ))) ∧
            x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧
            x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →
      ¬PEqualNP.ReadK.IsSingleRead x1 (14 : ℕ)
        (fun (x7 : ℕ) => Decidable.decide ((7 : ℕ) ≤ x7))
        [((0 : ℕ), (7 : ℕ))] →
      False) →
    (∀ x1 : PEqualNP.CircuitLowerBounds.Circuit,
      x1.size ≤ (27 : ℕ) →
      PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →
      (∀ x4 < x1.size,
        PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠
          PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →
      PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ) =
        { op := PEqualNP.CircuitLowerBounds.GateOp.and,
          inputs := [(1 : ℕ), (8 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } →
      (∀ (x6 : Fin (14 : ℕ) → Bool),
        x1.eval (List.ofFn x6) = Bool.true ↔
          ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)),
            (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨
              x7 = x8 + (3 : Fin (7 : ℕ))) ∧
            x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧
            x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →
      ¬PEqualNP.ReadK.IsSingleRead x1 (14 : ℕ)
        (fun (x7 : ℕ) => Decidable.decide ((7 : ℕ) ≤ x7))
        [((0 : ℕ), (7 : ℕ))] →
      False) →
    (∀ x1 : PEqualNP.CircuitLowerBounds.Circuit,
      x1.size ≤ (27 : ℕ) →
      PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →
      (∀ x4 < x1.size,
        PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠
          PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →
      PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ) =
        { op := PEqualNP.CircuitLowerBounds.GateOp.and,
          inputs := [(2 : ℕ), (8 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } →
      (∀ (x6 : Fin (14 : ℕ) → Bool),
        x1.eval (List.ofFn x6) = Bool.true ↔
          ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)),
            (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨
              x7 = x8 + (3 : Fin (7 : ℕ))) ∧
            x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧
            x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →
      ¬PEqualNP.ReadK.IsSingleRead x1 (14 : ℕ)
        (fun (x7 : ℕ) => Decidable.decide ((7 : ℕ) ≤ x7))
        [((0 : ℕ), (7 : ℕ))] →
      False) →
    (∀ x1 : PEqualNP.CircuitLowerBounds.Circuit,
      x1.size ≤ (27 : ℕ) →
      PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →
      (∀ x4 < x1.size,
        PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠
          PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →
      (∃ x5 ∈ [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (11 : ℕ)),
          ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (8 : ℕ))],
        PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ) =
          { op := PEqualNP.CircuitLowerBounds.GateOp.and,
            inputs := [x5.1, x5.2] : PEqualNP.CircuitLowerBounds.Gate }) →
      (∀ (x6 : Fin (14 : ℕ) → Bool),
        x1.eval (List.ofFn x6) = Bool.true ↔
          ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)),
            (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨
              x7 = x8 + (3 : Fin (7 : ℕ))) ∧
            x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧
            x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →
      ¬PEqualNP.ReadK.IsSingleRead x1 (14 : ℕ)
        (fun (x7 : ℕ) => Decidable.decide ((7 : ℕ) ≤ x7))
        [((0 : ℕ), (7 : ℕ))] →
      False) := by
  intro h07 h011 h18 h28 x1 hsize hao hdist hfirst htarget hsingle
  rcases hfirst with ⟨⟨a, b⟩, hmem, hgate⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h
  · cases h
    exact h07 x1 hsize hao hdist hgate htarget hsingle
  · cases h
    exact h011 x1 hsize hao hdist hgate htarget hsingle
  · cases h
    exact h18 x1 hsize hao hdist hgate htarget hsingle
  · cases h
    exact h28 x1 hsize hao hdist hgate htarget hsingle
