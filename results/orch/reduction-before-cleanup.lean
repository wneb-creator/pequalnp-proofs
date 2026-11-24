import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5324_49
    (edge_bound : ∀ (n m : ℕ) (E H : Finset (Fin n × Fin m))
      (C : PEqualNP.CircuitLowerBounds.Circuit) (T : Finset (ℕ × ℕ)),
      (∀ p q l s, p ≠ q → l ≠ s →
        ¬ ((p, l) ∈ E ∧ (p, s) ∈ E ∧ (q, l) ∈ E ∧ (q, s) ∈ E)) →
      PEqualNP.TopForm.IsAO2 (n + m) C →
      (∀ j < C.gates.length,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
          PEqualNP.CircuitLowerBounds.GateOp.and →
        ∃ z : Fin (n + m) → Bool,
          (C.wires (List.ofFn z)).getD (n + m + j) false = true ∧
          ¬ ∃ p l, (p, l) ∈ E ∧ z (Fin.castAdd m p) = true ∧
            z (Fin.natAdd n l) = true) →
      (∀ t ∈ T, ∀ z : Fin (n + m) → Bool,
        (C.wires (List.ofFn z)).getD t.1 false = true →
        (C.wires (List.ofFn z)).getD t.2 false = true →
        ∃ p l, (p, l) ∈ E ∧ z (Fin.castAdd m p) = true ∧
          z (Fin.natAdd n l) = true) →
      (∀ e ∈ H, e ∈ E ∧ ∃ t ∈ T,
        (C.wires (List.ofFn fun i : Fin (n + m) =>
          decide (i = Fin.castAdd m e.1 ∨ i = Fin.natAdd n e.2))).getD t.1 false = true ∧
        (C.wires (List.ofFn fun i : Fin (n + m) =>
          decide (i = Fin.castAdd m e.1 ∨ i = Fin.natAdd n e.2))).getD t.2 false = true) →
      H.card ≤ C.gates.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op) + T.card)
    (matching_bound : ∀ (n m : ℕ) (E H : Finset (Fin n × Fin m))
      (C : PEqualNP.CircuitLowerBounds.Circuit) (T : Finset (ℕ × ℕ)),
      (∀ p q l s, p ≠ q → l ≠ s →
        ¬ ((p, l) ∈ E ∧ (p, s) ∈ E ∧ (q, l) ∈ E ∧ (q, s) ∈ E)) →
      PEqualNP.TopForm.IsAO2 (n + m) C →
      (∀ j < C.gates.length,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
          PEqualNP.CircuitLowerBounds.GateOp.and →
        ∃ z : Fin (n + m) → Bool,
          (C.wires (List.ofFn z)).getD (n + m + j) false = true ∧
          ¬ ∃ p l, (p, l) ∈ E ∧ z (Fin.castAdd m p) = true ∧
            z (Fin.natAdd n l) = true) →
      (∀ t ∈ T, ∀ z : Fin (n + m) → Bool,
        (C.wires (List.ofFn z)).getD t.1 false = true →
        (C.wires (List.ofFn z)).getD t.2 false = true →
        ∃ p l, (p, l) ∈ E ∧ z (Fin.castAdd m p) = true ∧
          z (Fin.natAdd n l) = true) →
      (∀ e ∈ H, e ∈ E ∧ ∃ t ∈ T,
        (C.wires (List.ofFn fun i : Fin (n + m) =>
          decide (i = Fin.castAdd m e.1 ∨ i = Fin.natAdd n e.2))).getD t.1 false = true ∧
        (C.wires (List.ofFn fun i : Fin (n + m) =>
          decide (i = Fin.castAdd m e.1 ∨ i = Fin.natAdd n e.2))).getD t.2 false = true) →
      (∀ e ∈ H, ∀ d ∈ H, e.1 = d.1 → e = d) →
      (∀ e ∈ H, ∀ d ∈ H, e.2 = d.2 → e = d) →
      H.card ≤ C.gates.countP (fun g => !PEqualNP.SharedBlockCost.isOrOp g.op) + T.card) :
    ∀ (x1 x2 : ℕ) (x3 x4 x5 : Finset (Fin x1 × Fin x2)) (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : Finset (ℕ × ℕ)), (∀ (x8 x9 : Fin x1) (x10 x11 : Fin x2), x8 ≠ x9 → x10 ≠ x11 → ¬((x8, x10) ∈ x3 ∧ (x8, x11) ∈ x3 ∧ (x9, x10) ∈ x3 ∧ (x9, x11) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x6 → (∀ x10 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : Fin (x1 + x2) → Bool), (x6.wires (List.ofFn x13)).getD (x1 + x2 + x10) Bool.false = Bool.true ∧ ¬∃ (x14 : Fin x1) (x15 : Fin x2), (x14, x15) ∈ x3 ∧ x13 (Fin.castAdd x2 x14) = Bool.true ∧ x13 (Fin.natAdd x1 x15) = Bool.true) → (∀ x11 ∈ x7, ∀ (x13 : Fin (x1 + x2) → Bool), (x6.wires (List.ofFn x13)).getD x11.1 Bool.false = Bool.true → (x6.wires (List.ofFn x13)).getD x11.2 Bool.false = Bool.true → ∃ (x16 : Fin x1) (x17 : Fin x2), (x16, x17) ∈ x3 ∧ x13 (Fin.castAdd x2 x16) = Bool.true ∧ x13 (Fin.natAdd x1 x17) = Bool.true) → (∀ x12 ∈ x4, x12 ∈ x3 ∧ ∃ x14 ∈ x7, (x6.wires (List.ofFn fun (x15 : Fin (x1 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x12.1 ∨ x15 = Fin.natAdd x1 x12.2))).getD x14.1 Bool.false = Bool.true ∧ (x6.wires (List.ofFn fun (x15 : Fin (x1 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x12.1 ∨ x15 = Fin.natAdd x1 x12.2))).getD x14.2 Bool.false = Bool.true) → x5 ⊆ x4 → (∀ x14 ∈ x5, ∀ x16 ∈ x5, x14.1 = x16.1 → x14 = x16) → (∀ x15 ∈ x5, ∀ x17 ∈ x5, x15.2 = x17.2 → x15 = x17) → x4.card + x5.card ≤ x6.size + (2 : ℕ) * x7.card := by
  intro n m E H M C T h4 hAO hdirty hsafe hcover hMH hrow hcol
  have hE := edge_bound n m E H C T h4 hAO hdirty hsafe hcover
  have hM := matching_bound n m E M C T h4 hAO hdirty hsafe
    (fun e he => hcover e (hMH he)) hrow hcol
  have hcount : ∀ gs : List PEqualNP.CircuitLowerBounds.Gate,
      gs.countP (fun g => PEqualNP.SharedBlockCost.isOrOp g.op) +
      gs.countP (fun g => !PEqualNP.SharedBlockCost.isOrOp g.op) = gs.length := by
    intro gs
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      cases h : PEqualNP.SharedBlockCost.isOrOp g.op <;>
        simp [List.countP_cons, h] <;> omega
  have hc := hcount C.gates
  unfold PEqualNP.CircuitLowerBounds.Circuit.size
  omega
