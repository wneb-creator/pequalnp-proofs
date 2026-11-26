import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

-- The circuit is empty or its last gate is one of the two allowed kinds, and past the end of the
-- gate list `gateAt` reads the default OR gate. So the gate at index `size - 1` is an AND in one
-- case and an OR in the other, and the step is asked once for each of the two cases.
theorem PEqualNP.Outside.R_meta_6118_1
    (lastAnd :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 x4 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           x4 < (26 : ℕ) + x1.size →             x3 ≠ x4 →               have x11 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};               have x12 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x12 x13 : Fin (13 : ℕ)) => (List.ofFn fun (x14 : Fin (13 : ℕ)) => Decidable.decide (x14 = x12)) ++ List.ofFn fun (x14 : Fin (13 : ℕ)) => Decidable.decide (x14 = x13);               have x13 : Finset (Fin (13 : ℕ)) → List Bool := fun (x13 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x14 : Fin (13 : ℕ)) => Decidable.decide (x14 ∈ x13)) ++ List.ofFn fun (x14 : Fin (13 : ℕ)) => Decidable.decide (∀ x15 ∈ x13, x15 - x14 ∉ x11);               have x14 : Finset (Fin (13 : ℕ)) → Prop := fun (x14 : Finset (Fin (13 : ℕ))) => x14.card = (4 : ℕ) ∧ ∀ (x15 : Fin (13 : ℕ)), {x16 ∈ x14 | x16 - x15 ∈ x11}.card ≤ (2 : ℕ);               have x15 : ℕ → List Bool → Bool := fun (x15 : ℕ) (x16 : List Bool) => (x1.wires x16).getD x15 Bool.false;               have x16 : List Bool → Bool := fun (x16 : List Bool) => x15 x3 x16 || x15 x4 x16;               (∀ (x17 x18 : Fin (13 : ℕ)), x17 - x18 ∈ x11 → x15 x2 (x12 x17 x18) = Bool.true ∨ x16 (x12 x17 x18) = Bool.true) → (∀ (x18 : Finset (Fin (13 : ℕ))), x14 x18 → x15 x2 (x13 x18) = Bool.false ∧ x16 (x13 x18) = Bool.false) → (∃ (x19 : Fin (13 : ℕ)) (x20 : Fin (13 : ℕ)), x19 - x20 ∈ x11 ∧ x15 x2 (x12 x19 x20) = Bool.true ∧ x16 (x12 x19 x20) = Bool.false) → (∃ (x20 : Fin (13 : ℕ)) (x21 : Fin (13 : ℕ)), x20 - x21 ∈ x11 ∧ x16 (x12 x20 x21) = Bool.true ∧ x15 x2 (x12 x20 x21) = Bool.false) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and → (62 : ℕ) ≤ x1.size)
    (lastOr :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 x4 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           x4 < (26 : ℕ) + x1.size →             x3 ≠ x4 →               have x11 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};               have x12 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x12 x13 : Fin (13 : ℕ)) => (List.ofFn fun (x14 : Fin (13 : ℕ)) => Decidable.decide (x14 = x12)) ++ List.ofFn fun (x14 : Fin (13 : ℕ)) => Decidable.decide (x14 = x13);               have x13 : Finset (Fin (13 : ℕ)) → List Bool := fun (x13 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x14 : Fin (13 : ℕ)) => Decidable.decide (x14 ∈ x13)) ++ List.ofFn fun (x14 : Fin (13 : ℕ)) => Decidable.decide (∀ x15 ∈ x13, x15 - x14 ∉ x11);               have x14 : Finset (Fin (13 : ℕ)) → Prop := fun (x14 : Finset (Fin (13 : ℕ))) => x14.card = (4 : ℕ) ∧ ∀ (x15 : Fin (13 : ℕ)), {x16 ∈ x14 | x16 - x15 ∈ x11}.card ≤ (2 : ℕ);               have x15 : ℕ → List Bool → Bool := fun (x15 : ℕ) (x16 : List Bool) => (x1.wires x16).getD x15 Bool.false;               have x16 : List Bool → Bool := fun (x16 : List Bool) => x15 x3 x16 || x15 x4 x16;               (∀ (x17 x18 : Fin (13 : ℕ)), x17 - x18 ∈ x11 → x15 x2 (x12 x17 x18) = Bool.true ∨ x16 (x12 x17 x18) = Bool.true) → (∀ (x18 : Finset (Fin (13 : ℕ))), x14 x18 → x15 x2 (x13 x18) = Bool.false ∧ x16 (x13 x18) = Bool.false) → (∃ (x19 : Fin (13 : ℕ)) (x20 : Fin (13 : ℕ)), x19 - x20 ∈ x11 ∧ x15 x2 (x12 x19 x20) = Bool.true ∧ x16 (x12 x19 x20) = Bool.false) → (∃ (x20 : Fin (13 : ℕ)) (x21 : Fin (13 : ℕ)), x20 - x21 ∈ x11 ∧ x16 (x12 x20 x21) = Bool.true ∧ x15 x2 (x12 x20 x21) = Bool.false) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or → (62 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 x4 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           x4 < (26 : ℕ) + x1.size →             x3 ≠ x4 →               have x11 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};               have x12 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x12 x13 : Fin (13 : ℕ)) => (List.ofFn fun (x14 : Fin (13 : ℕ)) => Decidable.decide (x14 = x12)) ++ List.ofFn fun (x14 : Fin (13 : ℕ)) => Decidable.decide (x14 = x13);               have x13 : Finset (Fin (13 : ℕ)) → List Bool := fun (x13 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x14 : Fin (13 : ℕ)) => Decidable.decide (x14 ∈ x13)) ++ List.ofFn fun (x14 : Fin (13 : ℕ)) => Decidable.decide (∀ x15 ∈ x13, x15 - x14 ∉ x11);               have x14 : Finset (Fin (13 : ℕ)) → Prop := fun (x14 : Finset (Fin (13 : ℕ))) => x14.card = (4 : ℕ) ∧ ∀ (x15 : Fin (13 : ℕ)), {x16 ∈ x14 | x16 - x15 ∈ x11}.card ≤ (2 : ℕ);               have x15 : ℕ → List Bool → Bool := fun (x15 : ℕ) (x16 : List Bool) => (x1.wires x16).getD x15 Bool.false;               have x16 : List Bool → Bool := fun (x16 : List Bool) => x15 x3 x16 || x15 x4 x16;               (∀ (x17 x18 : Fin (13 : ℕ)), x17 - x18 ∈ x11 → x15 x2 (x12 x17 x18) = Bool.true ∨ x16 (x12 x17 x18) = Bool.true) → (∀ (x18 : Finset (Fin (13 : ℕ))), x14 x18 → x15 x2 (x13 x18) = Bool.false ∧ x16 (x13 x18) = Bool.false) → (∃ (x19 : Fin (13 : ℕ)) (x20 : Fin (13 : ℕ)), x19 - x20 ∈ x11 ∧ x15 x2 (x12 x19 x20) = Bool.true ∧ x16 (x12 x19 x20) = Bool.false) → (∃ (x20 : Fin (13 : ℕ)) (x21 : Fin (13 : ℕ)), x20 - x21 ∈ x11 ∧ x16 (x12 x20 x21) = Bool.true ∧ x15 x2 (x12 x20 x21) = Bool.false) → (62 : ℕ) ≤ x1.size := by
  intros x1 x2 x3 x4 h1 h2 h3 h4 h5 h6 L1 L2 L3 L4 L5 L6 h7 h8 h9 h10
  have hop : ∀ g ∈ x1.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    simpa using (h1 g hg).1
  have hsz : x1.size = x1.gates.length := rfl
  have hcase : (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op =
      GateOp.and ∨
      (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = GateOp.or := by
    rcases Nat.eq_zero_or_pos x1.size with hz | hpos
    · right
      have hg : PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))
          = Gate.mk GateOp.or [] := by
        show List.getD x1.gates (x1.size - (1 : ℕ)) (Gate.mk GateOp.or []) = _
        apply List.getD_eq_default
        omega
      rw [hg]
    · have hj : x1.size - (1 : ℕ) < x1.gates.length := by rw [← hsz]; omega
      have hg : PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))
          = x1.gates[x1.size - (1 : ℕ)] :=
        List.getD_eq_getElem _ _ hj
      rw [hg]
      exact hop _ (List.getElem_mem hj)
  rcases hcase with hand | har
  · exact lastAnd x1 x2 x3 x4 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hand
  · exact lastOr x1 x2 x3 x4 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 har
