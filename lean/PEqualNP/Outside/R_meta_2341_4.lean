import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

-- The circuit is empty or its last gate is one of the two allowed kinds, and past the end of the
-- gate list `gateAt` reads the default OR gate. So the gate at index `size - 1` is an AND in one
-- case and an OR in the other, and the step is asked once for each of the two cases.
theorem PEqualNP.Outside.R_meta_2341_4
    (lastAnd :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (13 : ℕ)) (x4 : Bool),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ (x6 : Fin x1.gates.length), ∀ x7 ∈ (x1.gates.get x6).inputs, x7 < (27 : ℕ) + ↑x6) →       have x7 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};       have x8 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x8 x9 : Fin (13 : ℕ)) => (List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 = x8)) ++ List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 = x9);       have x9 : Finset (Fin (13 : ℕ)) → List Bool := fun (x9 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 ∈ x9)) ++ List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (∀ x11 ∈ x9, x11 - x10 ∉ x7);       have x10 : Finset (Fin (13 : ℕ)) → Prop := fun (x10 : Finset (Fin (13 : ℕ))) => x10.card = (4 : ℕ) ∧ ∀ (x11 : Fin (13 : ℕ)), {x12 ∈ x10 | x12 - x11 ∈ x7}.card ≤ (2 : ℕ);       (∀ (x11 x12 : Fin (13 : ℕ)), x11 - x12 ∈ x7 → x11 ≠ x2 ∨ x12 ≠ x3 → x1.eval (x8 x11 x12 ++ [x4]) = Bool.true) → (∀ (x12 : Finset (Fin (13 : ℕ))), x10 x12 → x1.eval (x9 x12 ++ [x4]) = Bool.false) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and → (63 : ℕ) ≤ x1.size)
    (lastOr :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (13 : ℕ)) (x4 : Bool),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ (x6 : Fin x1.gates.length), ∀ x7 ∈ (x1.gates.get x6).inputs, x7 < (27 : ℕ) + ↑x6) →       have x7 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};       have x8 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x8 x9 : Fin (13 : ℕ)) => (List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 = x8)) ++ List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 = x9);       have x9 : Finset (Fin (13 : ℕ)) → List Bool := fun (x9 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 ∈ x9)) ++ List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (∀ x11 ∈ x9, x11 - x10 ∉ x7);       have x10 : Finset (Fin (13 : ℕ)) → Prop := fun (x10 : Finset (Fin (13 : ℕ))) => x10.card = (4 : ℕ) ∧ ∀ (x11 : Fin (13 : ℕ)), {x12 ∈ x10 | x12 - x11 ∈ x7}.card ≤ (2 : ℕ);       (∀ (x11 x12 : Fin (13 : ℕ)), x11 - x12 ∈ x7 → x11 ≠ x2 ∨ x12 ≠ x3 → x1.eval (x8 x11 x12 ++ [x4]) = Bool.true) → (∀ (x12 : Finset (Fin (13 : ℕ))), x10 x12 → x1.eval (x9 x12 ++ [x4]) = Bool.false) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or → (63 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (13 : ℕ)) (x4 : Bool),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ (x6 : Fin x1.gates.length), ∀ x7 ∈ (x1.gates.get x6).inputs, x7 < (27 : ℕ) + ↑x6) →       have x7 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};       have x8 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x8 x9 : Fin (13 : ℕ)) => (List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 = x8)) ++ List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 = x9);       have x9 : Finset (Fin (13 : ℕ)) → List Bool := fun (x9 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 ∈ x9)) ++ List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (∀ x11 ∈ x9, x11 - x10 ∉ x7);       have x10 : Finset (Fin (13 : ℕ)) → Prop := fun (x10 : Finset (Fin (13 : ℕ))) => x10.card = (4 : ℕ) ∧ ∀ (x11 : Fin (13 : ℕ)), {x12 ∈ x10 | x12 - x11 ∈ x7}.card ≤ (2 : ℕ);       (∀ (x11 x12 : Fin (13 : ℕ)), x11 - x12 ∈ x7 → x11 ≠ x2 ∨ x12 ≠ x3 → x1.eval (x8 x11 x12 ++ [x4]) = Bool.true) → (∀ (x12 : Finset (Fin (13 : ℕ))), x10 x12 → x1.eval (x9 x12 ++ [x4]) = Bool.false) → (63 : ℕ) ≤ x1.size := by
  intros x1 x2 x3 x4 h1 h2 L1 L2 L3 L4 h3 h4
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
  · exact lastAnd x1 x2 x3 x4 h1 h2 h3 h4 hand
  · exact lastOr x1 x2 x3 x4 h1 h2 h3 h4 har
