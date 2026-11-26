import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5987_73
    (c1 : have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ));
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 →
        (∀ x4 ∈ x2.gates, x4.inputs.Nodup) →
        x2.size ≤ (64 : ℕ) →
        have x6 : (Fin (26 : ℕ) → Bool) → ℕ → Bool := fun (x6 : Fin (26 : ℕ) → Bool) (x7 : ℕ) => (x2.wires (List.ofFn x6)).getD x7 Bool.false;
        (∀ (x7 : Fin (26 : ℕ) → Bool), x6 x7 x2.output = Bool.true ↔ ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), x1 x8 x9 ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true) →
        (∀ (x8 x9 : Fin (13 : ℕ)), x1 x8 x9 → ∃ x11 ⊆ Finset.range x2.size, (56 : ℕ) ≤ x11.card ∧ ∀ x12 ∈ x11, ∀ x14 < (26 : ℕ) + x12, ∃ (x16 : Fin (26 : ℕ) → Bool), x16 (Fin.castAdd (13 : ℕ) x8) = Bool.false ∧ x16 (Fin.natAdd (13 : ℕ) x9) = Bool.false ∧ x6 x16 x14 ≠ x6 x16 ((26 : ℕ) + x12)) →
        {i : Fin x2.gates.length | (x2.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard ≤ (20 : ℕ) →
        have x9 : ℕ → Prop := fun (x9 : ℕ) => Relation.ReflTransGen (fun (x10 x11 : ℕ) => ∃ (x12 : ℕ) (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate), x11 = (26 : ℕ) + x12 ∧ x2.gates[x12]? = Option.some x14 ∧ (x14.inputs = [x10, x13] ∨ x14.inputs = [x13, x10]) ∧ (x14.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x6 (fun (x15 : Fin (26 : ℕ)) => Decidable.decide (↑x15 = x9)) x13 = Bool.true)) ((13 : ℕ) - x9) x2.output;
        x9 (0 : ℕ) ∨ x9 (13 : ℕ))
    (c2 : have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ));
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 →
        (∀ x4 ∈ x2.gates, x4.inputs.Nodup) →
        x2.size ≤ (64 : ℕ) →
        have x6 : (Fin (26 : ℕ) → Bool) → ℕ → Bool := fun (x6 : Fin (26 : ℕ) → Bool) (x7 : ℕ) => (x2.wires (List.ofFn x6)).getD x7 Bool.false;
        (∀ (x7 : Fin (26 : ℕ) → Bool), x6 x7 x2.output = Bool.true ↔ ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), x1 x8 x9 ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true) →
        (∀ (x8 x9 : Fin (13 : ℕ)), x1 x8 x9 → ∃ x11 ⊆ Finset.range x2.size, (56 : ℕ) ≤ x11.card ∧ ∀ x12 ∈ x11, ∀ x14 < (26 : ℕ) + x12, ∃ (x16 : Fin (26 : ℕ) → Bool), x16 (Fin.castAdd (13 : ℕ) x8) = Bool.false ∧ x16 (Fin.natAdd (13 : ℕ) x9) = Bool.false ∧ x6 x16 x14 ≠ x6 x16 ((26 : ℕ) + x12)) →
        (have x3 : ℕ := {i : Fin x2.gates.length | (x2.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard; (21 : ℕ) ≤ x3 ∧ x3 ≤ (40 : ℕ)) →
        have x9 : ℕ → Prop := fun (x9 : ℕ) => Relation.ReflTransGen (fun (x10 x11 : ℕ) => ∃ (x12 : ℕ) (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate), x11 = (26 : ℕ) + x12 ∧ x2.gates[x12]? = Option.some x14 ∧ (x14.inputs = [x10, x13] ∨ x14.inputs = [x13, x10]) ∧ (x14.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x6 (fun (x15 : Fin (26 : ℕ)) => Decidable.decide (↑x15 = x9)) x13 = Bool.true)) ((13 : ℕ) - x9) x2.output;
        x9 (0 : ℕ) ∨ x9 (13 : ℕ))
    (c3 : have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ));
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 →
        (∀ x4 ∈ x2.gates, x4.inputs.Nodup) →
        x2.size ≤ (64 : ℕ) →
        have x6 : (Fin (26 : ℕ) → Bool) → ℕ → Bool := fun (x6 : Fin (26 : ℕ) → Bool) (x7 : ℕ) => (x2.wires (List.ofFn x6)).getD x7 Bool.false;
        (∀ (x7 : Fin (26 : ℕ) → Bool), x6 x7 x2.output = Bool.true ↔ ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), x1 x8 x9 ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true) →
        (∀ (x8 x9 : Fin (13 : ℕ)), x1 x8 x9 → ∃ x11 ⊆ Finset.range x2.size, (56 : ℕ) ≤ x11.card ∧ ∀ x12 ∈ x11, ∀ x14 < (26 : ℕ) + x12, ∃ (x16 : Fin (26 : ℕ) → Bool), x16 (Fin.castAdd (13 : ℕ) x8) = Bool.false ∧ x16 (Fin.natAdd (13 : ℕ) x9) = Bool.false ∧ x6 x16 x14 ≠ x6 x16 ((26 : ℕ) + x12)) →
        (41 : ℕ) ≤ {i : Fin x2.gates.length | (x2.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard →
        have x9 : ℕ → Prop := fun (x9 : ℕ) => Relation.ReflTransGen (fun (x10 x11 : ℕ) => ∃ (x12 : ℕ) (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate), x11 = (26 : ℕ) + x12 ∧ x2.gates[x12]? = Option.some x14 ∧ (x14.inputs = [x10, x13] ∨ x14.inputs = [x13, x10]) ∧ (x14.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x6 (fun (x15 : Fin (26 : ℕ)) => Decidable.decide (↑x15 = x9)) x13 = Bool.true)) ((13 : ℕ) - x9) x2.output;
        x9 (0 : ℕ) ∨ x9 (13 : ℕ)) :
    (have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 →     (∀ x4 ∈ x2.gates, x4.inputs.Nodup) →       x2.size ≤ (64 : ℕ) →         have x6 : (Fin (26 : ℕ) → Bool) → ℕ → Bool := fun (x6 : Fin (26 : ℕ) → Bool) (x7 : ℕ) => (x2.wires (List.ofFn x6)).getD x7 Bool.false;         (∀ (x7 : Fin (26 : ℕ) → Bool), x6 x7 x2.output = Bool.true ↔ ∃ (x8 : Fin (13 : ℕ)) (x9 : Fin (13 : ℕ)), x1 x8 x9 ∧ x7 (Fin.castAdd (13 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (13 : ℕ) x9) = Bool.true) →           (∀ (x8 x9 : Fin (13 : ℕ)), x1 x8 x9 → ∃ x11 ⊆ Finset.range x2.size, (56 : ℕ) ≤ x11.card ∧ ∀ x12 ∈ x11, ∀ x14 < (26 : ℕ) + x12, ∃ (x16 : Fin (26 : ℕ) → Bool), x16 (Fin.castAdd (13 : ℕ) x8) = Bool.false ∧ x16 (Fin.natAdd (13 : ℕ) x9) = Bool.false ∧ x6 x16 x14 ≠ x6 x16 ((26 : ℕ) + x12)) →             have x9 : ℕ → Prop := fun (x9 : ℕ) => Relation.ReflTransGen (fun (x10 x11 : ℕ) => ∃ (x12 : ℕ) (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate), x11 = (26 : ℕ) + x12 ∧ x2.gates[x12]? = Option.some x14 ∧ (x14.inputs = [x10, x13] ∨ x14.inputs = [x13, x10]) ∧ (x14.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x6 (fun (x15 : Fin (26 : ℕ)) => Decidable.decide (↑x15 = x9)) x13 = Bool.true)) ((13 : ℕ) - x9) x2.output;             x9 (0 : ℕ) ∨ x9 (13 : ℕ)) :=
  fun x2 hAO2 hNodup hSize hEval hSens =>
    @Decidable.byCases
      ({i : Fin x2.gates.length | (x2.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard ≤ 20)
      _
      (Nat.decLe _ 20)
      (fun hle20 => c1 x2 hAO2 hNodup hSize hEval hSens hle20)
      (fun hgt20 =>
        @Decidable.byCases
          ({i : Fin x2.gates.length | (x2.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard ≤ 40)
          _
          (Nat.decLe _ 40)
          (fun hle40 => c2 x2 hAO2 hNodup hSize hEval hSens ⟨Nat.succ_le_of_lt (Nat.lt_of_not_ge hgt20), hle40⟩)
          (fun hgt40 => c3 x2 hAO2 hNodup hSize hEval hSens (Nat.succ_le_of_lt (Nat.lt_of_not_ge hgt40))))
