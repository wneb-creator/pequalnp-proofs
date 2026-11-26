import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4653_73
    (c1 : have x1 : Fin (42 : ℕ) → Fin (42 : ℕ) → Prop := fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)];
      ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x7 →
        (∀ (x5 : Fin (42 : ℕ) → Bool), x7.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), x1 x6 x7 ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) →
        (∀ (x8 : Fin x7.gates.length), (x7.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ x9 ∈ (x7.gates.get x8).inputs, ∃ (x11 : Fin (42 : ℕ)) (x12 : Fin (42 : ℕ)), x1 x11 x12 ∧ { gates := x7.gates.set (↑x8) { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x9] : PEqualNP.CircuitLowerBounds.Gate }, output := x7.output : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn (fun (x13 : Fin (42 : ℕ)) => Decidable.decide (x13 = x11 ∨ x13 = x12))) = Bool.false ∧ have x13 : List Bool := { gates := List.take (↑x8) x7.gates, output := x7.output : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn (fun (x13 : Fin (42 : ℕ)) => Decidable.decide (x13 = x11 ∨ x13 = x12))); x13.getD x9 Bool.false = Bool.false ∧ ∃ x14 ∈ (x7.gates.get x8).inputs, x13.getD x14 Bool.false = Bool.true) →
        {x8 : Fin x7.gates.length | (x7.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard ≤ (20 : ℕ) →
        (104 : ℕ) ≤ {x8 : Fin x7.gates.length | (x7.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard)
    (c2 : have x1 : Fin (42 : ℕ) → Fin (42 : ℕ) → Prop := fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)];
      ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x7 →
        (∀ (x5 : Fin (42 : ℕ) → Bool), x7.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), x1 x6 x7 ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) →
        (∀ (x8 : Fin x7.gates.length), (x7.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ x9 ∈ (x7.gates.get x8).inputs, ∃ (x11 : Fin (42 : ℕ)) (x12 : Fin (42 : ℕ)), x1 x11 x12 ∧ { gates := x7.gates.set (↑x8) { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x9] : PEqualNP.CircuitLowerBounds.Gate }, output := x7.output : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn (fun (x13 : Fin (42 : ℕ)) => Decidable.decide (x13 = x11 ∨ x13 = x12))) = Bool.false ∧ have x13 : List Bool := { gates := List.take (↑x8) x7.gates, output := x7.output : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn (fun (x13 : Fin (42 : ℕ)) => Decidable.decide (x13 = x11 ∨ x13 = x12))); x13.getD x9 Bool.false = Bool.false ∧ ∃ x14 ∈ (x7.gates.get x8).inputs, x13.getD x14 Bool.false = Bool.true) →
        have x8 : ℕ := {x8 : Fin x7.gates.length | (x7.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard;
        ((21 : ℕ) ≤ x8 ∧ x8 ≤ (45 : ℕ)) →
        (104 : ℕ) ≤ {x8 : Fin x7.gates.length | (x7.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard)
    (c3 : have x1 : Fin (42 : ℕ) → Fin (42 : ℕ) → Prop := fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)];
      ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x7 →
        (∀ (x5 : Fin (42 : ℕ) → Bool), x7.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), x1 x6 x7 ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) →
        (∀ (x8 : Fin x7.gates.length), (x7.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or → ∀ x9 ∈ (x7.gates.get x8).inputs, ∃ (x11 : Fin (42 : ℕ)) (x12 : Fin (42 : ℕ)), x1 x11 x12 ∧ { gates := x7.gates.set (↑x8) { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x9] : PEqualNP.CircuitLowerBounds.Gate }, output := x7.output : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn (fun (x13 : Fin (42 : ℕ)) => Decidable.decide (x13 = x11 ∨ x13 = x12))) = Bool.false ∧ have x13 : List Bool := { gates := List.take (↑x8) x7.gates, output := x7.output : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn (fun (x13 : Fin (42 : ℕ)) => Decidable.decide (x13 = x11 ∨ x13 = x12))); x13.getD x9 Bool.false = Bool.false ∧ ∃ x14 ∈ (x7.gates.get x8).inputs, x13.getD x14 Bool.false = Bool.true) →
        (46 : ℕ) ≤ {x8 : Fin x7.gates.length | (x7.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard →
        (104 : ℕ) ≤ {x8 : Fin x7.gates.length | (x7.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard) :
    (have x1 : Fin (42 : ℕ) → Fin (42 : ℕ) → Prop := fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; have x2 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => {x3 : Fin x2.gates.length | (x2.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard; have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → PEqualNP.CircuitLowerBounds.Circuit := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ) => { gates := x3.gates.set x4 { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5] : PEqualNP.CircuitLowerBounds.Gate }, output := x3.output : PEqualNP.CircuitLowerBounds.Circuit }; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x5 : Fin (42 : ℕ) → Bool), x4.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), x1 x6 x7 ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true; have x5 : Fin (42 : ℕ) → Fin (42 : ℕ) → Fin (42 : ℕ) → Bool := fun (x5 x6 x7 : Fin (42 : ℕ)) => Decidable.decide (x7 = x5 ∨ x7 = x6); have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) =>   ∀ (x7 : Fin x6.gates.length),     (x6.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.or →       ∀ x9 ∈ (x6.gates.get x7).inputs,         ∃ (x11 : Fin (42 : ℕ)) (x12 : Fin (42 : ℕ)),           x1 x11 x12 ∧             (x3 x6 (↑x7) x9).eval (List.ofFn (x5 x11 x12)) = Bool.false ∧               have x13 : List Bool := { gates := List.take (↑x7) x6.gates, output := x6.output : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn (x5 x11 x12));               x13.getD x9 Bool.false = Bool.false ∧ ∃ x14 ∈ (x6.gates.get x7).inputs, x13.getD x14 Bool.false = Bool.true; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → x4 x7 → x6 x7 → (104 : ℕ) ≤ x2 x7) :=
  fun x7 hm h4 h6 =>
    @Decidable.byCases
      ({x8 : Fin x7.gates.length | (x7.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard ≤ 20)
      ((104 : ℕ) ≤ {x8 : Fin x7.gates.length | (x7.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard)
      (Nat.decLe _ 20)
      (fun hle20 => c1 x7 hm h4 h6 hle20)
      (fun hgt20 =>
        @Decidable.byCases
          ({x8 : Fin x7.gates.length | (x7.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard ≤ 45)
          ((104 : ℕ) ≤ {x8 : Fin x7.gates.length | (x7.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard)
          (Nat.decLe _ 45)
          (fun hle45 => c2 x7 hm h4 h6 ⟨Nat.succ_le_of_lt (Nat.lt_of_not_ge hgt20), hle45⟩)
          (fun hgt45 => c3 x7 hm h4 h6 (Nat.succ_le_of_lt (Nat.lt_of_not_ge hgt45))))
