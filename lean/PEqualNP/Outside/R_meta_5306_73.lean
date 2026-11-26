import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5306_73
    (h1 :
      let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ));
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x2 →
        x2.size ≤ (63 : ℕ) →
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (1 : ℕ) →
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (1 : ℕ) →
        {i : Fin x2.gates.length | (x2.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard ≤ (20 : ℕ) →
        (∀ (x7 x8 : Fin (13 : ℕ)), x1 x7 x8 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8)) = Bool.true) →
        ∃ (x8 : Finset (Fin (13 : ℕ))) (x9 : Finset (Fin (13 : ℕ))),
          (∀ x10 ∈ x8, ∀ x12 ∈ x9, ¬x1 x10 x12) ∧
          (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x8 | x1 x11 x10}.card ≤ (2 : ℕ)) ∧
          (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x9 | x1 x10 x11}.card ≤ (2 : ℕ)) ∧
          ∀ (x10 : Fin (26 : ℕ) → Bool),
            (∀ x11 ∈ x8, x10 (Fin.castAdd (13 : ℕ) x11) = Bool.true) →
            (∀ x12 ∈ x9, x10 (Fin.natAdd (13 : ℕ) x12) = Bool.true) →
            PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 x10 = Bool.true)
    (h2 :
      let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ));
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x2 →
        x2.size ≤ (63 : ℕ) →
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (1 : ℕ) →
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (1 : ℕ) →
        (have x3 : ℕ := {i : Fin x2.gates.length | (x2.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard; (21 : ℕ) ≤ x3 ∧ x3 ≤ (35 : ℕ)) →
        (∀ (x7 x8 : Fin (13 : ℕ)), x1 x7 x8 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8)) = Bool.true) →
        ∃ (x8 : Finset (Fin (13 : ℕ))) (x9 : Finset (Fin (13 : ℕ))),
          (∀ x10 ∈ x8, ∀ x12 ∈ x9, ¬x1 x10 x12) ∧
          (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x8 | x1 x11 x10}.card ≤ (2 : ℕ)) ∧
          (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x9 | x1 x10 x11}.card ≤ (2 : ℕ)) ∧
          ∀ (x10 : Fin (26 : ℕ) → Bool),
            (∀ x11 ∈ x8, x10 (Fin.castAdd (13 : ℕ) x11) = Bool.true) →
            (∀ x12 ∈ x9, x10 (Fin.natAdd (13 : ℕ) x12) = Bool.true) →
            PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 x10 = Bool.true)
    (h3 :
      let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ));
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x2 →
        x2.size ≤ (63 : ℕ) →
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (1 : ℕ) →
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (1 : ℕ) →
        (36 : ℕ) ≤ {i : Fin x2.gates.length | (x2.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard →
        (∀ (x7 x8 : Fin (13 : ℕ)), x1 x7 x8 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8)) = Bool.true) →
        ∃ (x8 : Finset (Fin (13 : ℕ))) (x9 : Finset (Fin (13 : ℕ))),
          (∀ x10 ∈ x8, ∀ x12 ∈ x9, ¬x1 x10 x12) ∧
          (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x8 | x1 x11 x10}.card ≤ (2 : ℕ)) ∧
          (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x9 | x1 x10 x11}.card ≤ (2 : ℕ)) ∧
          ∀ (x10 : Fin (26 : ℕ) → Bool),
            (∀ x11 ∈ x8, x10 (Fin.castAdd (13 : ℕ) x11) = Bool.true) →
            (∀ x12 ∈ x9, x10 (Fin.natAdd (13 : ℕ) x12) = Bool.true) →
            PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 x10 = Bool.true) :
    let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size ≤ (63 : ℕ) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (1 : ℕ) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (1 : ℕ) → (∀ (x7 x8 : Fin (13 : ℕ)), x1 x7 x8 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8)) = Bool.true) → ∃ (x8 : Finset (Fin (13 : ℕ))) (x9 : Finset (Fin (13 : ℕ))), (∀ x10 ∈ x8, ∀ x12 ∈ x9, ¬x1 x10 x12) ∧ (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x8 | x1 x11 x10}.card ≤ (2 : ℕ)) ∧ (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x9 | x1 x10 x11}.card ≤ (2 : ℕ)) ∧ ∀ (x10 : Fin (26 : ℕ) → Bool), (∀ x11 ∈ x8, x10 (Fin.castAdd (13 : ℕ) x11) = Bool.true) → (∀ x12 ∈ x9, x10 (Fin.natAdd (13 : ℕ) x12) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 x10 = Bool.true :=
  fun x2 hmono hsize hnl hnp hinc =>
    @Decidable.byCases
      ({i : Fin x2.gates.length | (x2.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard ≤ (20 : ℕ))
      _
      (Nat.decLe {i : Fin x2.gates.length | (x2.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard (20 : ℕ))
      (fun h => h1 x2 hmono hsize hnl hnp h hinc)
      (fun hnot20 =>
        @Decidable.byCases
          ({i : Fin x2.gates.length | (x2.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard ≤ (35 : ℕ))
          _
          (Nat.decLe {i : Fin x2.gates.length | (x2.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard (35 : ℕ))
          (fun hle35 =>
            h2 x2 hmono hsize hnl hnp
              ⟨Nat.succ_le_of_lt (Nat.lt_of_not_ge hnot20), hle35⟩
              hinc)
          (fun hnot35 =>
            h3 x2 hmono hsize hnl hnp
              (Nat.succ_le_of_lt (Nat.lt_of_not_ge hnot35))
              hinc))
