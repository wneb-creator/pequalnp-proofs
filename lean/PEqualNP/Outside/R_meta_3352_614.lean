import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3352_614
    (normalize :
      have f : (Fin 9 → Bool) → Bool := fun x =>
        [1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85].any fun e : ℕ =>
          x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10));
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo C →
        (∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) →
        (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) →
        C.size ≤ 15 → PEqualNP.MetaComplexity.circuitFun 9 C = f →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.MetaComplexity.FanInTwo D ∧
          (∀ g ∈ D.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) ∧
          D.size = 15 ∧ D.output = 23 ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt D 0).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
          ((PEqualNP.MetaComplexity.NestedCover.gateAt D 0).inputs = [0, 2] ∨
            (PEqualNP.MetaComplexity.NestedCover.gateAt D 0).inputs = [2, 0]) ∧
          PEqualNP.MetaComplexity.circuitFun 9 D = PEqualNP.MetaComplexity.circuitFun 9 C ∧
          ∀ w, D.gates.countP (fun g => g.inputs.contains w) ≤ C.gates.countP (fun g => g.inputs.contains w))
    (lastCase :
      have f : (Fin 9 → Bool) → Bool := fun x =>
        [1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85].any fun e : ℕ =>
          x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10));
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo D →
        (∀ g ∈ D.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) →
        D.size = 15 → D.output = 23 →
        (PEqualNP.MetaComplexity.NestedCover.gateAt D 0).op = PEqualNP.CircuitLowerBounds.GateOp.or →
        ((PEqualNP.MetaComplexity.NestedCover.gateAt D 0).inputs = [0, 2] ∨
          (PEqualNP.MetaComplexity.NestedCover.gateAt D 0).inputs = [2, 0]) →
        (∀ i : Fin 3, D.gates.countP (fun g => g.inputs.contains (![4, 6, 7] i)) ≤ 2) →
        PEqualNP.MetaComplexity.circuitFun 9 D ≠ f) :
have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ x4 ∈ x2.gates, x4.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → (∀ (x5 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x5)).getD (9 : ℕ) Bool.false = (x5 (0 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)))) → x2.size ≤ (15 : ℕ) → (∀ (x7 : Fin (3 : ℕ)), List.countP (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => x8.inputs.contains (![(4 : ℕ), (6 : ℕ), (7 : ℕ)] x7)) x2.gates ≤ (2 : ℕ)) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 ≠ x1
 := by
  intro f C fan noNot preset size counts computes
  obtain ⟨D, dFan, dNoNot, dSize, dOutput, firstOp, firstInputs, same, reads⟩ :=
    normalize C fan noNot preset size computes
  exact lastCase D dFan dNoNot dSize dOutput firstOp firstInputs
    (fun i => (reads (![4, 6, 7] i)).trans (counts i)) (same.trans computes)
