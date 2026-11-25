namespace PEqualNP.Outside.L_meta_3451_aux.Two

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma normalize_with_certificate
    (cert : ∀ r : Fin 16, 0 < Four.bound r →
      Four.possible (Four.bound r - 1) Four.inputs (Four.target r) = false)
    (I : Fin 2 → Fin 2 → Prop) [DecidableRel I] (C : Circuit)
    (hm : Monotone2 C) (hb : NestedCover.ReadsBack 4 C)
    (sem : ∀ z : Fin 4 → Bool, circuitFun 4 C z = true ↔
      ∃ p l : Fin 2, I p l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 2 l) = true) :
    ∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack 4 D ∧ D.size ≤ C.size ∧
      (∀ z : Fin 4 → Bool, circuitFun 4 D z = true ↔
        ∃ p l : Fin 2, I p l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 2 l) = true) ∧
      (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
        ∀ p l : Fin 2, ¬ I p l →
          (D.wires (List.ofFn (fun k : Fin 4 =>
            decide (k = Fin.castAdd 2 p ∨ k = Fin.natAdd 2 l)))).getD (4 + j) false = false) ∧
      (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
        (∀ p : Fin 2, (D.wires (List.ofFn (fun k : Fin 4 =>
          decide (k = Fin.castAdd 2 p)))).getD (4 + j) false = false) ∧
        ∀ l : Fin 2, (D.wires (List.ofFn (fun k : Fin 4 =>
          decide (k = Fin.natAdd 2 l)))).getD (4 + j) false = false) := by
  apply from_size I C
  rw [witness_size]
  apply Four.lower_bound_with_certificate cert _ C hm hb
  intro x
  rw [circuit_truth I C sem, Four.target_bits]
  obtain ⟨ha, hb, hc, hd⟩ := code_bits (decide (I 0 0)) (decide (I 0 1))
    (decide (I 1 0)) (decide (I 1 1))
  simp only [ha, hb, hc, hd, truth]

lemma normalize
    (I : Fin 2 → Fin 2 → Prop) [DecidableRel I] (C : Circuit)
    (hm : Monotone2 C) (hb : NestedCover.ReadsBack 4 C)
    (sem : ∀ z : Fin 4 → Bool, circuitFun 4 C z = true ↔
      ∃ p l : Fin 2, I p l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 2 l) = true) :
    ∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack 4 D ∧ D.size ≤ C.size ∧
      (∀ z : Fin 4 → Bool, circuitFun 4 D z = true ↔
        ∃ p l : Fin 2, I p l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 2 l) = true) ∧
      (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
        ∀ p l : Fin 2, ¬ I p l →
          (D.wires (List.ofFn (fun k : Fin 4 =>
            decide (k = Fin.castAdd 2 p ∨ k = Fin.natAdd 2 l)))).getD (4 + j) false = false) ∧
      (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
        (∀ p : Fin 2, (D.wires (List.ofFn (fun k : Fin 4 =>
          decide (k = Fin.castAdd 2 p)))).getD (4 + j) false = false) ∧
        ∀ l : Fin 2, (D.wires (List.ofFn (fun k : Fin 4 =>
          decide (k = Fin.natAdd 2 l)))).getD (4 + j) false = false) :=
  normalize_with_certificate Four.certificate I C hm hb sem

end PEqualNP.Outside.L_meta_3451_aux.Two
