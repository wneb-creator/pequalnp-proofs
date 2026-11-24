lemma padSuffices (hclean : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ p0 l0 : Fin N, ¬ I p0 l0 → (D.wires (List.ofFn (fun ke : Fin (N + N) => decide (ke = Fin.castAdd N p0 ∨ ke = Fin.natAdd N l0)))).getD (N + N + j) false = false)) :
    ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ p0 l0 : Fin N, ¬ I p0 l0 → (D.wires (List.ofFn (fun ke : Fin (N + N) => decide (ke = Fin.castAdd N p0 ∨ ke = Fin.natAdd N l0)))).getD (N + N + j) false = false) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  intro N I inst C hfour hC hrC hfC
  classical
  let C' := zResCircuit (padLift (N := N)) C
  have hC' : Monotone2 C' := zRes_monotone _ _ hC
  have hrC' : ReadsBack ((N + 1) + (N + 1)) C' := zRes_readsBack _ _ hrC
  have hfC' := padLift_computes I C hC hfC
  obtain ⟨D, hD, hrD, hsD, hfD, hpD⟩ :=
    hclean (N + 1) (padI I) C' (padI_noRect I hfour) hC' hrC' hfC'
  have hsingle := decAndSingletons (N + 1) (padI I) D hD
    (fun p => ⟨Fin.last N, padI_line_last I p⟩)
    (fun l => ⟨Fin.last N, padI_point_last I l⟩) hpD
  let E := zResCircuit (padDrop (N := N)) D
  refine ⟨E, zRes_monotone _ _ hD, zRes_readsBack _ _ hrD, ?_,
    padDrop_computes I D hD hfD, ?_, ?_⟩
  · simpa only [E, C', zRes_size] using hsD
  · intro j hj hand p l hpl
    have hj' : j < D.gates.length := by simpa [E, zResCircuit] using hj
    have hand' : (gateAt D j).op = .and :=
      zRes_and_source _ _ (by simpa only [E, zRes_gateAt] using hand)
    change ((zResCircuit (padDrop (N := N)) D).wires _).getD (N + N + j) false = false
    rw [zRes_wires_gate _ _ hD, padDrop_pair]
    exact hpD j hj' hand' p.castSucc l.castSucc (fun h => hpl ((padI_cast I p l).mp h))
  · intro j hj hand
    have hj' : j < D.gates.length := by simpa [E, zResCircuit] using hj
    have hand' : (gateAt D j).op = .and :=
      zRes_and_source _ _ (by simpa only [E, zRes_gateAt] using hand)
    constructor
    · intro p
      change ((zResCircuit (padDrop (N := N)) D).wires _).getD (N + N + j) false = false
      rw [zRes_wires_gate _ _ hD, padDrop_point]
      exact (hsingle j hj' hand').1 p.castSucc
    · intro l
      change ((zResCircuit (padDrop (N := N)) D).wires _).getD (N + N + j) false = false
      rw [zRes_wires_gate _ _ hD, padDrop_line]
      exact (hsingle j hj' hand').2 l.castSucc
