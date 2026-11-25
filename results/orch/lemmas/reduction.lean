import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3451_51
    (h1 : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      let good := fun C : PEqualNP.CircuitLowerBounds.Circuit =>
        PEqualNP.MetaComplexity.Monotone2 C ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C ∧
        (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔
          ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
      let single := fun C : PEqualNP.CircuitLowerBounds.Circuit =>
        ∀ j < C.gates.length,
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
            PEqualNP.CircuitLowerBounds.GateOp.and →
          ∀ k : Fin (N + N), PEqualNP.EdgeOwnership.gateVal (N + N) C j
            (PEqualNP.EdgeOwnership.pairInput k k) = false
      (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      ∀ C, good C → ∃ D, good D ∧ D.size ≤ C.size ∧ single D)
    (h2 : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      let good := fun C : PEqualNP.CircuitLowerBounds.Circuit =>
        PEqualNP.MetaComplexity.Monotone2 C ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C ∧
        (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔
          ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
      let single := fun C : PEqualNP.CircuitLowerBounds.Circuit =>
        ∀ j < C.gates.length,
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
            PEqualNP.CircuitLowerBounds.GateOp.and →
          ∀ k : Fin (N + N), PEqualNP.EdgeOwnership.gateVal (N + N) C j
            (PEqualNP.EdgeOwnership.pairInput k k) = false
      (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      ∀ C, good C → single C → ∃ D, good D ∧ D.size ≤ C.size ∧ single D ∧
        ∀ j < D.gates.length,
          (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op =
            PEqualNP.CircuitLowerBounds.GateOp.and →
          ∀ p l : Fin N, ¬ I p l → PEqualNP.EdgeOwnership.gateVal (N + N) D j
            (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd N p) (Fin.natAdd N l)) = false) :
    ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ p0 l0 : Fin N, ¬ I p0 l0 → (D.wires (List.ofFn (fun ke : Fin (N + N) => decide (ke = Fin.castAdd N p0 ∨ ke = Fin.natAdd N l0)))).getD (N + N + j) false = false) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  intro N I inst C h4 hmono hback hfun
  obtain ⟨B, hBgood, hBsize, hBsingle⟩ := h1 N I h4 C ⟨hmono, hback, hfun⟩
  obtain ⟨D, hDgood, hDsize, hDsingle, hDpair⟩ := h2 N I h4 B hBgood hBsingle
  refine ⟨D, hDgood.1, hDgood.2.1, hDsize.trans hBsize, hDgood.2.2, ?_, ?_⟩
  · exact hDpair
  · intro j hj hand
    constructor
    · intro p
      simpa only [PEqualNP.EdgeOwnership.gateVal, PEqualNP.EdgeOwnership.pairInput,
        or_self] using hDsingle j hj hand (Fin.castAdd N p)
    · intro l
      simpa only [PEqualNP.EdgeOwnership.gateVal, PEqualNP.EdgeOwnership.pairInput,
        or_self] using hDsingle j hj hand (Fin.natAdd N l)
