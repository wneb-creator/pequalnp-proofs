import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_2583_1
    (normalize : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
          z (Fin.natAdd N l) = true)) →
      ∃ D : Circuit, IsAO2 (N + N) D ∧
        circuitFun (N + N) D = circuitFun (N + N) C ∧ D.size ≤ C.size ∧
        ∀ g ∈ D.gates, g.op = GateOp.and → ∀ w ∈ g.inputs,
        let V : (Fin (N + N) → Bool) → Bool :=
          fun z => (D.wires (List.ofFn z)).getD w false
        ∀ z : Fin (N + N) → Bool,
          V z = (V (fun i => if i.val < N then z i else false) ||
            V (fun i => if N ≤ i.val then z i else false)))
    (lower : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
          z (Fin.natAdd N l) = true)) →
      (∀ g ∈ C.gates, g.op = GateOp.and → ∀ w ∈ g.inputs,
        let V : (Fin (N + N) → Bool) → Bool :=
          fun z => (C.wires (List.ofFn z)).getD w false
        ∀ z : Fin (N + N) → Bool,
          V z = (V (fun i => if i.val < N then z i else false) ||
            V (fun i => if N ≤ i.val then z i else false))) → N * (q + 2) - 1 ≤ C.size)
    (upper : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      ∃ D : Circuit, IsAO2 (N + N) D ∧
        (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z =
          decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
            z (Fin.natAdd N l) = true)) ∧
        D.size ≤ N * (q + 2) - 1 ∧ PEqualNP.ReadK.IsReadK (N + N) D 1) :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧ (∀ y : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D y = decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true)) ∧ D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (N + N) D 1 := by
  intro q N I inst C hq hN hL hPair hC hfun
  have hLcard : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1 := by
    intro l
    simpa only [Fintype.card_subtype] using hL l
  obtain ⟨D, hD, hEq, hDC, hSep⟩ := normalize q N I C hq hN hLcard hPair hC hfun
  have hDfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
        z (Fin.natAdd N l) = true) := by
    intro z
    rw [hEq]
    exact hfun z
  have hBound := lower q N I D hq hN hLcard hPair hD hDfun hSep
  obtain ⟨E, hE, hEfun, hSize, hRead⟩ := upper q N I hLcard
  exact ⟨E, hE, hEfun, hSize.trans (hBound.trans hDC), hRead⟩
