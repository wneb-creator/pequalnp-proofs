import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3262_2
    (junkfree : ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (π : Equiv.Perm (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), 0 < n →
      (∀ (x5 x6 x7 x8 : Fin n), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ E ∧ (x5, x8) ∈ E ∧ (x6, x7) ∈ E ∧ (x6, x8) ∈ E)) → (∀ (x6 : Fin n), (x6, π x6) ∈ E) → PEqualNP.TopForm.IsAO2 (n + n) C → (∀ (x8 : Fin (n + n) → Bool), PEqualNP.MetaComplexity.circuitFun (n + n) C x8 = Decidable.decide (∃ (x9 : Fin n) (x10 : Fin n), (x9, x10) ∈ E ∧ x8 (Fin.castAdd n x9) = Bool.true ∧ x8 (Fin.natAdd n x10) = Bool.true)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, D.size ≤ C.size ∧ PEqualNP.TopForm.IsAO2 (n + n) D ∧ (∀ x : Fin (n + n) → Bool, PEqualNP.MetaComplexity.circuitFun (n + n) D x = PEqualNP.MetaComplexity.circuitFun (n + n) C x) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ x : Fin (n + n) → Bool, PEqualNP.EdgeOwnership.gateVal (n + n) D j x = true → ∃ a b : Fin n, (a, b) ∈ E ∧ x (Fin.castAdd n a) = true ∧ x (Fin.natAdd n b) = true))
    (count : ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (π : Equiv.Perm (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), 0 < n →
      (∀ (x5 x6 x7 x8 : Fin n), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ E ∧ (x5, x8) ∈ E ∧ (x6, x7) ∈ E ∧ (x6, x8) ∈ E)) → (∀ (x6 : Fin n), (x6, π x6) ∈ E) → PEqualNP.TopForm.IsAO2 (n + n) C → (∀ (x8 : Fin (n + n) → Bool), PEqualNP.MetaComplexity.circuitFun (n + n) C x8 = Decidable.decide (∃ (x9 : Fin n) (x10 : Fin n), (x9, x10) ∈ E ∧ x8 (Fin.castAdd n x9) = Bool.true ∧ x8 (Fin.natAdd n x10) = Bool.true)) → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ x : Fin (n + n) → Bool, PEqualNP.EdgeOwnership.gateVal (n + n) C j x = true → ∃ a b : Fin n, (a, b) ∈ E ∧ x (Fin.castAdd n a) = true ∧ x (Fin.natAdd n b) = true) → E.card + n ≤ C.size + 1) :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 x7 x8 : Fin x1), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ x2 ∧ (x5, x8) ∈ x2 ∧ (x6, x7) ∈ x2 ∧ (x6, x8) ∈ x2)) → (∀ (x6 : Fin x1), (x6, x3 x6) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x8 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x1), (x9, x10) ∈ x2 ∧ x8 (Fin.castAdd x1 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → x2.card + x1 ≤ x4.size + (1 : ℕ) := by
  intro n E π C square matching model computes
  by_cases hn : n = 0
  · subst n
    have h0 : E.card = 0 := Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr (fun e _ => Fin.elim0 e.1))
    omega
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  obtain ⟨D, hsize, hDmodel, hDeq, hDjunk⟩ := junkfree n E π C hnpos square matching model computes
  have hDcomputes : (∀ x : Fin (n + n) → Bool, PEqualNP.MetaComplexity.circuitFun (n + n) D x = Decidable.decide (∃ (x9 : Fin n) (x10 : Fin n), (x9, x10) ∈ E ∧ x (Fin.castAdd n x9) = Bool.true ∧ x (Fin.natAdd n x10) = Bool.true)) := fun x => (hDeq x).trans (computes x)
  have h := count n E π D hnpos square matching hDmodel hDcomputes hDjunk
  omega
