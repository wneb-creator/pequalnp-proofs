import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5270_1
    (hOut :
      have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ)); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (List.filter (fun (x4 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x4)) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates)).Nodup; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2 x4 → ¬x3 x4 → (14 : ℕ) ≤ x4.output → x4.output ∈ List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(0 : ℕ)} → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ)} → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), x2 x9 ∧ x3 x9 ∧ (2 : ℕ) ≤ x9.lineDeg (14 : ℕ) {(0 : ℕ)} ∧ (2 : ℕ) ≤ x9.lineDeg (14 : ℕ) {(7 : ℕ)})
    (hInt :
      have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ)); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (List.filter (fun (x4 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x4)) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates)).Nodup; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2 x4 → ¬x3 x4 → (∃ (w : ℕ), (14 : ℕ) ≤ w ∧ w ≠ x4.output ∧ (2 : ℕ) ≤ List.count w (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates)) → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(0 : ℕ)} → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ)} → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), x2 x9 ∧ x3 x9 ∧ (2 : ℕ) ≤ x9.lineDeg (14 : ℕ) {(0 : ℕ)} ∧ (2 : ℕ) ≤ x9.lineDeg (14 : ℕ) {(7 : ℕ)}) :
    have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ)); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (List.filter (fun (x4 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x4)) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates)).Nodup; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2 x4 → ¬x3 x4 → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(0 : ℕ)} → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ)} → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), x2 x9 ∧ x3 x9 ∧ (2 : ℕ) ≤ x9.lineDeg (14 : ℕ) {(0 : ℕ)} ∧ (2 : ℕ) ≤ x9.lineDeg (14 : ℕ) {(7 : ℕ)} := by
  intro x1 x2 x3 x4 hx2 hnx3 hd0 hd7
  have hnot_le1 : ¬ ∀ w : ℕ, List.count w (List.filter (fun a => Decidable.decide (14 ≤ a)) (x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates)) ≤ 1 := by
    intro hall
    exact hnx3 (List.nodup_iff_count_le_one.mpr hall)
  obtain ⟨w, hwgt⟩ := Classical.not_forall.mp hnot_le1
  have hw2 : 2 ≤ List.count w (List.filter (fun a => Decidable.decide (14 ≤ a)) (x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates)) := by
    omega
  have hwmem : w ∈ (List.filter (fun a => Decidable.decide (14 ≤ a)) (x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates)) :=
    List.count_pos_iff.mp (by omega)
  have hw14 : 14 ≤ w := of_decide_eq_true (List.mem_filter.mp hwmem).2
  have hwcnt : 2 ≤ List.count w (x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) :=
    le_trans hw2 (List.Sublist.count_le w List.filter_sublist)
  by_cases hwout : w = x4.output
  · subst hwout
    have hflat_pos : 0 < List.count x4.output (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) := by
      rw [List.count_cons] at hwcnt
      split at hwcnt <;> omega
    exact hOut x4 hx2 hnx3 hw14 (List.count_pos_iff.mp hflat_pos) hd0 hd7
  · have hcntF : 2 ≤ List.count w (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) := by
      rwa [List.count_cons_of_ne (show x4.output ≠ w from fun h => hwout h.symm)] at hwcnt
    exact hInt x4 hx2 hnx3 ⟨w, hw14, hwout, hcntF⟩ hd0 hd7
