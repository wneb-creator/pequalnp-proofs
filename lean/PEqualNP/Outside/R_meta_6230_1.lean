import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_6230_1
  (and_case : ∀ (C : Circuit), (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ (a : ℕ) (b : ℕ), g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) → (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ (x2 : Fin (13 : ℕ)) (x3 : Fin (13 : ℕ)), (x2 = x3 ∨ x2 = x3 + (1 : Fin (13 : ℕ)) ∨ x2 = x3 + (3 : Fin (13 : ℕ)) ∨ x2 = x3 + (9 : Fin (13 : ℕ))) ∧ x (Fin.castAdd (13 : ℕ) x2) = Bool.true ∧ x (Fin.natAdd (13 : ℕ) x3) = Bool.true) →
    (∀ a b : Fin 26, a ≠ b → ∃ gg : Gate, gg ∈ C.gates ∧ (a : ℕ) ∈ gg.inputs ∧ (b : ℕ) ∉ gg.inputs) → C.gates.head? = some ⟨GateOp.and, [0, 13]⟩ → 63 ≤ C.size)
  (or_case : ∀ (C : Circuit) (w : ℕ), w ∈ [(1 : ℕ), (13 : ℕ), (14 : ℕ)] →
    (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ (a : ℕ) (b : ℕ), g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) → (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ (x2 : Fin (13 : ℕ)) (x3 : Fin (13 : ℕ)), (x2 = x3 ∨ x2 = x3 + (1 : Fin (13 : ℕ)) ∨ x2 = x3 + (3 : Fin (13 : ℕ)) ∨ x2 = x3 + (9 : Fin (13 : ℕ))) ∧ x (Fin.castAdd (13 : ℕ) x2) = Bool.true ∧ x (Fin.natAdd (13 : ℕ) x3) = Bool.true) → (∀ a b : Fin 26, a ≠ b → ∃ gg : Gate, gg ∈ C.gates ∧ (a : ℕ) ∈ gg.inputs ∧ (b : ℕ) ∉ gg.inputs) →
    C.gates.head? = some ⟨GateOp.or, [0, w]⟩ → 63 ≤ C.size)
  (head_some : ∀ (C : Circuit), (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ (a : ℕ) (b : ℕ), g.inputs = [a, b] ∧ a ≠ b ∧ a < 26 + j ∧ b < 26 + j) → (∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔ ∃ (x2 : Fin (13 : ℕ)) (x3 : Fin (13 : ℕ)), (x2 = x3 ∨ x2 = x3 + (1 : Fin (13 : ℕ)) ∨ x2 = x3 + (3 : Fin (13 : ℕ)) ∨ x2 = x3 + (9 : Fin (13 : ℕ))) ∧ x (Fin.castAdd (13 : ℕ) x2) = Bool.true ∧ x (Fin.natAdd (13 : ℕ) x3) = Bool.true) → C.gates.head? ≠ none) :
  (have x1 : (Fin (26 : ℕ) → Bool) → Prop := fun (x1 : Fin (26 : ℕ) → Bool) => ∃ (x2 : Fin (13 : ℕ)) (x3 : Fin (13 : ℕ)), (x2 = x3 ∨ x2 = x3 + (1 : Fin (13 : ℕ)) ∨ x2 = x3 + (3 : Fin (13 : ℕ)) ∨ x2 = x3 + (9 : Fin (13 : ℕ))) ∧ x1 (Fin.castAdd (13 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (13 : ℕ) x3) = Bool.true; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (26 : ℕ) + x3 ∧ x7 < (26 : ℕ) + x3; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x4 : Fin (26 : ℕ) → Bool), x3.eval (List.ofFn x4) = Bool.true ↔ x1 x4; have x4 : PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [(0 : ℕ), (13 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∨ ∃ x5 ∈ [(1 : ℕ), (13 : ℕ), (14 : ℕ)], x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), x5] : PEqualNP.CircuitLowerBounds.Gate }; ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x2 x5 → x3 x5 → (∀ (x8 : PEqualNP.CircuitLowerBounds.Gate), x5.gates.head? = Option.some x8 → x4 x8) → (∀ (x9 x10 : Fin (26 : ℕ)), x9 ≠ x10 → ∃ x12 ∈ x5.gates, ↑x9 ∈ x12.inputs ∧ ↑x10 ∉ x12.inputs) → (63 : ℕ) ≤ x5.size) := by
  intro Inc AO2 Comp First C hAO hComp hHead hSep
  have hne := head_some C hAO hComp
  obtain ⟨gg, hgg'⟩ := Option.ne_none_iff_exists.mp hne
  have hgg : C.gates.head? = some gg := hgg'.symm
  have hfirst := hHead gg hgg
  rcases hfirst with hfirst | ⟨w, hwmem, hw⟩
  · apply and_case C hAO hComp hSep
    simpa [hfirst] using hgg
  · apply or_case C w hwmem hAO hComp hSep
    simpa [hw] using hgg
