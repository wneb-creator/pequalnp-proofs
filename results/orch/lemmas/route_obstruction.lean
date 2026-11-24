import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3451.RouteObstruction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- This example defeats a local operand replacement, not the posted statement.
-- The same matching has the clean three-gate circuit below.

def matching (z : Fin 4 → Bool) : Bool := (z 0 && z 2) || (z 1 && z 3)

def pairInput (p l : Fin 2) (k : Fin 4) : Bool :=
  decide (k = Fin.castAdd 2 p ∨ k = Fin.natAdd 2 l)

def points (k : Fin 4) : Bool := decide (k.val < 2)

def lines (k : Fin 4) : Bool := decide (2 ≤ k.val)

def circuit7 : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.and, [4, 5]⟩,
    ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [2, 1]⟩, ⟨GateOp.and, [7, 8]⟩,
    ⟨GateOp.and, [6, 9]⟩], 10⟩

def circuit3 : Circuit :=
  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [4, 5]⟩], 6⟩

lemma matching_incidence : ∀ z : Fin 4 → Bool, matching z = true ↔
    ∃ p l : Fin 2, p = l ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 2 l) = true := by
  decide

lemma matching_fourcycle_free : ∀ p p' l l' : Fin 2, p ≠ p' → l ≠ l' →
    ¬ (p = l ∧ p = l' ∧ p' = l ∧ p' = l') := by
  decide

lemma circuit7_correct : ∀ z : Fin 4 → Bool, circuitFun 4 circuit7 z = matching z := by
  decide

lemma circuit7_monotone : Monotone2 circuit7 := by
  simp [Monotone2, circuit7]

lemma circuit7_readsBack : ReadsBack 4 circuit7 := by
  decide

lemma circuit7_size : circuit7.size = 7 := rfl

lemma circuit7_dirty_and : ∀ j < circuit7.gates.length,
    (gateAt circuit7 j).op = GateOp.and →
    ((∃ p l : Fin 2, p ≠ l ∧
      (circuit7.wires (List.ofFn (pairInput p l))).getD (4 + j) false = true) ↔ j = 2) := by
  letI := gateOpDecEq
  decide

lemma point_operand_bypass_fails :
    circuitFun 4 (PEqualNP.CircuitMoves.eraseGate 4 circuit7 2 4) points = true ∧
      matching points = false := by
  decide

lemma line_operand_bypass_fails :
    circuitFun 4 (PEqualNP.CircuitMoves.eraseGate 4 circuit7 2 5) lines = true ∧
      matching lines = false := by
  decide

lemma circuit3_correct : ∀ z : Fin 4 → Bool, circuitFun 4 circuit3 z = matching z := by
  decide

lemma circuit3_monotone : Monotone2 circuit3 := by
  simp [Monotone2, circuit3]

lemma circuit3_readsBack : ReadsBack 4 circuit3 := by
  decide

lemma circuit3_size : circuit3.size = 3 := rfl

lemma circuit3_clean : ∀ j < circuit3.gates.length,
    (gateAt circuit3 j).op = GateOp.and →
    (∀ p l : Fin 2, p ≠ l →
      (circuit3.wires (List.ofFn (pairInput p l))).getD (4 + j) false = false) ∧
    (∀ p : Fin 2,
      (circuit3.wires (List.ofFn (fun k : Fin 4 => decide (k = Fin.castAdd 2 p)))).getD
        (4 + j) false = false) ∧
    (∀ l : Fin 2,
      (circuit3.wires (List.ofFn (fun k : Fin 4 => decide (k = Fin.natAdd 2 l)))).getD
        (4 + j) false = false) := by
  letI := gateOpDecEq
  decide

end PEqualNP.Outside.L_meta_3451.RouteObstruction
