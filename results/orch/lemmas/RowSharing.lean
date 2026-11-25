import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675.RowSharing

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.TwoColour

def circuit : Circuit :=
  ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.and, [1, 3]⟩,
    ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [7, 4]⟩,
    ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [8, 9]⟩], 10⟩

def edges : Finset (Fin 2 × Fin 3) := {(0, 0), (0, 2), (1, 1), (1, 2)}

lemma circuit_ao : IsAO2 5 circuit := by decide

lemma circuit_zero : tCount 5 circuit (fun i => decide (2 ≤ i)) = 0 := by decide

lemma no_rectangle : ∀ (a a' : Fin 2) (b b' : Fin 3), a ≠ a' → b ≠ b' →
    ¬ ((a, b) ∈ edges ∧ (a, b') ∈ edges ∧ (a', b) ∈ edges ∧ (a', b') ∈ edges) := by
  decide

lemma circuit_value : ∀ x : Fin 5 → Bool,
    PEqualNP.MetaComplexity.circuitFun 5 circuit x =
      decide (∃ (a : Fin 2) (b : Fin 3), (a, b) ∈ edges ∧
        x (Fin.castAdd 3 a) = true ∧ x (Fin.natAdd 2 b) = true) := by
  decide

def rowInput (a : Fin 2) (y : Fin 3 → Bool) : Fin 5 → Bool :=
  fun i => if h : i.val < 2 then decide (a.val = i.val) else y ⟨i.val - 2, by omega⟩

lemma shared_or_left : ∀ y : Fin 3 → Bool,
    PEqualNP.EdgeOwnership.gateVal 5 circuit 3 (rowInput 0 y) =
      (y 0 || y 2) := by decide

lemma shared_or_right : ∀ y : Fin 3 → Bool,
    PEqualNP.EdgeOwnership.gateVal 5 circuit 3 (rowInput 1 y) =
      (y 1 || y 2) := by decide

lemma shared_or_reach : orIn 5 circuit 8 = {4} := by decide

end PEqualNP.Outside.L_meta_4675.RowSharing
