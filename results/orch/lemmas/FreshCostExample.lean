import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2585.FreshCostExample

open PEqualNP.CircuitLowerBounds

-- Two disjoint three-leaf stars amplify the repeated edges without amplifying
-- the gap between this dirty circuit and the ordinary read-one construction.

def C : Circuit :=
  ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [8, 4]⟩,
    ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [10, 7]⟩,
    ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [9, 11]⟩,
    ⟨GateOp.or, [0, 11]⟩, ⟨GateOp.or, [1, 9]⟩,
    ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.and, [14, 15]⟩,
    ⟨GateOp.and, [16, 17]⟩], 18⟩

def D : Circuit :=
  ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [8, 4]⟩,
    ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [10, 7]⟩,
    ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [1, 11]⟩,
    ⟨GateOp.or, [12, 13]⟩], 14⟩

def E : List (ℕ × ℕ) := [(0, 2), (0, 3), (0, 4), (1, 5), (1, 6), (1, 7)]

def isLine (i : ℕ) : Bool := decide (2 ≤ i)

abbrev I (p : Fin 2) (l : Fin 6) : Prop :=
  (p = 0 ∧ l.val < 3) ∨ (p = 1 ∧ 3 ≤ l.val)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma valid_C : PEqualNP.TopForm.IsAO2 8 C := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma valid_D : PEqualNP.TopForm.IsAO2 8 D := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma no_four_cycle : ∀ p p' : Fin 2, ∀ l l' : Fin 6,
    p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l') := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma computes_C : ∀ z : Fin 8 → Bool,
    PEqualNP.MetaComplexity.circuitFun 8 C z =
      decide (∃ p : Fin 2, ∃ l : Fin 6, I p l ∧
        z (Fin.castAdd 6 p) = true ∧ z (Fin.natAdd 2 l) = true) := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma computes_D : ∀ z : Fin 8 → Bool,
    PEqualNP.MetaComplexity.circuitFun 8 D z =
      decide (∃ p : Fin 2, ∃ l : Fin 6, I p l ∧
        z (Fin.castAdd 6 p) = true ∧ z (Fin.natAdd 2 l) = true) := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma all_interior_not_below : ∀ w : Fin 18,
    ¬ PEqualNP.CircuitMoves.WireBelowOutput 8 C w.val := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma all_edges_double_reread : PEqualNP.ReadK.doubleReread C 8 isLine E = E := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma read_one_D : PEqualNP.ReadK.IsReadK 8 D 1 := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma sizes : C.size = 11 ∧ D.size = 7 := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma repeats_exceed_size_gap :
    C.size - D.size < (PEqualNP.ReadK.doubleReread C 8 isLine E).length := by decide

end PEqualNP.Outside.L_meta_2585.FreshCostExample
