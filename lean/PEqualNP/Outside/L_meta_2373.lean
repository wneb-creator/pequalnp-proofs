import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_2373

def edge (x : Fin 10 → Bool) : Bool :=
    x 0 && x 1 ||
    x 1 && x 2 ||
    x 2 && x 3 ||
    x 3 && x 4 ||
    x 4 && x 0 ||
    x 0 && x 5 ||
    x 1 && x 6 ||
    x 2 && x 7 ||
    x 3 && x 8 ||
    x 4 && x 9 ||
    x 5 && x 7 ||
    x 7 && x 9 ||
    x 9 && x 6 ||
    x 6 && x 8 ||
    x 8 && x 5

def upperCircuit : Circuit :=
  ⟨[⟨GateOp.or, [1, 4]⟩,
      ⟨GateOp.or, [10, 5]⟩,
      ⟨GateOp.and, [0, 11]⟩,
      ⟨GateOp.or, [2, 6]⟩,
      ⟨GateOp.and, [1, 13]⟩,
      ⟨GateOp.or, [2, 4]⟩,
      ⟨GateOp.or, [15, 8]⟩,
      ⟨GateOp.and, [3, 16]⟩,
      ⟨GateOp.or, [2, 5]⟩,
      ⟨GateOp.or, [18, 9]⟩,
      ⟨GateOp.and, [7, 19]⟩,
      ⟨GateOp.or, [6, 5]⟩,
      ⟨GateOp.and, [8, 21]⟩,
      ⟨GateOp.or, [4, 6]⟩,
      ⟨GateOp.and, [9, 23]⟩,
      ⟨GateOp.or, [12, 14]⟩,
      ⟨GateOp.or, [25, 17]⟩,
      ⟨GateOp.or, [26, 20]⟩,
      ⟨GateOp.or, [27, 22]⟩,
      ⟨GateOp.or, [28, 24]⟩], 29⟩

lemma upperCircuit_size : upperCircuit.size = 20 := rfl

lemma upperCircuit_fanInTwo : FanInTwo upperCircuit := by
  simp [FanInTwo, upperCircuit]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
lemma upperCircuit_computes : ∀ x : Fin 10 → Bool,
    upperCircuit.eval (List.ofFn x) = edge x := by
  decide

lemma upper_bound : HasCircuitSize 10 edge 20 :=
  ⟨upperCircuit, upperCircuit_fanInTwo, le_of_eq upperCircuit_size, upperCircuit_computes⟩

lemma five_cycle_cover_weight (a b c d e : Nat)
    (hab : 1 ≤ a + b) (hbc : 1 ≤ b + c) (hcd : 1 ≤ c + d)
    (hde : 1 ≤ d + e) (hea : 1 ≤ e + a) : 3 ≤ a + b + c + d + e := by
  omega

lemma petersen_cover_weight (w : Fin 10 → Nat)
    (h01 : 1 ≤ w 0 + w 1) (h12 : 1 ≤ w 1 + w 2)
    (h23 : 1 ≤ w 2 + w 3) (h34 : 1 ≤ w 3 + w 4)
    (h40 : 1 ≤ w 4 + w 0) (h57 : 1 ≤ w 5 + w 7)
    (h79 : 1 ≤ w 7 + w 9) (h96 : 1 ≤ w 9 + w 6)
    (h68 : 1 ≤ w 6 + w 8) (h85 : 1 ≤ w 8 + w 5) :
    6 ≤ w 0 + w 1 + w 2 + w 3 + w 4 + w 5 + w 6 + w 7 + w 8 + w 9 := by
  have ho := five_cycle_cover_weight (w 0) (w 1) (w 2) (w 3) (w 4)
    h01 h12 h23 h34 h40
  have hi := five_cycle_cover_weight (w 5) (w 7) (w 9) (w 6) (w 8)
    h57 h79 h96 h68 h85
  omega


end PEqualNP.Outside.L_meta_2373
