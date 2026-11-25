import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_650
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def baseline : Circuit :=
  ⟨[
    ⟨GateOp.or, [13, 14]⟩,
    ⟨GateOp.or, [26, 16]⟩,
    ⟨GateOp.or, [27, 22]⟩,
    ⟨GateOp.and, [0, 28]⟩,
    ⟨GateOp.or, [13, 15]⟩,
    ⟨GateOp.or, [30, 21]⟩,
    ⟨GateOp.or, [31, 25]⟩,
    ⟨GateOp.and, [1, 32]⟩,
    ⟨GateOp.or, [14, 20]⟩,
    ⟨GateOp.or, [34, 24]⟩,
    ⟨GateOp.or, [35, 25]⟩,
    ⟨GateOp.and, [2, 36]⟩,
    ⟨GateOp.or, [13, 19]⟩,
    ⟨GateOp.or, [38, 23]⟩,
    ⟨GateOp.or, [39, 24]⟩,
    ⟨GateOp.and, [3, 40]⟩,
    ⟨GateOp.or, [18, 22]⟩,
    ⟨GateOp.or, [42, 23]⟩,
    ⟨GateOp.or, [43, 25]⟩,
    ⟨GateOp.and, [4, 44]⟩,
    ⟨GateOp.or, [17, 21]⟩,
    ⟨GateOp.or, [46, 22]⟩,
    ⟨GateOp.or, [47, 24]⟩,
    ⟨GateOp.and, [5, 48]⟩,
    ⟨GateOp.or, [16, 20]⟩,
    ⟨GateOp.or, [50, 21]⟩,
    ⟨GateOp.or, [51, 23]⟩,
    ⟨GateOp.and, [6, 52]⟩,
    ⟨GateOp.or, [15, 19]⟩,
    ⟨GateOp.or, [54, 20]⟩,
    ⟨GateOp.or, [55, 22]⟩,
    ⟨GateOp.and, [7, 56]⟩,
    ⟨GateOp.or, [14, 18]⟩,
    ⟨GateOp.or, [58, 19]⟩,
    ⟨GateOp.or, [59, 21]⟩,
    ⟨GateOp.and, [8, 60]⟩,
    ⟨GateOp.or, [13, 17]⟩,
    ⟨GateOp.or, [62, 18]⟩,
    ⟨GateOp.or, [63, 20]⟩,
    ⟨GateOp.and, [9, 64]⟩,
    ⟨GateOp.or, [16, 17]⟩,
    ⟨GateOp.or, [66, 19]⟩,
    ⟨GateOp.or, [67, 25]⟩,
    ⟨GateOp.and, [10, 68]⟩,
    ⟨GateOp.or, [15, 16]⟩,
    ⟨GateOp.or, [70, 18]⟩,
    ⟨GateOp.or, [71, 24]⟩,
    ⟨GateOp.and, [11, 72]⟩,
    ⟨GateOp.or, [14, 15]⟩,
    ⟨GateOp.or, [74, 17]⟩,
    ⟨GateOp.or, [75, 23]⟩,
    ⟨GateOp.and, [12, 76]⟩,
    ⟨GateOp.or, [29, 33]⟩,
    ⟨GateOp.or, [78, 37]⟩,
    ⟨GateOp.or, [79, 41]⟩,
    ⟨GateOp.or, [80, 45]⟩,
    ⟨GateOp.or, [81, 49]⟩,
    ⟨GateOp.or, [82, 53]⟩,
    ⟨GateOp.or, [83, 57]⟩,
    ⟨GateOp.or, [84, 61]⟩,
    ⟨GateOp.or, [85, 65]⟩,
    ⟨GateOp.or, [86, 69]⟩,
    ⟨GateOp.or, [87, 73]⟩,
    ⟨GateOp.or, [88, 77]⟩
  ], 89⟩

lemma baseline_size : baseline.size = 64 := rfl

lemma baseline_monotone : Monotone2 baseline := by
  simp [baseline, Monotone2]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma baseline_eval (x : Fin 26 → Bool) :
    baseline.eval (List.ofFn x) =
    ((x 0 && (x 13 || x 14 || x 16 || x 22)) || (x 1 && (x 13 || x 15 || x 21 || x 25)) || (x 2 && (x 14 || x 20 || x 24 || x 25)) || (x 3 && (x 13 || x 19 || x 23 || x 24)) || (x 4 && (x 18 || x 22 || x 23 || x 25)) || (x 5 && (x 17 || x 21 || x 22 || x 24)) || (x 6 && (x 16 || x 20 || x 21 || x 23)) || (x 7 && (x 15 || x 19 || x 20 || x 22)) || (x 8 && (x 14 || x 18 || x 19 || x 21)) || (x 9 && (x 13 || x 17 || x 18 || x 20)) || (x 10 && (x 16 || x 17 || x 19 || x 25)) || (x 11 && (x 15 || x 16 || x 18 || x 24)) || (x 12 && (x 14 || x 15 || x 17 || x 23))) := by
  simp [baseline, Circuit.eval, Circuit.wires, GateOp.eval, List.ofFn_succ]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma baseline_correct (x : Fin 26 → Bool) :
    baseline.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val, v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true := by
  rw [baseline_eval]
  simp [Fin.exists_iff, Prod.mk.injEq, or_and_right, exists_or, and_assoc, and_or_left, or_assoc]

end PEqualNP.Outside.L_meta_650
