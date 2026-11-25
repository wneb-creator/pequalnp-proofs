import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_650.FullPairAugment
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- This partial computes the posted edges together with six additional edges.
def candidate : Circuit :=
  ⟨[
    ⟨GateOp.or, [13, 14]⟩,
    ⟨GateOp.or, [15, 20]⟩,
    ⟨GateOp.or, [21, 24]⟩,
    ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [26, 27]⟩,
    ⟨GateOp.or, [28, 30]⟩,
    ⟨GateOp.or, [25, 31]⟩,
    ⟨GateOp.and, [29, 32]⟩,
    ⟨GateOp.or, [13, 19]⟩,
    ⟨GateOp.or, [23, 34]⟩,
    ⟨GateOp.or, [24, 35]⟩,
    ⟨GateOp.and, [3, 36]⟩,
    ⟨GateOp.or, [18, 22]⟩,
    ⟨GateOp.or, [23, 38]⟩,
    ⟨GateOp.or, [25, 39]⟩,
    ⟨GateOp.and, [4, 40]⟩,
    ⟨GateOp.or, [17, 28]⟩,
    ⟨GateOp.or, [22, 42]⟩,
    ⟨GateOp.and, [5, 43]⟩,
    ⟨GateOp.or, [16, 20]⟩,
    ⟨GateOp.or, [21, 45]⟩,
    ⟨GateOp.or, [23, 46]⟩,
    ⟨GateOp.and, [6, 47]⟩,
    ⟨GateOp.or, [19, 27]⟩,
    ⟨GateOp.or, [22, 49]⟩,
    ⟨GateOp.and, [7, 50]⟩,
    ⟨GateOp.or, [14, 18]⟩,
    ⟨GateOp.or, [19, 52]⟩,
    ⟨GateOp.or, [21, 53]⟩,
    ⟨GateOp.and, [8, 54]⟩,
    ⟨GateOp.or, [13, 17]⟩,
    ⟨GateOp.or, [18, 56]⟩,
    ⟨GateOp.or, [20, 57]⟩,
    ⟨GateOp.and, [9, 58]⟩,
    ⟨GateOp.or, [16, 17]⟩,
    ⟨GateOp.or, [19, 60]⟩,
    ⟨GateOp.or, [25, 61]⟩,
    ⟨GateOp.and, [10, 62]⟩,
    ⟨GateOp.or, [15, 16]⟩,
    ⟨GateOp.or, [18, 64]⟩,
    ⟨GateOp.or, [24, 65]⟩,
    ⟨GateOp.and, [11, 66]⟩,
    ⟨GateOp.or, [14, 15]⟩,
    ⟨GateOp.or, [17, 68]⟩,
    ⟨GateOp.or, [23, 69]⟩,
    ⟨GateOp.and, [12, 70]⟩,
    ⟨GateOp.or, [33, 37]⟩,
    ⟨GateOp.or, [41, 72]⟩,
    ⟨GateOp.or, [44, 73]⟩,
    ⟨GateOp.or, [48, 74]⟩,
    ⟨GateOp.or, [51, 75]⟩,
    ⟨GateOp.or, [55, 76]⟩,
    ⟨GateOp.or, [59, 77]⟩,
    ⟨GateOp.or, [63, 78]⟩,
    ⟨GateOp.or, [67, 79]⟩,
    ⟨GateOp.or, [71, 80]⟩,
    ⟨GateOp.or, [16, 26]⟩,
    ⟨GateOp.or, [22, 82]⟩,
    ⟨GateOp.and, [0, 83]⟩,
    ⟨GateOp.or, [81, 84]⟩
  ], 85⟩

def targetEdges : List (ℕ × ℕ) := [(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)]
def extraEdges : List (ℕ × ℕ) := [(1, 14), (1, 20), (1, 24), (2, 13), (2, 15), (2, 21)]
def augmentedEdges : List (ℕ × ℕ) := targetEdges ++ extraEdges

theorem candidate_size : candidate.size = 60 := rfl

theorem candidate_monotone : Monotone2 candidate := by
  simp [candidate, Monotone2]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem candidate_eval (x : Fin 26 → Bool) :
    candidate.eval (List.ofFn x) = (((x 12 && (x 23 || (x 17 || (x 14 || x 15)))) || ((x 11 && (x 24 || (x 18 || (x 15 || x 16)))) || ((x 10 && (x 25 || (x 19 || (x 16 || x 17)))) || ((x 9 && (x 20 || (x 18 || (x 13 || x 17)))) || ((x 8 && (x 21 || (x 19 || (x 14 || x 18)))) || ((x 7 && (x 22 || (x 19 || (x 15 || x 20)))) || ((x 6 && (x 23 || (x 21 || (x 16 || x 20)))) || ((x 5 && (x 22 || (x 17 || (x 21 || x 24)))) || ((x 4 && (x 25 || (x 23 || (x 18 || x 22)))) || (((x 1 || x 2) && (x 25 || ((x 21 || x 24) || ((x 13 || x 14) || (x 15 || x 20))))) || (x 3 && (x 24 || (x 23 || (x 13 || x 19)))))))))))))) || (x 0 && (x 22 || (x 16 || (x 13 || x 14))))) := by
  simp [candidate, Circuit.eval, Circuit.wires, GateOp.eval, List.ofFn_succ]

def edgeExpr (x : Fin 26 → Bool) : Bool :=
  (x 0 && x 13) || (x 0 && x 14) || (x 0 && x 16) || (x 0 && x 22) || (x 1 && x 13) || (x 1 && x 15) || (x 1 && x 21) || (x 1 && x 25) || (x 2 && x 14) || (x 2 && x 20) || (x 2 && x 24) || (x 2 && x 25) || (x 3 && x 13) || (x 3 && x 19) || (x 3 && x 23) || (x 3 && x 24) || (x 4 && x 18) || (x 4 && x 22) || (x 4 && x 23) || (x 4 && x 25) || (x 5 && x 17) || (x 5 && x 21) || (x 5 && x 22) || (x 5 && x 24) || (x 6 && x 16) || (x 6 && x 20) || (x 6 && x 21) || (x 6 && x 23) || (x 7 && x 15) || (x 7 && x 19) || (x 7 && x 20) || (x 7 && x 22) || (x 8 && x 14) || (x 8 && x 18) || (x 8 && x 19) || (x 8 && x 21) || (x 9 && x 13) || (x 9 && x 17) || (x 9 && x 18) || (x 9 && x 20) || (x 10 && x 16) || (x 10 && x 17) || (x 10 && x 19) || (x 10 && x 25) || (x 11 && x 15) || (x 11 && x 16) || (x 11 && x 18) || (x 11 && x 24) || (x 12 && x 14) || (x 12 && x 15) || (x 12 && x 17) || (x 12 && x 23) || (x 1 && x 14) || (x 1 && x 20) || (x 1 && x 24) || (x 2 && x 13) || (x 2 && x 15) || (x 2 && x 21)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem candidate_normal (x : Fin 26 → Bool) :
    candidate.eval (List.ofFn x) = edgeExpr x := by
  rw [candidate_eval]
  simp only [edgeExpr, Bool.and_or_distrib_left, Bool.and_or_distrib_right]
  ac_rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem candidate_correct (x : Fin 26 → Bool) :
    candidate.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 26, (u.val, v.val) ∈ augmentedEdges ∧ x u = true ∧ x v = true := by
  rw [candidate_normal]
  simp [edgeExpr, augmentedEdges, targetEdges, extraEdges, Fin.exists_iff, Prod.mk.injEq,
    or_and_right, exists_or, and_assoc, and_or_left, or_assoc]

theorem exists_augmented :
    ∃ C : Circuit, Monotone2 C ∧ C.size = 60 ∧
      ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 26, (u.val, v.val) ∈ augmentedEdges ∧ x u = true ∧ x v = true := by
  exact ⟨candidate, candidate_monotone, candidate_size, candidate_correct⟩

end PEqualNP.Outside.L_meta_650.FullPairAugment
