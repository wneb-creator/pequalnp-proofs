import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_650.Augmented17
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- This partial circuit includes four extra edges beyond the six-row target.
def candidate : Circuit :=
  ⟨[
    ⟨GateOp.or, [0, 2]⟩,
    ⟨GateOp.or, [9, 11]⟩,
    ⟨GateOp.or, [6, 18]⟩,
    ⟨GateOp.or, [7, 19]⟩,
    ⟨GateOp.or, [13, 20]⟩,
    ⟨GateOp.or, [10, 15]⟩,
    ⟨GateOp.or, [15, 16]⟩,
    ⟨GateOp.and, [17, 21]⟩,
    ⟨GateOp.or, [6, 12]⟩,
    ⟨GateOp.or, [16, 25]⟩,
    ⟨GateOp.or, [8, 26]⟩,
    ⟨GateOp.and, [1, 27]⟩,
    ⟨GateOp.or, [14, 22]⟩,
    ⟨GateOp.and, [2, 23]⟩,
    ⟨GateOp.or, [6, 29]⟩,
    ⟨GateOp.and, [3, 31]⟩,
    ⟨GateOp.or, [18, 12]⟩,
    ⟨GateOp.or, [8, 11]⟩,
    ⟨GateOp.or, [14, 33]⟩,
    ⟨GateOp.and, [4, 35]⟩,
    ⟨GateOp.or, [30, 36]⟩,
    ⟨GateOp.or, [10, 13]⟩,
    ⟨GateOp.or, [34, 38]⟩,
    ⟨GateOp.and, [5, 39]⟩,
    ⟨GateOp.or, [24, 28]⟩,
    ⟨GateOp.or, [32, 41]⟩,
    ⟨GateOp.or, [37, 42]⟩,
    ⟨GateOp.or, [40, 43]⟩
  ], 44⟩

def targetEdges : List (ℕ × ℕ) :=
  [(0, 6), (0, 7), (0, 9), (0, 13), (1, 6), (1, 8), (1, 12), (1, 16), (2, 7), (2, 11), (2, 15), (2, 16), (3, 6), (3, 10), (3, 14), (3, 15), (4, 9), (4, 11), (4, 12), (4, 14), (5, 8), (5, 10), (5, 11), (5, 13)]

def extraEdges : List (ℕ × ℕ) :=
  [(0, 11), (2, 6), (2, 9), (2, 13)]

def augmentedEdges : List (ℕ × ℕ) := targetEdges ++ extraEdges

theorem candidate_size : candidate.size = 28 := rfl

theorem candidate_monotone : Monotone2 candidate := by
  simp [candidate, Monotone2]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem candidate_eval (x : Fin 17 → Bool) :
    candidate.eval (List.ofFn x) =
    ((x 5 && ((x 8 || x 11) || (x 10 || x 13))) || (((x 2 && (x 15 || x 16)) || (x 4 && (x 14 || ((x 9 || x 11) || x 12)))) || ((x 3 && (x 6 || (x 14 || (x 10 || x 15)))) || (((x 0 || x 2) && (x 13 || (x 7 || (x 6 || (x 9 || x 11))))) || (x 1 && (x 8 || (x 16 || (x 6 || x 12)))))))) := by
  simp [candidate, Circuit.eval, Circuit.wires, GateOp.eval, List.ofFn_succ]

def edgeExpr (x : Fin 17 → Bool) : Bool :=
  (x 0 && x 6) || (x 0 && x 7) || (x 0 && x 9) || (x 0 && x 13) || (x 1 && x 6) || (x 1 && x 8) || (x 1 && x 12) || (x 1 && x 16) || (x 2 && x 7) || (x 2 && x 11) || (x 2 && x 15) || (x 2 && x 16) || (x 3 && x 6) || (x 3 && x 10) || (x 3 && x 14) || (x 3 && x 15) || (x 4 && x 9) || (x 4 && x 11) || (x 4 && x 12) || (x 4 && x 14) || (x 5 && x 8) || (x 5 && x 10) || (x 5 && x 11) || (x 5 && x 13) || (x 0 && x 11) || (x 2 && x 6) || (x 2 && x 9) || (x 2 && x 13)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem candidate_normal (x : Fin 17 → Bool) :
    candidate.eval (List.ofFn x) = edgeExpr x := by
  rw [candidate_eval]
  simp only [edgeExpr, Bool.and_or_distrib_left, Bool.and_or_distrib_right]
  ac_rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem candidate_correct (x : Fin 17 → Bool) :
    candidate.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 17, (u.val, v.val) ∈ augmentedEdges ∧ x u = true ∧ x v = true := by
  rw [candidate_normal]
  simp [edgeExpr, augmentedEdges, targetEdges, extraEdges, Fin.exists_iff, Prod.mk.injEq,
    or_and_right, exists_or, and_assoc, and_or_left, or_assoc]

theorem exists_augmented :
    ∃ C : Circuit, Monotone2 C ∧ C.size = 28 ∧
      ∀ x : Fin 17 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u v : Fin 17, (u.val, v.val) ∈ augmentedEdges ∧ x u = true ∧ x v = true := by
  exact ⟨candidate, candidate_monotone, candidate_size, candidate_correct⟩

end PEqualNP.Outside.L_meta_650.Augmented17
