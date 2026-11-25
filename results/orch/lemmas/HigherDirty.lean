import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2585_aux.HigherDirty

open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [6, 5]⟩,
    ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.or, [8, 2]⟩,
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [10, 2]⟩,
    ⟨GateOp.or, [0, 4]⟩,
    ⟨GateOp.or, [12, 2]⟩,
    ⟨GateOp.or, [0, 4]⟩,
    ⟨GateOp.or, [14, 5]⟩,
    ⟨GateOp.or, [3, 1]⟩,
    ⟨GateOp.or, [16, 2]⟩,
    ⟨GateOp.or, [3, 1]⟩,
    ⟨GateOp.or, [18, 5]⟩,
    ⟨GateOp.and, [7, 9]⟩,
    ⟨GateOp.and, [20, 11]⟩,
    ⟨GateOp.and, [21, 13]⟩,
    ⟨GateOp.and, [22, 15]⟩,
    ⟨GateOp.and, [23, 17]⟩,
    ⟨GateOp.and, [24, 19]⟩,
    ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.or, [26, 5]⟩,
    ⟨GateOp.and, [25, 27]⟩], 28⟩

def H : Circuit := ⟨C.gates, 25⟩

lemma valid : PEqualNP.TopForm.IsAO2 6 C := by decide

lemma computes_matching : ∀ z : Fin 6 → Bool,
    PEqualNP.MetaComplexity.circuitFun 6 C z =
      ((z 0 && z 3) || (z 1 && z 4) || (z 2 && z 5)) := by decide

lemma all_interior_not_below : ∀ w : Fin 28,
    ¬ PEqualNP.CircuitMoves.WireBelowOutput 6 C w.val := by decide

lemma dirty_pair_shadow_exact : ∀ u v : Fin 6,
    PEqualNP.MetaComplexity.circuitFun 6 H (fun i => decide (i = u ∨ i = v)) =
      PEqualNP.MetaComplexity.circuitFun 6 C (fun i => decide (i = u ∨ i = v)) := by decide

lemma dirty_on_independent_triple :
    PEqualNP.MetaComplexity.circuitFun 6 H (fun i => decide (i.val < 3)) = true ∧
    PEqualNP.MetaComplexity.circuitFun 6 C (fun i => decide (i.val < 3)) = false := by decide

lemma every_gate_on_edge : ∀ j : Fin 23, ∃ p : Fin 3,
    PEqualNP.MetaComplexity.circuitFun 6 ⟨C.gates, 6 + j.val⟩
      (fun i => decide (i.val = p.val ∨ i.val = 3 + p.val)) = true := by decide

lemma ands_false_on_singletons : ∀ j ∈ ([14, 15, 16, 17, 18, 19, 22] : List ℕ),
    ∀ p : Fin 6, PEqualNP.MetaComplexity.circuitFun 6 ⟨C.gates, 6 + j⟩
      (fun i => decide (i = p)) = false := by decide

end PEqualNP.Outside.L_meta_2585_aux.HigherDirty
