import PEqualNP.Outside.L_meta_2448

namespace PEqualNP.Outside.L_meta_2448_aux.twoJunkExample

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma circuit_not_star : ¬ HasStarProfile 6 G C := by decide

def starC : Circuit := ⟨[
  ⟨GateOp.or, [4, 5]⟩,
  ⟨GateOp.and, [0, 6]⟩,
  ⟨GateOp.or, [2, 3]⟩,
  ⟨GateOp.and, [1, 8]⟩,
  ⟨GateOp.or, [7, 9]⟩], 10⟩

lemma starC_monotone : Monotone2 starC := by simp [Monotone2, starC]

lemma starC_reads_back : ReadsBack 6 starC := by decide

lemma starC_star : HasStarProfile 6 G starC := by decide

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
lemma starC_computes : ∀ x : Fin 6 → Bool, circuitFun 6 starC x = graphFun G ∅ x := by decide

lemma starC_smaller : starC.size < C.size := by decide

lemma circuit_not_minimal : ¬ IsMinimalMonoCircuit 6 C := by
  intro h
  have heq : circuitFun 6 starC = circuitFun 6 C := by
    funext x
    exact (starC_computes x).trans (circuit_computes x).symm
  have hle := h.2 starC starC_monotone heq
  exact (Nat.not_le_of_gt starC_smaller) hle

end PEqualNP.Outside.L_meta_2448_aux.twoJunkExample
