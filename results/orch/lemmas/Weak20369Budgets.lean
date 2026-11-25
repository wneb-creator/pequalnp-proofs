import Weak20369Supports
import Weak20369Cofactors
import Mono18Rectangle9611
import EntryTableAdapters

namespace PEqualNP.Outside.L_meta_2373.Weak20369
open Live1024 CountVector

lemma rectangle_values : ∀ i : Fin 12, childWs9611 i = Mono18Rectangle9611.childSignals9611 i := by
  decide +kernel
lemma rectangle_lengths : ∀ i : Fin 12, childCap9611 i + 1 = (Mono18Rectangle9611.childSignals9611 i).length := by
  decide +kernel

lemma childRuns9611 (i : Fin 12) (k : Nat) (cap : k ≤ childCap9611 i) :
    ¬ Run false (observe graph) k ((childWs9611 i).map observe) := by
  have length := rectangle_lengths i
  rw [rectangle_values i]
  exact Mono18Rectangle9611.child_cut9611 i (by omega)

lemma childBudget9611 (i : Fin 12) : BudgetRunCut
    (duplicateRoots Finset.univ (support9611 i))
    (duplicateRaw (fun r => signal9611 (tag9611 r)) (entryValue9611 i)) false graph 0 := by
  exact budgetRunCut_of_list _ _ (childLabels9611 i) (childWs9611 i)
    (childLabels_nodup9611 i) (childLabels_basis9611 i) (childLabels_values9611 i)
    false graph 0 (childCap9611 i) (childLabels_size9611 i) (childRuns9611 i)

lemma childRuns20369 (i : Fin 11) (notMemo : i ≠ 6) (k : Nat) (cap : k ≤ childCap20369 i) :
    ¬ Run false (observe graph) k ((childWs20369 i).map observe) := by
  fin_cases i
  · exact terminalRun20370 cap
  · exact terminalRun20371 cap
  · exact terminalRun20372 cap
  · exact terminalRun20373 cap
  · exact terminalRun20374 cap
  · exact terminalRun20375 cap
  · exact False.elim (notMemo rfl)
  · exact terminalRun20377 cap
  · exact terminalRun20378 cap
  · exact terminalRun20379 cap
  · exact terminalRun20380 cap

lemma childBudget20369 (i : Fin 11) (notMemo : i ≠ 6) : BudgetRunCut
    (duplicateRoots Finset.univ (support20369 i))
    (duplicateRaw (fun r => signal20369 (tag20369 r)) (entryValue20369 i)) false graph 1 := by
  exact budgetRunCut_of_list _ _ (childLabels20369 i) (childWs20369 i)
    (childLabels_nodup20369 i) (childLabels_basis20369 i) (childLabels_values20369 i)
    false graph 1 (childCap20369 i) (childLabels_size20369 i) (childRuns20369 i notMemo)

def gateWs : Fin 5 → List Sig := ![gateWs0, gateWs1, gateWs2, gateWs3, gateWs4]
lemma gateLabels_values : ∀ i : Fin 5,
    (gateLabels i).map (duplicateRaw (fun r => signal9611 (tag9611 r)) (gateValue i)) = gateWs i := by
  decide +kernel

lemma gateBudget (i : Fin 5) : BudgetRunCut (compressRoots Finset.univ (gateSupport i))
    (duplicateRaw (fun r => signal9611 (tag9611 r)) (gateValue i)) false graph 1 := by
  apply budgetRunCut_of_list _ _ (gateLabels i) (gateWs i) (gateLabels_nodup i) (gateLabels_basis i)
    (gateLabels_values i) false graph 1 (gateCap i) (gateLabels_size i)
  fin_cases i
  · intro k cap; exact gateRun0 cap
  · intro k cap; exact gateRun1 cap
  · intro k cap; exact gateRun2 cap
  · intro k cap; exact gateRun3 cap
  · intro k cap; exact gateRun4 cap

end PEqualNP.Outside.L_meta_2373.Weak20369
