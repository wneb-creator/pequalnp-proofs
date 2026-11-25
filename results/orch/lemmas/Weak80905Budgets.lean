import Weak80905Supports
import Weak80905Cofactors
import EntryTableAdapters

namespace PEqualNP.Outside.L_meta_2373.Weak80905
open Live1024 CountVector

lemma childRuns76616 (i : Fin 11) (k : Nat) (cap : k ≤ 14) :
    ¬ Run false (observe graph) k ((childWs76616 i).map observe) := by
  fin_cases i
  · exact terminalRun76617 cap
  · exact terminalRun76618 cap
  · exact terminalRun76619 cap
  · exact terminalRun76620 cap
  · exact terminalRun76621 cap
  · exact terminalRun76622 cap
  · exact terminalRun76623 cap
  · exact terminalRun76624 cap
  · exact terminalRun76625 cap
  · exact terminalRun76626 cap
  · exact terminalRun76627 cap

lemma childBudget76616 (i : Fin 11) :
    BudgetRunCut (duplicateRoots Finset.univ (support76616 i))
      (duplicateRaw (fun r => signal (tag76616 r)) (signal i)) false graph 1 := by
  exact budgetRunCut_of_list _ _ (childLabels76616 i) (childWs76616 i)
    (childLabels_nodup76616 i) (childLabels_basis76616 i) (childLabels_values76616 i)
    false graph 1 14 (childLabels_size76616 i) (childRuns76616 i)

lemma childRuns80905 (i : Fin 11) (notMemo : i ≠ 7) (k : Nat) (cap : k ≤ 14) :
    ¬ Run false (observe graph) k ((childWs80905 i).map observe) := by
  fin_cases i
  · exact terminalRun80906 cap
  · exact terminalRun80907 cap
  · exact terminalRun80908 cap
  · exact terminalRun80909 cap
  · exact terminalRun80910 cap
  · exact terminalRun80911 cap
  · exact terminalRun80912 cap
  · exact False.elim (notMemo rfl)
  · exact terminalRun80914 cap
  · exact terminalRun80915 cap
  · exact terminalRun80916 cap

lemma childBudget80905 (i : Fin 11) (notMemo : i ≠ 7) :
    BudgetRunCut (duplicateRoots Finset.univ (support80905 i))
      (duplicateRaw (fun r => signal (tag80905 r)) (signal i)) false graph 2 := by
  exact budgetRunCut_of_list _ _ (childLabels80905 i) (childWs80905 i)
    (childLabels_nodup80905 i) (childLabels_basis80905 i) (childLabels_values80905 i)
    false graph 2 14 (childLabels_size80905 i) (childRuns80905 i notMemo)

def gateWs : Fin 2 → List Sig := ![gateWs0, gateWs1]

lemma gateLabels_values : ∀ i : Fin 2,
    gateLabels.map (duplicateRaw (fun r => signal (tag76616 r)) (gateValue i)) = gateWs i := by
  decide +kernel

lemma gateBudget (i : Fin 2) : BudgetRunCut (compressRoots Finset.univ gateSupport)
    (duplicateRaw (fun r => signal (tag76616 r)) (gateValue i)) false graph 2 := by
  apply budgetRunCut_of_list _ _ gateLabels (gateWs i) gateLabels_nodup gateLabels_basis
    (gateLabels_values i) false graph 2 13 gateLabels_size
  fin_cases i
  · intro k cap; exact gateRun0 cap
  · intro k cap; exact gateRun1 cap

end PEqualNP.Outside.L_meta_2373.Weak80905
