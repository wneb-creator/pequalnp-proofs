import CountFixture1098Supports
import RectangleExport1098Children
import EntryTableAdapters

namespace PEqualNP.Outside.L_meta_2373.CountFixture1098
open Live1024 CountVector

def childLabels : Fin 13 → List (Sum (Fin 16) Bool) := ![
  [Sum.inl 1, Sum.inr false, Sum.inr true, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12, Sum.inl 13, Sum.inl 14, Sum.inl 15],
  [Sum.inl 0, Sum.inl 1, Sum.inr false, Sum.inr true, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12, Sum.inl 13, Sum.inl 14, Sum.inl 15],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr false, Sum.inr true, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12, Sum.inl 13, Sum.inl 14, Sum.inl 15],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 5, Sum.inl 6, Sum.inr false, Sum.inr true, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12, Sum.inl 13, Sum.inl 14, Sum.inl 15],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inr false, Sum.inr true, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12, Sum.inl 13, Sum.inl 14, Sum.inl 15],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inr false, Sum.inr true, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12, Sum.inl 13, Sum.inl 14, Sum.inl 15],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inr false, Sum.inr true, Sum.inl 10, Sum.inl 11, Sum.inl 12, Sum.inl 13, Sum.inl 14, Sum.inl 15],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inr false, Sum.inr true, Sum.inl 11, Sum.inl 12, Sum.inl 13, Sum.inl 14, Sum.inl 15],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inr false, Sum.inr true, Sum.inl 12, Sum.inl 13, Sum.inl 14, Sum.inl 15],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inr false, Sum.inr true, Sum.inl 13, Sum.inl 14, Sum.inl 15],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12, Sum.inr false, Sum.inr true, Sum.inl 14, Sum.inl 15],
  [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12, Sum.inl 13, Sum.inl 15, Sum.inr false, Sum.inr true],
  [Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12, Sum.inl 13, Sum.inr false, Sum.inr true, Sum.inl 14, Sum.inl 15]
]

lemma childLabels_nodup : ∀ i : Fin 13, (childLabels i).Nodup := by
  decide +kernel

lemma childLabels_basis : ∀ i : Fin 13, (childLabels i).toFinset =
    duplicateRoots Finset.univ (entrySupport i) := by
  decide +kernel

lemma childLabels_values : ∀ i : Fin 13,
    (childLabels i).map (duplicateRaw (fun r => signal (basisTag r)) (entryValue i)) =
      RectangleExport1098Children.childSignals i := by
  intro i; fin_cases i <;> decide +kernel

lemma childLabels_size : ∀ i : Fin 13,
    (duplicateRoots Finset.univ (entrySupport i)).card ≤
      (RectangleExport1098Children.childSignals i).length := by
  decide +kernel

lemma childBudget (i : Fin 13) : BudgetRunCut
    (duplicateRoots Finset.univ (entrySupport i))
    (duplicateRaw (fun r => signal (basisTag r)) (entryValue i)) false graph 0 := by
  let ws := RectangleExport1098Children.childSignals i
  apply budgetRunCut_of_list _ _ (childLabels i) ws (childLabels_nodup i)
    (childLabels_basis i) (childLabels_values i) false graph 0 (ws.length - 1)
  · have size := childLabels_size i
    change (duplicateRoots Finset.univ (entrySupport i)).card ≤ ws.length at size
    have pos : 0 < ws.length := by fin_cases i <;> decide +kernel
    simp only [Nat.add_zero]
    omega
  · intro k cap run
    have pos : 0 < ws.length := by fin_cases i <;> decide +kernel
    exact RectangleExport1098Children.child_cut i (by change k + 1 ≤ ws.length; omega) run

end PEqualNP.Outside.L_meta_2373.CountFixture1098
