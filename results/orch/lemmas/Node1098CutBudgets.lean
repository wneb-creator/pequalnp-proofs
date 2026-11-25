import Node1098Cofactors
import CountFixture1098Supports
import EntryTableAdapters

namespace PEqualNP.Outside.L_meta_2373.CountFixture1098

open Live1024

def cutLabels (i : Fin 13) : List (Sum (Fin 16) Bool) :=
  ![[Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12, Sum.inl 13, Sum.inl 14, Sum.inl 15, Sum.inr false], [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12, Sum.inl 14, Sum.inl 15, Sum.inr false], [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12, Sum.inl 14, Sum.inl 15, Sum.inr false], [Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12, Sum.inl 13, Sum.inl 15, Sum.inr false], [Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12, Sum.inl 13, Sum.inl 15, Sum.inr false], [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12, Sum.inl 13, Sum.inl 15, Sum.inr false], [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12, Sum.inl 13, Sum.inl 15, Sum.inr false], [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12, Sum.inl 15, Sum.inr false], [Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12, Sum.inl 15, Sum.inr false], [Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12, Sum.inl 14, Sum.inl 15, Sum.inr false], [Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12, Sum.inl 14, Sum.inl 15, Sum.inr false], [Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12, Sum.inl 13, Sum.inl 15, Sum.inr false], [Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 5, Sum.inl 6, Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10, Sum.inl 11, Sum.inl 12, Sum.inl 13, Sum.inl 15, Sum.inr false]] i

def cutWords (i : Fin 13) : List Sig := ![cutWs0, cutWs1, cutWs2, cutWs3, cutWs4, cutWs5, cutWs6, cutWs7, cutWs8, cutWs9, cutWs10, cutWs11, cutWs12] i

def cutCap (i : Fin 13) : Nat := ![15, 15, 15, 15, 15, 15, 15, 15, 15, 14, 14, 14, 14] i

lemma cutLabels_nodup : ∀ i : Fin 13, (cutLabels i).Nodup := by
  intro i
  fin_cases i <;> decide +kernel

lemma cutLabels_basis : ∀ i : Fin 13, (cutLabels i).toFinset =
    compressRoots (Finset.univ : Finset (Fin 16)) (cutSupport i) := by
  intro i
  fin_cases i <;> decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma cutLabels_values : ∀ i : Fin 13,
    (cutLabels i).map (duplicateRaw (fun r => signal (basisTag r)) (cutValue i)) = cutWords i := by
  intro i
  fin_cases i <;> decide +kernel

lemma cutLabels_size : ∀ i : Fin 13,
    (compressRoots (Finset.univ : Finset (Fin 16)) (cutSupport i)).card + 1 ≤ cutCap i + 1 := by
  intro i
  fin_cases i <;> decide +kernel

lemma cutRun (i : Fin 13) {k : Nat} (bound : k ≤ cutCap i) :
    ¬ Run false (observe graph) k ((cutWords i).map observe) := by
  fin_cases i
  · exact cutRun0 bound
  · exact cutRun1 bound
  · exact cutRun2 bound
  · exact cutRun3 bound
  · exact cutRun4 bound
  · exact cutRun5 bound
  · exact cutRun6 bound
  · exact cutRun7 bound
  · exact cutRun8 bound
  · exact cutRun9 bound
  · exact cutRun10 bound
  · exact cutRun11 bound
  · exact cutRun12 bound

lemma cutBudget (i : Fin 13) :
    BudgetRunCut (compressRoots (Finset.univ : Finset (Fin 16)) (cutSupport i))
      (duplicateRaw (fun r => signal (basisTag r)) (cutValue i)) false graph 1 :=
  budgetRunCut_of_list _ _ (cutLabels i) (cutWords i) (cutLabels_nodup i)
    (cutLabels_basis i) (cutLabels_values i) false graph 1 (cutCap i)
    (cutLabels_size i) (fun k bound => cutRun i bound)

end PEqualNP.Outside.L_meta_2373.CountFixture1098
