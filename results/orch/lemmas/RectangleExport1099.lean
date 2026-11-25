import RectangleOrEdgeRun
import RectanglePackedCheck
import CountVectorTransport

namespace PEqualNP.Outside.L_meta_2373.RectangleExport1099

open Live1024
open RectangleOrEdgeRun

def extra : Sig := bin 1 (inputs.getD 6 zero)
  (bin 1 (inputs.getD 1 zero) (inputs.getD 2 zero))

def signal (i : Fin 12) : Sig := Fin.lastCases extra basis i

def natWeight (r c : Nat) : Int :=
  RectangleOrEdge.weight (Fin.ofNat 15 r) (Fin.ofNat 15 c)

def positiveSupport : List Nat := [0, 1, 2, 6, 7, 12, 13]
def negativeSupport : List Nat := [8, 10]

lemma positive_support : ∀ r : Fin 15,
    observe extra (positiveRows r) = true → r.val ∈ positiveSupport := by
  decide +kernel

lemma negative_support : ∀ c : Fin 15,
    observe extra (negativeRows c) = false → c.val ∈ negativeSupport := by
  decide +kernel

lemma checked_cost : RectanglePackedCheck.check natWeight positiveSupport negativeSupport 4 = true := by
  decide +kernel

lemma weight_eq : ∀ r c : Fin 15,
    natWeight r.val c.val = RectangleOrEdge.weight r c := by
  decide +kernel

lemma extra_bound : RectangleRun.Bounds positiveRows negativeRows
    RectangleOrEdge.weight (observe extra) 4 := by
  have bound := RectanglePackedCheck.bounds_of_check positiveRows negativeRows
    natWeight positiveSupport negativeSupport (observe extra) 4
    (by decide) (by decide) checked_cost positive_support negative_support
  simpa only [weight_eq] using bound

lemma signal_bound (i : Fin 12) : RectangleRun.Bounds positiveRows negativeRows
    RectangleOrEdge.weight (observe (signal i)) 4 := by
  refine Fin.lastCases ?_ ?_ i
  · change RectangleRun.Bounds positiveRows negativeRows
      RectangleOrEdge.weight (observe extra) 4
    exact extra_bound
  · intro j
    simpa [signal] using prefix_bound j

def tag : Fin 17 → Fin 12 := ![0, 0, 0, 1, 2, 3, 3, 3, 4, 5, 6, 7, 8, 9, 10, 11, 11]
def indexedRaw (i : Fin 17) : Sig := signal (tag i)
def counts : Fin 12 → Nat := ![3, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 2]

def sourceIds : Fin 12 → Nat := ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 1514]

lemma exported_bank : (List.finRange 17).map (fun i => sourceIds (tag i)) =
    [1, 1, 1, 2, 3, 4, 4, 4, 5, 6, 7, 8, 9, 10, 12, 1514, 1514] := by
  decide +kernel

lemma tag_counts : ∀ j : Fin 12,
    CountVector.count tag (Finset.univ : Finset (Fin 17)) j = counts j := by
  decide +kernel

lemma budget_cut : BudgetRunCut (Finset.univ : Finset (Fin 17)) indexedRaw false graph 0 := by
  intro k cap trace
  have lower := RectangleRun.run_length_le trace
  have length : ((Finset.univ : Finset (Fin 17)).toList.map
      (fun i => observe (indexedRaw i))).length = 17 := by simp
  rw [length] at lower
  have upper : k + 1 ≤ 17 := by simpa using cap
  have tight : ((Finset.univ : Finset (Fin 17)).toList.map
      (fun i => observe (indexedRaw i))).length = k + 1 := by omega
  have bound := RectangleRun.tight_run_uniform positiveRows negativeRows RectangleOrEdge.weight
    trace tight (cap := 4)
    (fun v hv => by
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
      exact signal_bound (tag i)) positive_graph negative_graph
  change RectangleOrEdge.rect Finset.univ Finset.univ ≤ _ at bound
  rw [RectangleOrEdge.full_weight, length] at bound
  norm_num at bound

lemma budget_cut_of_counts {α : Type} [DecidableEq α] (roots : Finset α)
    (classes : α → Fin 12)
    (same : ∀ j, CountVector.count classes roots j = counts j) :
    BudgetRunCut roots (fun r => signal (classes r)) false graph 0 := by
  exact CountVector.budgetRunCut_transport tag classes signal Finset.univ roots
    (fun j => (tag_counts j).trans (same j).symm) false graph 0 budget_cut

lemma extra_export : extra = 0xfffffffffffffffffcfcfcfcfcfcfcfcfffffffffffffffffcfcfcfcfcfcfcfcfffffffffffffffffcfcfcfcfcfcfcfcfffffffffffffffffcfcfcfcfcfcfcfcfffffffffffffffffcfcfcfcfcfcfcfcfffffffffffffffffcfcfcfcfcfcfcfcfffffffffffffffffcfcfcfcfcfcfcfcfffffffffffffffffcfcfcfcfcfcfcfc := by decide +kernel

end PEqualNP.Outside.L_meta_2373.RectangleExport1099
