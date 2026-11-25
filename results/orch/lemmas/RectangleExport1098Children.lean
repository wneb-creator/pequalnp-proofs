import RectangleExport1099
import RectangleRunIndexed

namespace PEqualNP.Outside.L_meta_2373.RectangleExport1098Children

open Live1024 RectangleOrEdgeRun

def extra : Sig := bin 1 (inputs.getD 0 zero) (inputs.getD 3 zero)
def signal (i : Fin 13) : Sig := Fin.lastCases extra RectangleExport1099.signal i
def caps (i : Fin 13) : Int := Fin.lastCases 8 (fun _ => 4) i

def positiveSupport : List Nat := [0, 2, 3, 4, 5, 8]
def negativeSupport : List Nat := [0, 3, 6, 7, 9, 11, 13]

lemma positive_support : ∀ r : Fin 15,
    observe extra (positiveRows r) = true → r.val ∈ positiveSupport := by
  decide +kernel

lemma negative_support : ∀ c : Fin 15,
    observe extra (negativeRows c) = false → c.val ∈ negativeSupport := by
  decide +kernel

lemma checked_cost : RectanglePackedCheck.check RectangleExport1099.natWeight
    positiveSupport negativeSupport 8 = true := by decide +kernel

lemma extra_bound : RectangleRun.Bounds positiveRows negativeRows
    RectangleOrEdge.weight (observe extra) 8 := by
  have bound := RectanglePackedCheck.bounds_of_check positiveRows negativeRows
    RectangleExport1099.natWeight positiveSupport negativeSupport (observe extra) 8
    (by decide) (by decide) checked_cost positive_support negative_support
  simpa only [RectangleExport1099.weight_eq] using bound

lemma signal_bound (i : Fin 13) : RectangleRun.Bounds positiveRows negativeRows
    RectangleOrEdge.weight (observe (signal i)) (caps i) := by
  refine Fin.lastCases ?_ ?_ i
  · change RectangleRun.Bounds positiveRows negativeRows RectangleOrEdge.weight (observe extra) 8
    exact extra_bound
  · intro j
    simpa [signal, caps] using RectangleExport1099.signal_bound j

def labels : Fin 13 → List (Fin 13) := ![
  [0, 0, 0, 1, 2, 3, 3, 3, 4, 5, 6, 7, 8, 9, 10, 11, 11],
  [0, 0, 1, 1, 2, 3, 3, 3, 4, 5, 6, 7, 8, 9, 10, 11, 11],
  [0, 0, 1, 2, 2, 3, 3, 3, 4, 5, 6, 7, 8, 9, 10, 11, 11],
  [0, 0, 1, 2, 3, 3, 3, 3, 4, 5, 6, 7, 8, 9, 10, 11, 11],
  [0, 0, 1, 2, 3, 3, 3, 4, 4, 5, 6, 7, 8, 9, 10, 11, 11],
  [0, 0, 1, 2, 3, 3, 3, 4, 5, 5, 6, 7, 8, 9, 10, 11, 11],
  [0, 0, 1, 2, 3, 3, 3, 4, 5, 6, 6, 7, 8, 9, 10, 11, 11],
  [0, 0, 1, 2, 3, 3, 3, 4, 5, 6, 7, 7, 8, 9, 10, 11, 11],
  [0, 0, 1, 2, 3, 3, 3, 4, 5, 6, 7, 8, 8, 9, 10, 11, 11],
  [0, 0, 1, 2, 3, 3, 3, 4, 5, 6, 7, 8, 9, 9, 10, 11, 11],
  [0, 0, 1, 2, 3, 3, 3, 4, 5, 6, 7, 8, 9, 10, 10, 11, 11],
  [0, 0, 1, 2, 3, 3, 3, 4, 5, 6, 7, 8, 9, 10, 11, 11, 11],
  [0, 1, 2, 3, 3, 4, 5, 6, 7, 8, 9, 10, 12, 12, 11, 11]
]

def childSignals (i : Fin 13) : List Sig := (labels i).map signal

lemma total_bound : ∀ i : Fin 13, ((labels i).map caps).sum ≤ 72 := by
  decide +kernel

lemma run_exclusion (i : Fin 13) (k : Nat) (cap : k + 1 ≤ (labels i).length)
    (trace : Run false (observe graph) k ((labels i).map (fun j => observe (signal j)))) : False := by
  have lower := RectangleRun.run_length_le trace
  simp only [List.length_map] at lower
  have tight : (labels i).length = k + 1 := by omega
  have bounds := RectangleRun.tight_run_indexed positiveRows negativeRows RectangleOrEdge.weight
    (fun j => observe (signal j)) caps (labels i) trace tight (fun j _ => signal_bound j)
  have bound := bounds Finset.univ Finset.univ
    (fun r _ => positive_graph r) (fun c _ => negative_graph c)
  change RectangleOrEdge.rect Finset.univ Finset.univ ≤ ((labels i).map caps).sum at bound
  rw [RectangleOrEdge.full_weight] at bound
  have cost := total_bound i
  omega

lemma child_cut (i : Fin 13) {k : Nat} (cap : k + 1 ≤ (childSignals i).length)
    (trace : Run false (observe graph) k ((childSignals i).map observe)) : False := by
  apply run_exclusion i k (by simpa only [childSignals, List.length_map] using cap)
  simpa only [childSignals, List.map_map, Function.comp_def] using trace

lemma extra_export : extra = 0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa := by decide +kernel

end PEqualNP.Outside.L_meta_2373.RectangleExport1098Children
