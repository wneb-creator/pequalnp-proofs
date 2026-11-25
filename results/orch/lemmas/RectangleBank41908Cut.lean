import PrunedInterface
import RectangleBank41908

namespace PEqualNP.Outside.L_meta_2373.RectangleBank41908

open Live1024

def indexedRaw (i : Fin 20) : Sig := raw (labels.getD i.val 0)

lemma budget_cut : BudgetRunCut (Finset.univ : Finset (Fin 20)) indexedRaw false graph 0 := by
  intro k cap trace
  have perm : (Finset.univ : Finset (Fin 20)).toList.Perm (List.finRange 20) := by
    apply List.perm_of_nodup_nodup_toFinset_eq (Finset.nodup_toList _) (List.nodup_finRange _)
    ext i
    simp
  have ordered := Run.perm (perm.map (fun i => observe (indexedRaw i))) trace
  have same : (List.finRange 20).map (fun i => observe (indexedRaw i)) =
      labels.map (fun i => observe (raw i)) := by rfl
  rw [same] at ordered
  have lower := RectangleRun.run_length_le ordered
  have length : (labels.map (fun i => observe (raw i))).length = 20 := by rfl
  rw [length] at lower
  have upper : k + 1 ≤ 20 := by simpa using cap
  have exactBudget : k = 19 := by omega
  subst k
  exact bank_exclusion ordered

end PEqualNP.Outside.L_meta_2373.RectangleBank41908
