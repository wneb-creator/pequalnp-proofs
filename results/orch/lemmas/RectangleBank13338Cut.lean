import PrunedInterface
import RectangleBank13338

namespace PEqualNP.Outside.L_meta_2373.RectangleBank13338

open Live1024

def indexedRaw (i : Fin 18) : Sig := raw (labels.getD i.val 0)

lemma budget_cut : BudgetRunCut (Finset.univ : Finset (Fin 18)) indexedRaw false graph 0 := by
  intro k cap trace
  have perm : (Finset.univ : Finset (Fin 18)).toList.Perm (List.finRange 18) := by
    apply List.perm_of_nodup_nodup_toFinset_eq (Finset.nodup_toList _) (List.nodup_finRange _)
    ext i
    simp
  have ordered := Run.perm (perm.map (fun i => observe (indexedRaw i))) trace
  have same : (List.finRange 18).map (fun i => observe (indexedRaw i)) =
      labels.map (fun i => observe (raw i)) := by rfl
  rw [same] at ordered
  have lower := RectangleRun.run_length_le ordered
  have length : (labels.map (fun i => observe (raw i))).length = 18 := by rfl
  rw [length] at lower
  have upper : k + 1 ≤ 18 := by simpa using cap
  have exactBudget : k = 17 := by omega
  subst k
  exact bank_exclusion ordered

end PEqualNP.Outside.L_meta_2373.RectangleBank13338
