import Seed0SymBase
namespace PEqualNP.Outside.L_meta_982_aux.Finite
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem seed0_pair_check_6 :
    (seed0PairPerms.getD 6 []).length = 151 ∧
    ∀ j : Fin 151, seed0PairRow 6 j < 151 ∧
      seed0PairRow (seed0InversePerms.getD 6 0) j < 151 ∧
      seed0PairRow 6 (seed0PairRow (seed0InversePerms.getD 6 0) j) = j := by
  decide +kernel


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem seed0_pool_check_6 :
    seed0Forbidden.Subset (seed0Forbidden.map (seed0SymWord 6)) := by
  have hc : seed0Forbidden.all
      (fun a => (seed0Forbidden.map (seed0SymWord 6)).contains a) = true := by
    decide +kernel
  intro a ha
  simpa using (List.all_eq_true.1 hc a ha)


end PEqualNP.Outside.L_meta_982_aux.Finite
