import Seed8SymBase
namespace PEqualNP.Outside.L_meta_982_aux.Finite
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem seed8_pair_check_4 :
    (seed8PairPerms.getD 4 []).length = 218 ∧
    ∀ j : Fin 218, seed8PairRow 4 j < 218 ∧
      seed8PairRow (seed8InversePerms.getD 4 0) j < 218 ∧
      seed8PairRow 4 (seed8PairRow (seed8InversePerms.getD 4 0) j) = j := by
  decide +kernel


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem seed8_pool_check_4 :
    seed8Forbidden.Subset (seed8Forbidden.map (seed8SymWord 4)) := by
  have hc : seed8Forbidden.all
      (fun a => (seed8Forbidden.map (seed8SymWord 4)).contains a) = true := by
    decide +kernel
  intro a ha
  simpa using (List.all_eq_true.1 hc a ha)


end PEqualNP.Outside.L_meta_982_aux.Finite
