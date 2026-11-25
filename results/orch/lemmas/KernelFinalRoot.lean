import KernelFirst13
import SingleRootAdapter
namespace PEqualNP.Outside.L_meta_10760_first
def finalGates : List Gt := [(false, 0, 2), (false, 3, 5), (false, 0, 5), (false, 0, 6), (false, 5, 6), (true, 1, 2), (true, 3, 4), (false, 1, 4), (false, 0, 1), (false, 4, 5), (false, 0, 3), (false, 2, 5), (false, 1, 2), (false, 3, 4), (false, 1, 6), (false, 4, 6), (false, 2, 3), (false, 0, 4), (false, 1, 5), (false, 1, 3), (false, 2, 4), (false, 2, 6), (false, 3, 6), (true, 0, 1), (true, 4, 5), (true, 0, 3), (true, 2, 5), (true, 1, 6), (true, 4, 6), (true, 2, 3), (true, 0, 2), (true, 3, 5), (true, 0, 4), (true, 1, 5), (true, 0, 5), (true, 0, 6), (true, 5, 6), (true, 1, 3), (true, 2, 4), (true, 1, 4), (true, 2, 6), (true, 3, 6)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma final_shape : pOk 0 root13Q = true ∧ fbOk [] finalGates (1, 1) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma final_search : okLs root13Q 13 (1, 1) [1] = true := by decide +kernel
lemma live_excluded (hF : ∀ e ∈ finalGates, Imp [e] 0 13) :
    ∀ S : Finset Nat, (S : Set Nat) ⊆ C (mz 0) (WZ [] 0) →
      ¬ Live Z0 (mz 0) (tz 0) 13 1 S :=
  reject_one_cert root13Q_bounds final_shape.1 final_shape.2 hF bound13 final_search
end PEqualNP.Outside.L_meta_10760_first
