import RootShardAdapter
import KernelFirst13
namespace PEqualNP.Outside.L_meta_10760_first
def optQ14 : List (Nat × Nat) := pick acc_extraFive [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12, 8198, 8197, 8195, 4192, 4162, 4130, 2128, 2113, 2065, 1072, 1064, 1048, 32768, 16384, 512, 104, 84, 74, 69, 50, 42, 28, 26, 22, 21, 19, 14]
def finalGates : List Gt := [(false, 0, 2), (false, 3, 5), (false, 0, 5), (false, 0, 6), (false, 5, 6), (true, 1, 2), (true, 3, 4), (false, 1, 4), (false, 0, 1), (false, 4, 5), (false, 0, 3), (false, 2, 5), (false, 1, 2), (false, 3, 4), (false, 1, 6), (false, 4, 6), (false, 2, 3), (false, 0, 4), (false, 1, 5), (false, 1, 3), (false, 2, 4), (false, 2, 6), (false, 3, 6), (true, 0, 1), (true, 4, 5), (true, 0, 3), (true, 2, 5), (true, 1, 6), (true, 4, 6), (true, 2, 3), (true, 0, 2), (true, 3, 5), (true, 0, 4), (true, 1, 5), (true, 0, 5), (true, 0, 6), (true, 5, 6), (true, 1, 3), (true, 2, 4), (true, 1, 4), (true, 2, 6), (true, 3, 6)]
def optM14 : List (Nat × Nat) := [(0, 1), (FF, 0)]
lemma optQ14_bounds : ∀ e ∈ optQ14, Imp [] e.1 e.2 := pickI accBounds_extraFive
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma optQ14_shape : pOk 0 optQ14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma finalGates_shape : fbOk [] finalGates (1, 1) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma optM14_shape : mFull optM14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def optUnary14 : chkT topC [] optQ14 (1, 1) 0 13 [1] 0 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def optBinary14 : chkT topC [] optQ14 (1, 1) 0 13 [1] FF 0 = false := by decide +kernel
lemma optReject14 (hmin : Imp [] 0 13) (hF : ∀ e ∈ finalGates, Imp [e] 0 13) :
    ∀ S : Finset Nat, (S : Set Nat) ⊆ C (mz 0) (WZ [] 0) →
      ¬ Live Z0 (mz 0) (tz 0) 13 1 S := by
  apply reject_one_shards optQ14_bounds optQ14_shape finalGates_shape hF hmin optM14_shape
  intro p hp
  simp only [optM14, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact optUnary14
  · exact optBinary14
lemma live_excluded (hF : ∀ e ∈ finalGates, Imp [e] 0 13) :
    ∀ S : Finset Nat, (S : Set Nat) ⊆ C (mz 0) (WZ [] 0) →
      ¬ Live Z0 (mz 0) (tz 0) 13 1 S := optReject14 bound13 hF
end PEqualNP.Outside.L_meta_10760_first
