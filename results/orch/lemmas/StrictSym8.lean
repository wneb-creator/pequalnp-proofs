import ShardCase
namespace PEqualNP.Outside.L_meta_10760_first
def gate_s8 : Gt := (true, 0, 1)
def prior_s8 : List Gt := [(false, 0, 2), (false, 3, 5), (false, 0, 5), (false, 0, 6), (false, 5, 6), (true, 1, 2), (true, 3, 4), (false, 1, 4), (false, 0, 1), (false, 4, 5), (false, 0, 3), (false, 2, 5), (false, 1, 2), (false, 3, 4), (false, 1, 6), (false, 4, 6), (false, 2, 3), (false, 0, 4), (false, 1, 5), (false, 1, 3), (false, 2, 4), (false, 2, 6), (false, 3, 6)]
def rows_s8 : List ((Nat × Nat) × List Nat) := ownRows acc_extraFive [120, 116, 60, 32784, 112, 32800, 32776, 32772, 4112, 4100, 2080, 2056, 56, 52, 4192, 2128, 32768, 4160, 4128, 2112, 2064, 4096, 2048, 48, 40, 24, 20, 32, 16]
def owns_s8 : List Nat := rows_s8.map (fun r => r.1.1)
def codes_s8 : List Nat := [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma owned_s8_checked : ownCheck topC gate_s8 acc_extraFive [] rows_s8 = true := by decide +kernel
lemma owned_s8_bounds : ∀ x ∈ acc_extraFive, x.1 ∈ owns_s8 → Imp [gate_s8] x.1 x.2 := by
  have h := ownCheck_imp topC_ok (e := gate_s8) (by decide) accBounds_extraFive own0 owned_s8_checked
  simpa only [owns_s8, List.append_nil] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma shape_s8_checked : okTy prior_s8 acc_extraFive 12 prior_s8.length gate_s8 owns_s8 codes_s8 (220, ((((((0x400400a <<< 64) + 0x6000402000404000) <<< 64) + 0x1823000000804209) <<< 64) + 0x0010002008000000)) [List.range 13] = true := by decide +kernel
def masks_sym8 : List (Nat × Nat) := [(0, 1), (((2 ^ 13 - 1) <<< 0), 0), (((2 ^ 13 - 1) <<< 13), 0), (((2 ^ 6 - 1) <<< 26), 0), (((2 ^ 7 - 1) <<< 32), 0), (((2 ^ 14 - 1) <<< 39), 0), (((2 ^ 27 - 1) <<< 53), 0), (((2 ^ 27 - 1) <<< 80), 0), (((2 ^ 13 - 1) <<< 107), 0), (((2 ^ 13 - 1) <<< 120), 0), (((2 ^ 13 - 1) <<< 133), 0), (((2 ^ 7 - 1) <<< 146), 0), (((2 ^ 7 - 1) <<< 153), 0), (((2 ^ 6 - 1) <<< 160), 0), (((2 ^ 7 - 1) <<< 166), 0), (((2 ^ 14 - 1) <<< 173), 0), (((2 ^ 27 - 1) <<< 187), 0)]
lemma masks_sym8_full : mFull masks_sym8 = true := by decide +kernel
noncomputable def run_sym8 (p : Nat × Nat) : Bool :=
  chkT topC [gate_s8] (tabE gate_s8 owns_s8 (pick acc_extraFive codes_s8)) (220, ((((((0x400400a <<< 64) + 0x6000402000404000) <<< 64) + 0x1823000000804209) <<< 64) + 0x0010002008000000)) 0 12 (List.range 13) p.1 p.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma split_sym8_0 : run_sym8 (0, 1) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma split_sym8_1 : run_sym8 (((2 ^ 13 - 1) <<< 0), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma split_sym8_2 : run_sym8 (((2 ^ 13 - 1) <<< 13), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma split_sym8_3 : run_sym8 (((2 ^ 6 - 1) <<< 26), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma split_sym8_4 : run_sym8 (((2 ^ 7 - 1) <<< 32), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma split_sym8_5 : run_sym8 (((2 ^ 14 - 1) <<< 39), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma split_sym8_6 : run_sym8 (((2 ^ 27 - 1) <<< 53), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma split_sym8_7 : run_sym8 (((2 ^ 27 - 1) <<< 80), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma split_sym8_8 : run_sym8 (((2 ^ 13 - 1) <<< 107), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma split_sym8_9 : run_sym8 (((2 ^ 13 - 1) <<< 120), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma split_sym8_10 : run_sym8 (((2 ^ 13 - 1) <<< 133), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma split_sym8_11 : run_sym8 (((2 ^ 7 - 1) <<< 146), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma split_sym8_12 : run_sym8 (((2 ^ 7 - 1) <<< 153), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma split_sym8_13 : run_sym8 (((2 ^ 6 - 1) <<< 160), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma split_sym8_14 : run_sym8 (((2 ^ 7 - 1) <<< 166), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma split_sym8_15 : run_sym8 (((2 ^ 14 - 1) <<< 173), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma split_sym8_16 : run_sym8 (((2 ^ 27 - 1) <<< 187), 0) = false := by decide +kernel
lemma case_s8_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior_s8, Imp [f] 0 13) : Imp [gate_s8] 0 13 := by
  have hc : ∀ p ∈ masks_sym8, run_sym8 p = false := by
    intro p hp
    simp only [masks_sym8, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact split_sym8_0
    · exact split_sym8_1
    · exact split_sym8_2
    · exact split_sym8_3
    · exact split_sym8_4
    · exact split_sym8_5
    · exact split_sym8_6
    · exact split_sym8_7
    · exact split_sym8_8
    · exact split_sym8_9
    · exact split_sym8_10
    · exact split_sym8_11
    · exact split_sym8_12
    · exact split_sym8_13
    · exact split_sym8_14
    · exact split_sym8_15
    · exact split_sym8_16
  exact ty_imp_shards accBounds_extraFive owned_s8_bounds shape_s8_checked masks_sym8_full hc h0 (by simpa using hF)
end PEqualNP.Outside.L_meta_10760_first
