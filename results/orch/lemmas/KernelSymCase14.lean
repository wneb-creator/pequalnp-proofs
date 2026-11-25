import OwnRows
namespace PEqualNP.Outside.L_meta_10760_first
def gate_s14 : Gt := (true, 0, 5)
def prior_s14 : List Gt := [(false, 0, 2), (false, 3, 5), (false, 0, 5), (false, 0, 6), (false, 5, 6), (true, 1, 2), (true, 3, 4), (false, 1, 4), (false, 0, 1), (false, 4, 5), (false, 0, 3), (false, 2, 5), (false, 1, 2), (false, 3, 4), (false, 1, 6), (false, 4, 6), (false, 2, 3), (false, 0, 4), (false, 1, 5), (false, 1, 3), (false, 2, 4), (false, 2, 6), (false, 3, 6), (true, 0, 1), (true, 4, 5), (true, 0, 3), (true, 2, 5), (true, 1, 6), (true, 4, 6), (true, 2, 3), (true, 0, 2), (true, 3, 5), (true, 0, 4), (true, 1, 5)]
def rows_s14 : List ((Nat × Nat) × List Nat) := ownRows acc_extraFive [94, 92, 90, 86, 78, 76, 8256, 8200, 4112, 4100, 2056, 2050, 1088, 1028, 88, 82, 70, 8198, 4162, 2128, 1048, 84, 74, 26, 22, 8196, 8194, 4160, 4098, 2112, 2064, 1040, 1032, 72, 68, 8192, 4096, 2048, 1024, 80, 66, 24, 20, 18, 10, 6, 64, 16, 2]
def owns_s14 : List Nat := rows_s14.map (fun r => r.1.1)
def codes_s14 : List Nat := [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma owned_s14_checked : ownCheck topC gate_s14 acc_extraFive [] rows_s14 = true := by decide +kernel
lemma owned_s14_bounds : ∀ x ∈ acc_extraFive, x.1 ∈ owns_s14 → Imp [gate_s14] x.1 x.2 := by
  have h := ownCheck_imp topC_ok (e := gate_s14) (by decide) accBounds_extraFive own0 owned_s14_checked
  simpa only [owns_s14, List.append_nil] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma shape_s14_checked : okTy prior_s14 acc_extraFive 12 prior_s14.length gate_s14 owns_s14 codes_s14 (215, ((((((0x604030 <<< 64) + 0x0000c00a04200190) <<< 64) + 0x0409004000200a88) <<< 64) + 0x4001084148080004)) [List.range 13] = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma search_s14_checked : [List.range 13].all (okTs acc_extraFive 12 gate_s14 owns_s14 codes_s14 (215, ((((((0x604030 <<< 64) + 0x0000c00a04200190) <<< 64) + 0x0409004000200a88) <<< 64) + 0x4001084148080004))) = true := by decide +kernel
lemma case_s14_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior_s14, Imp [f] 0 13) : Imp [gate_s14] 0 13 :=
  ty_imp accBounds_extraFive owned_s14_bounds shape_s14_checked search_s14_checked (by decide) h0 (by simpa using hF)
end PEqualNP.Outside.L_meta_10760_first
