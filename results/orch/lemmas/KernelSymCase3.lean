import OwnRows
namespace PEqualNP.Outside.L_meta_10760_first
def gate_s3 : Gt := (false, 1, 6)
def prior_s3 : List Gt := [(false, 0, 2), (false, 3, 5), (false, 0, 5), (false, 0, 6), (false, 5, 6), (true, 1, 2), (true, 3, 4), (false, 1, 4), (false, 0, 1), (false, 4, 5), (false, 0, 3), (false, 2, 5), (false, 1, 2), (false, 3, 4)]
def rows_s3 : List ((Nat × Nat) × List Nat) := ownRows acc_extraFive [60, 57, 45, 53, 29, 16400, 16388, 520, 24576, 12288, 18432, 6144, 4608, 16392, 16385, 8224, 8200, 4112, 4100, 4097, 2080, 2056, 544, 528, 516, 56, 52, 49, 44, 41, 37, 25, 13, 8197, 2065, 16384, 512, 28, 21, 8196, 8193, 4128, 2064, 2049, 12, 8192, 4096, 2048, 48, 40, 36, 33, 24, 20, 17, 9, 5, 32, 16, 8, 4, 1]
def owns_s3 : List Nat := rows_s3.map (fun r => r.1.1)
def codes_s3 : List Nat := [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma owned_s3_checked : ownCheck topC gate_s3 acc_extraFive [] rows_s3 = true := by decide +kernel
lemma owned_s3_bounds : ∀ x ∈ acc_extraFive, x.1 ∈ owns_s3 → Imp [gate_s3] x.1 x.2 := by
  have h := ownCheck_imp topC_ok (e := gate_s3) (by decide) accBounds_extraFive own0 owned_s3_checked
  simpa only [owns_s3, List.append_nil] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma shape_s3_checked : okTy prior_s3 acc_extraFive 12 prior_s3.length gate_s3 owns_s3 codes_s3 (114, ((0xb1010001000 <<< 64) + 0x0010002001201112)) [List.range 13] = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma search_s3_checked : [List.range 13].all (okTs acc_extraFive 12 gate_s3 owns_s3 codes_s3 (114, ((0xb1010001000 <<< 64) + 0x0010002001201112))) = true := by decide +kernel
lemma case_s3_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior_s3, Imp [f] 0 13) : Imp [gate_s3] 0 13 :=
  ty_imp accBounds_extraFive owned_s3_bounds shape_s3_checked search_s3_checked (by decide) h0 (by simpa using hF)
end PEqualNP.Outside.L_meta_10760_first
