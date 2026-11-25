import OwnRows
namespace PEqualNP.Outside.L_meta_10760_first
def gate_s2 : Gt := (false, 1, 2)
def prior_s2 : List Gt := [(false, 0, 2), (false, 3, 5), (false, 0, 5), (false, 0, 6), (false, 5, 6), (true, 1, 2), (true, 3, 4), (false, 1, 4), (false, 0, 1), (false, 4, 5), (false, 0, 3), (false, 2, 5)]
def rows_s2 : List ((Nat × Nat) × List Nat) := ownRows acc_extraFive [120, 113, 89, 57, 105, 32784, 16400, 520, 112, 40960, 24576, 12288, 4608, 32800, 32776, 32769, 16448, 16392, 16385, 8256, 8224, 8200, 4112, 4097, 576, 544, 528, 97, 88, 81, 73, 56, 49, 41, 25, 4192, 32768, 16384, 512, 104, 8193, 4160, 4128, 72, 8192, 4096, 96, 80, 65, 48, 40, 33, 24, 17, 9, 64, 32, 16, 8, 1]
def owns_s2 : List Nat := rows_s2.map (fun r => r.1.1)
def codes_s2 : List Nat := [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma owned_s2_checked : ownCheck topC gate_s2 acc_extraFive [] rows_s2 = true := by decide +kernel
lemma owned_s2_bounds : ∀ x ∈ acc_extraFive, x.1 ∈ owns_s2 → Imp [gate_s2] x.1 x.2 := by
  have h := ownCheck_imp topC_ok (e := gate_s2) (by decide) accBounds_extraFive own0 owned_s2_checked
  simpa only [owns_s2, List.append_nil] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma shape_s2_checked : okTy prior_s2 acc_extraFive 12 prior_s2.length gate_s2 owns_s2 codes_s2 (78, ((0x2c41 <<< 64) + 0x0400000141000094)) [List.range 13] = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma search_s2_checked : [List.range 13].all (okTs acc_extraFive 12 gate_s2 owns_s2 codes_s2 (78, ((0x2c41 <<< 64) + 0x0400000141000094))) = true := by decide +kernel
lemma case_s2_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior_s2, Imp [f] 0 13) : Imp [gate_s2] 0 13 :=
  ty_imp accBounds_extraFive owned_s2_bounds shape_s2_checked search_s2_checked (by decide) h0 (by simpa using hF)
end PEqualNP.Outside.L_meta_10760_first
