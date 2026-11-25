import OwnRows
namespace PEqualNP.Outside.L_meta_10760_first
def gate_s4 : Gt := (false, 2, 3)
def prior_s4 : List Gt := [(false, 0, 2), (false, 3, 5), (false, 0, 5), (false, 0, 6), (false, 5, 6), (true, 1, 2), (true, 3, 4), (false, 1, 4), (false, 0, 1), (false, 4, 5), (false, 0, 3), (false, 2, 5), (false, 1, 2), (false, 3, 4), (false, 1, 6), (false, 4, 6)]
def rows_s4 : List ((Nat × Nat) × List Nat) := ownRows acc_extraFive [114, 113, 99, 83, 51, 32784, 32770, 16400, 514, 112, 67, 40960, 24576, 33792, 1536, 32800, 32769, 16448, 16386, 16385, 8256, 8224, 1088, 1025, 576, 544, 528, 98, 97, 82, 81, 49, 35, 8195, 1072, 32768, 16384, 512, 50, 19, 8194, 8193, 1056, 1040, 8192, 1024, 96, 80, 66, 65, 48, 34, 33, 18, 17, 3, 64, 32, 16, 2, 1]
def owns_s4 : List Nat := rows_s4.map (fun r => r.1.1)
def codes_s4 : List Nat := [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma owned_s4_checked : ownCheck topC gate_s4 acc_extraFive [] rows_s4 = true := by decide +kernel
lemma owned_s4_bounds : ∀ x ∈ acc_extraFive, x.1 ∈ owns_s4 → Imp [gate_s4] x.1 x.2 := by
  have h := ownCheck_imp topC_ok (e := gate_s4) (by decide) accBounds_extraFive own0 owned_s4_checked
  simpa only [owns_s4, List.append_nil] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma shape_s4_checked : okTy prior_s4 acc_extraFive 12 prior_s4.length gate_s4 owns_s4 codes_s4 (150, ((((0x100000 <<< 64) + 0x0000008220000000) <<< 64) + 0x4470c00009100004)) [List.range 13] = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma search_s4_checked : [List.range 13].all (okTs acc_extraFive 12 gate_s4 owns_s4 codes_s4 (150, ((((0x100000 <<< 64) + 0x0000008220000000) <<< 64) + 0x4470c00009100004))) = true := by decide +kernel
lemma case_s4_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior_s4, Imp [f] 0 13) : Imp [gate_s4] 0 13 :=
  ty_imp accBounds_extraFive owned_s4_bounds shape_s4_checked search_s4_checked (by decide) h0 (by simpa using hF)
end PEqualNP.Outside.L_meta_10760_first
