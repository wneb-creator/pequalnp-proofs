import OwnRows
namespace PEqualNP.Outside.L_meta_10760_first
def gate_s7 : Gt := (false, 2, 6)
def prior_s7 : List Gt := [(false, 0, 2), (false, 3, 5), (false, 0, 5), (false, 0, 6), (false, 5, 6), (true, 1, 2), (true, 3, 4), (false, 1, 4), (false, 0, 1), (false, 4, 5), (false, 0, 3), (false, 2, 5), (false, 1, 2), (false, 3, 4), (false, 1, 6), (false, 4, 6), (false, 2, 3), (false, 0, 4), (false, 1, 5), (false, 1, 3), (false, 2, 4)]
def rows_s7 : List ((Nat × Nat) × List Nat) := ownRows acc_extraFive [51, 43, 27, 16400, 520, 514, 24576, 12288, 4608, 1536, 16392, 16386, 16385, 8224, 8200, 4112, 4097, 544, 528, 35, 11, 8195, 4130, 16384, 512, 50, 42, 26, 19, 8194, 8193, 4128, 4098, 8192, 4096, 40, 34, 24, 18, 10, 3, 32, 16, 8, 2]
def owns_s7 : List Nat := rows_s7.map (fun r => r.1.1)
def codes_s7 : List Nat := [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma owned_s7_checked : ownCheck topC gate_s7 acc_extraFive [] rows_s7 = true := by decide +kernel
lemma owned_s7_bounds : ∀ x ∈ acc_extraFive, x.1 ∈ owns_s7 → Imp [gate_s7] x.1 x.2 := by
  have h := ownCheck_imp topC_ok (e := gate_s7) (by decide) accBounds_extraFive own0 owned_s7_checked
  simpa only [owns_s7, List.append_nil] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma shape_s7_checked : okTy prior_s7 acc_extraFive 12 prior_s7.length gate_s7 owns_s7 codes_s7 (206, ((((((0x400 <<< 64) + 0x4200000004000101) <<< 64) + 0x2000000000008306) <<< 64) + 0x2400040001081800)) [List.range 13] = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma search_s7_checked : [List.range 13].all (okTs acc_extraFive 12 gate_s7 owns_s7 codes_s7 (206, ((((((0x400 <<< 64) + 0x4200000004000101) <<< 64) + 0x2000000000008306) <<< 64) + 0x2400040001081800))) = true := by decide +kernel
lemma case_s7_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior_s7, Imp [f] 0 13) : Imp [gate_s7] 0 13 :=
  ty_imp accBounds_extraFive owned_s7_bounds shape_s7_checked search_s7_checked (by decide) h0 (by simpa using hF)
end PEqualNP.Outside.L_meta_10760_first
