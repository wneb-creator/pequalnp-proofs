import OwnRows
namespace PEqualNP.Outside.L_meta_10760_first
def gate_s15 : Gt := (true, 0, 6)
def prior_s15 : List Gt := [(false, 0, 2), (false, 3, 5), (false, 0, 5), (false, 0, 6), (false, 5, 6), (true, 1, 2), (true, 3, 4), (false, 1, 4), (false, 0, 1), (false, 4, 5), (false, 0, 3), (false, 2, 5), (false, 1, 2), (false, 3, 4), (false, 1, 6), (false, 4, 6), (false, 2, 3), (false, 0, 4), (false, 1, 5), (false, 1, 3), (false, 2, 4), (false, 2, 6), (false, 3, 6), (true, 0, 1), (true, 4, 5), (true, 0, 3), (true, 2, 5), (true, 1, 6), (true, 4, 6), (true, 2, 3), (true, 0, 2), (true, 3, 5), (true, 0, 4), (true, 1, 5), (true, 0, 5)]
def rows_s15 : List ((Nat × Nat) × List Nat) := ownRows acc_extraFive [60, 62, 54, 46, 8224, 8200, 4112, 4100, 1028, 52, 44, 38, 8198, 4130, 42, 22, 8196, 8194, 4128, 4098, 12, 8192, 4096, 40, 36, 34, 20, 6, 32, 4]
def owns_s15 : List Nat := rows_s15.map (fun r => r.1.1)
def codes_s15 : List Nat := [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma owned_s15_checked : ownCheck topC gate_s15 acc_extraFive [] rows_s15 = true := by decide +kernel
lemma owned_s15_bounds : ∀ x ∈ acc_extraFive, x.1 ∈ owns_s15 → Imp [gate_s15] x.1 x.2 := by
  have h := ownCheck_imp topC_ok (e := gate_s15) (by decide) accBounds_extraFive own0 owned_s15_checked
  simpa only [owns_s15, List.append_nil] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma shape_s15_checked : okTy prior_s15 acc_extraFive 12 prior_s15.length gate_s15 owns_s15 codes_s15 (181, ((((0x8081150200008 <<< 64) + 0x6110100250100020) <<< 64) + 0x800a850a84020360)) [List.range 13] = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma search_s15_checked : [List.range 13].all (okTs acc_extraFive 12 gate_s15 owns_s15 codes_s15 (181, ((((0x8081150200008 <<< 64) + 0x6110100250100020) <<< 64) + 0x800a850a84020360))) = true := by decide +kernel
lemma case_s15_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior_s15, Imp [f] 0 13) : Imp [gate_s15] 0 13 :=
  ty_imp accBounds_extraFive owned_s15_bounds shape_s15_checked search_s15_checked (by decide) h0 (by simpa using hF)
end PEqualNP.Outside.L_meta_10760_first
