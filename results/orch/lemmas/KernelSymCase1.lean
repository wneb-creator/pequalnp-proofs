import OwnRows
namespace PEqualNP.Outside.L_meta_10760_first
def gate_s1 : Gt := (false, 0, 3)
def prior_s1 : List Gt := [(false, 0, 2), (false, 3, 5), (false, 0, 5), (false, 0, 6), (false, 5, 6), (true, 1, 2), (true, 3, 4), (false, 1, 4), (false, 0, 1), (false, 4, 5)]
def rows_s1 : List ((Nat × Nat) × List Nat) := ownRows acc_extraFive [116, 114, 102, 86, 54, 32784, 32770, 16400, 16388, 112, 40960, 24576, 18432, 33792, 3072, 32800, 32772, 16448, 16386, 8256, 8224, 2080, 2050, 1088, 1028, 100, 98, 82, 70, 52, 38, 8198, 2128, 1072, 32768, 16384, 84, 50, 22, 8196, 8194, 2112, 2064, 1056, 1040, 68, 8192, 2048, 1024, 96, 80, 66, 48, 36, 34, 20, 18, 6, 64, 32, 16, 4, 2]
def owns_s1 : List Nat := rows_s1.map (fun r => r.1.1)
def codes_s1 : List Nat := [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma owned_s1_checked : ownCheck topC gate_s1 acc_extraFive [] rows_s1 = true := by decide +kernel
lemma owned_s1_bounds : ∀ x ∈ acc_extraFive, x.1 ∈ owns_s1 → Imp [gate_s1] x.1 x.2 := by
  have h := ownCheck_imp topC_ok (e := gate_s1) (by decide) accBounds_extraFive own0 owned_s1_checked
  simpa only [owns_s1, List.append_nil] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma shape_s1_checked : okTy prior_s1 acc_extraFive 12 prior_s1.length gate_s1 owns_s1 codes_s1 (125, ((0x1000000100082000 <<< 64) + 0x0000200000401004)) [List.range 13] = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma search_s1_checked : [List.range 13].all (okTs acc_extraFive 12 gate_s1 owns_s1 codes_s1 (125, ((0x1000000100082000 <<< 64) + 0x0000200000401004))) = true := by decide +kernel
lemma case_s1_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior_s1, Imp [f] 0 13) : Imp [gate_s1] 0 13 :=
  ty_imp accBounds_extraFive owned_s1_bounds shape_s1_checked search_s1_checked (by decide) h0 (by simpa using hF)
end PEqualNP.Outside.L_meta_10760_first
