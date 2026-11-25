import OwnRows
namespace PEqualNP.Outside.L_meta_10760_first
def gate_s6 : Gt := (false, 1, 3)
def prior_s6 : List Gt := [(false, 0, 2), (false, 3, 5), (false, 0, 5), (false, 0, 6), (false, 5, 6), (true, 1, 2), (true, 3, 4), (false, 1, 4), (false, 0, 1), (false, 4, 5), (false, 0, 3), (false, 2, 5), (false, 1, 2), (false, 3, 4), (false, 1, 6), (false, 4, 6), (false, 2, 3), (false, 0, 4), (false, 1, 5)]
def rows_s6 : List ((Nat × Nat) × List Nat) := ownRows acc_extraFive [101, 53, 32784, 16400, 16388, 40960, 24576, 18432, 32800, 32772, 32769, 16448, 16385, 8256, 8224, 37, 8197, 32768, 16384, 69, 21, 8196, 8193, 68, 8192, 20, 17, 5, 64, 16, 4, 1]
def owns_s6 : List Nat := rows_s6.map (fun r => r.1.1)
def codes_s6 : List Nat := [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma owned_s6_checked : ownCheck topC gate_s6 acc_extraFive [] rows_s6 = true := by decide +kernel
lemma owned_s6_bounds : ∀ x ∈ acc_extraFive, x.1 ∈ owns_s6 → Imp [gate_s6] x.1 x.2 := by
  have h := ownCheck_imp topC_ok (e := gate_s6) (by decide) accBounds_extraFive own0 owned_s6_checked
  simpa only [owns_s6, List.append_nil] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma shape_s6_checked : okTy prior_s6 acc_extraFive 12 prior_s6.length gate_s6 owns_s6 codes_s6 (108, ((0xc1040 <<< 64) + 0x00800044e4214b01)) [List.range 13] = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma search_s6_checked : [List.range 13].all (okTs acc_extraFive 12 gate_s6 owns_s6 codes_s6 (108, ((0xc1040 <<< 64) + 0x00800044e4214b01))) = true := by decide +kernel
lemma case_s6_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior_s6, Imp [f] 0 13) : Imp [gate_s6] 0 13 :=
  ty_imp accBounds_extraFive owned_s6_bounds shape_s6_checked search_s6_checked (by decide) h0 (by simpa using hF)
end PEqualNP.Outside.L_meta_10760_first
