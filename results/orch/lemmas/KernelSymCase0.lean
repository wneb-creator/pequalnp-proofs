import OwnRows
namespace PEqualNP.Outside.L_meta_10760_first
def gate_s0 : Gt := (false, 0, 1)
def prior_s0 : List Gt := [(false, 0, 2), (false, 3, 5), (false, 0, 5), (false, 0, 6), (false, 5, 6), (true, 1, 2), (true, 3, 4), (false, 1, 4)]
def rows_s0 : List ((Nat × Nat) × List Nat) := ownRows acc_extraFive [120, 116, 60, 108, 92, 32784, 16400, 16388, 112, 76, 40960, 24576, 12288, 18432, 6144, 32800, 32776, 32772, 16448, 16392, 8256, 8224, 8200, 4112, 4100, 2080, 2056, 100, 88, 56, 52, 44, 4192, 2128, 32768, 16384, 104, 84, 28, 8196, 4160, 4128, 2112, 2064, 72, 68, 12, 8192, 4096, 2048, 96, 80, 48, 40, 36, 24, 20, 64, 32, 16, 8, 4]
def owns_s0 : List Nat := rows_s0.map (fun r => r.1.1)
def codes_s0 : List Nat := [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma owned_s0_checked : ownCheck topC gate_s0 acc_extraFive [] rows_s0 = true := by decide +kernel
lemma owned_s0_bounds : ∀ x ∈ acc_extraFive, x.1 ∈ owns_s0 → Imp [gate_s0] x.1 x.2 := by
  have h := ownCheck_imp topC_ok (e := gate_s0) (by decide) accBounds_extraFive own0 owned_s0_checked
  simpa only [owns_s0, List.append_nil] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma shape_s0_checked : okTy prior_s0 acc_extraFive 12 prior_s0.length gate_s0 owns_s0 codes_s0 (121, ((0x80c000000080 <<< 64) + 0x8200020000000400)) [List.range 13] = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma search_s0_checked : [List.range 13].all (okTs acc_extraFive 12 gate_s0 owns_s0 codes_s0 (121, ((0x80c000000080 <<< 64) + 0x8200020000000400))) = true := by decide +kernel
lemma case_s0_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior_s0, Imp [f] 0 13) : Imp [gate_s0] 0 13 :=
  ty_imp accBounds_extraFive owned_s0_bounds shape_s0_checked search_s0_checked (by decide) h0 (by simpa using hF)
end PEqualNP.Outside.L_meta_10760_first
