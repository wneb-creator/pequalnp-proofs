import OwnRows
namespace PEqualNP.Outside.L_meta_10760_first
def gate_s16 : Gt := (true, 1, 3)
def prior_s16 : List Gt := [(false, 0, 2), (false, 3, 5), (false, 0, 5), (false, 0, 6), (false, 5, 6), (true, 1, 2), (true, 3, 4), (false, 1, 4), (false, 0, 1), (false, 4, 5), (false, 0, 3), (false, 2, 5), (false, 1, 2), (false, 3, 4), (false, 1, 6), (false, 4, 6), (false, 2, 3), (false, 0, 4), (false, 1, 5), (false, 1, 3), (false, 2, 4), (false, 2, 6), (false, 3, 6), (true, 0, 1), (true, 4, 5), (true, 0, 3), (true, 2, 5), (true, 1, 6), (true, 4, 6), (true, 2, 3), (true, 0, 2), (true, 3, 5), (true, 0, 4), (true, 1, 5), (true, 0, 5), (true, 0, 6), (true, 5, 6)]
def rows_s16 : List ((Nat × Nat) × List Nat) := ownRows acc_extraFive [116, 113, 117, 101, 53, 32784, 112, 32800, 32772, 32769, 8256, 8224, 2080, 576, 544, 528, 516, 100, 97, 52, 49, 37, 8197, 32768, 512, 21, 8196, 8193, 68, 8192, 96, 48, 36, 33, 20, 17, 5, 64, 32, 16, 4, 1]
def owns_s16 : List Nat := rows_s16.map (fun r => r.1.1)
def codes_s16 : List Nat := [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma owned_s16_checked : ownCheck topC gate_s16 acc_extraFive [] rows_s16 = true := by decide +kernel
lemma owned_s16_bounds : ∀ x ∈ acc_extraFive, x.1 ∈ owns_s16 → Imp [gate_s16] x.1 x.2 := by
  have h := ownCheck_imp topC_ok (e := gate_s16) (by decide) accBounds_extraFive own0 owned_s16_checked
  simpa only [owns_s16, List.append_nil] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma shape_s16_checked : okTy prior_s16 acc_extraFive 12 prior_s16.length gate_s16 owns_s16 codes_s16 (159, ((((0x40308a80 <<< 64) + 0x600aa45033080008) <<< 64) + 0x0500040022c20001)) [List.range 13] = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma search_s16_checked : [List.range 13].all (okTs acc_extraFive 12 gate_s16 owns_s16 codes_s16 (159, ((((0x40308a80 <<< 64) + 0x600aa45033080008) <<< 64) + 0x0500040022c20001))) = true := by decide +kernel
lemma case_s16_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior_s16, Imp [f] 0 13) : Imp [gate_s16] 0 13 :=
  ty_imp accBounds_extraFive owned_s16_bounds shape_s16_checked search_s16_checked (by decide) h0 (by simpa using hF)
end PEqualNP.Outside.L_meta_10760_first
