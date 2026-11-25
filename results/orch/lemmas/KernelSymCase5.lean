import OwnRows
namespace PEqualNP.Outside.L_meta_10760_first
def gate_s5 : Gt := (false, 0, 4)
def prior_s5 : List Gt := [(false, 0, 2), (false, 3, 5), (false, 0, 5), (false, 0, 6), (false, 5, 6), (true, 1, 2), (true, 3, 4), (false, 1, 4), (false, 0, 1), (false, 4, 5), (false, 0, 3), (false, 2, 5), (false, 1, 2), (false, 3, 4), (false, 1, 6), (false, 4, 6), (false, 2, 3)]
def rows_s5 : List ((Nat × Nat) × List Nat) := ownRows acc_extraFive [108, 78, 46, 32770, 16388, 76, 18432, 6144, 33792, 3072, 32800, 32776, 32772, 16448, 16392, 16386, 2080, 2056, 2050, 1088, 1028, 44, 1064, 32768, 16384, 104, 74, 42, 14, 2112, 1056, 1032, 72, 68, 12, 2048, 1024, 40, 34, 10, 64, 32, 8, 4, 2]
def owns_s5 : List Nat := rows_s5.map (fun r => r.1.1)
def codes_s5 : List Nat := [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma owned_s5_checked : ownCheck topC gate_s5 acc_extraFive [] rows_s5 = true := by decide +kernel
lemma owned_s5_bounds : ∀ x ∈ acc_extraFive, x.1 ∈ owns_s5 → Imp [gate_s5] x.1 x.2 := by
  have h := ownCheck_imp topC_ok (e := gate_s5) (by decide) accBounds_extraFive own0 owned_s5_checked
  simpa only [owns_s5, List.append_nil] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma shape_s5_checked : okTy prior_s5 acc_extraFive 12 prior_s5.length gate_s5 owns_s5 codes_s5 (139, ((((0x188 <<< 64) + 0x00c0000000058400) <<< 64) + 0x5020021000400001)) [List.range 13] = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma search_s5_checked : [List.range 13].all (okTs acc_extraFive 12 gate_s5 owns_s5 codes_s5 (139, ((((0x188 <<< 64) + 0x00c0000000058400) <<< 64) + 0x5020021000400001))) = true := by decide +kernel
lemma case_s5_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior_s5, Imp [f] 0 13) : Imp [gate_s5] 0 13 :=
  ty_imp accBounds_extraFive owned_s5_bounds shape_s5_checked search_s5_checked (by decide) h0 (by simpa using hF)
end PEqualNP.Outside.L_meta_10760_first
