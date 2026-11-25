import OwnRows
namespace PEqualNP.Outside.L_meta_10760_first
def gate_s17 : Gt := (true, 1, 4)
def prior_s17 : List Gt := [(false, 0, 2), (false, 3, 5), (false, 0, 5), (false, 0, 6), (false, 5, 6), (true, 1, 2), (true, 3, 4), (false, 1, 4), (false, 0, 1), (false, 4, 5), (false, 0, 3), (false, 2, 5), (false, 1, 2), (false, 3, 4), (false, 1, 6), (false, 4, 6), (false, 2, 3), (false, 0, 4), (false, 1, 5), (false, 1, 3), (false, 2, 4), (false, 2, 6), (false, 3, 6), (true, 0, 1), (true, 4, 5), (true, 0, 3), (true, 2, 5), (true, 1, 6), (true, 4, 6), (true, 2, 3), (true, 0, 2), (true, 3, 5), (true, 0, 4), (true, 1, 5), (true, 0, 5), (true, 0, 6), (true, 5, 6), (true, 1, 3), (true, 2, 4)]
def rows_s17 : List ((Nat × Nat) × List Nat) := ownRows acc_extraFive [45, 109, 108, 105, 101, 77, 16388, 520, 76, 32800, 32776, 32772, 32769, 16448, 16392, 16385, 4100, 4097, 2080, 2056, 576, 544, 516, 100, 97, 73, 44, 41, 37, 13, 4192, 2113, 32768, 16384, 512, 104, 69, 4160, 4128, 2112, 2049, 72, 68, 12, 4096, 2048, 96, 65, 40, 36, 33, 9, 5, 64, 32, 8, 4, 1]
def owns_s17 : List Nat := rows_s17.map (fun r => r.1.1)
def codes_s17 : List Nat := [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma owned_s17_checked : ownCheck topC gate_s17 acc_extraFive [] rows_s17 = true := by decide +kernel
lemma owned_s17_bounds : ∀ x ∈ acc_extraFive, x.1 ∈ owns_s17 → Imp [gate_s17] x.1 x.2 := by
  have h := ownCheck_imp topC_ok (e := gate_s17) (by decide) accBounds_extraFive own0 owned_s17_checked
  simpa only [owns_s17, List.append_nil] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma shape_s17_checked : okTy prior_s17 acc_extraFive 12 prior_s17.length gate_s17 owns_s17 codes_s17 (229, ((((((0x140a002010 <<< 64) + 0x0040104101169400) <<< 64) + 0x2c42001044082000) <<< 64) + 0x004000080000a4d0)) [List.range 13] = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma search_s17_checked : [List.range 13].all (okTs acc_extraFive 12 gate_s17 owns_s17 codes_s17 (229, ((((((0x140a002010 <<< 64) + 0x0040104101169400) <<< 64) + 0x2c42001044082000) <<< 64) + 0x004000080000a4d0))) = true := by decide +kernel
lemma case_s17_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior_s17, Imp [f] 0 13) : Imp [gate_s17] 0 13 :=
  ty_imp accBounds_extraFive owned_s17_bounds shape_s17_checked search_s17_checked (by decide) h0 (by simpa using hF)
end PEqualNP.Outside.L_meta_10760_first
