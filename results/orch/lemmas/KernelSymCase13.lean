import OwnRows
namespace PEqualNP.Outside.L_meta_10760_first
def gate_s13 : Gt := (true, 0, 4)
def prior_s13 : List Gt := [(false, 0, 2), (false, 3, 5), (false, 0, 5), (false, 0, 6), (false, 5, 6), (true, 1, 2), (true, 3, 4), (false, 1, 4), (false, 0, 1), (false, 4, 5), (false, 0, 3), (false, 2, 5), (false, 1, 2), (false, 3, 4), (false, 1, 6), (false, 4, 6), (false, 2, 3), (false, 0, 4), (false, 1, 5), (false, 1, 3), (false, 2, 4), (false, 2, 6), (false, 3, 6), (true, 0, 1), (true, 4, 5), (true, 0, 3), (true, 2, 5), (true, 1, 6), (true, 4, 6), (true, 2, 3), (true, 0, 2), (true, 3, 5)]
def rows_s13 : List ((Nat × Nat) × List Nat) := ownRows acc_extraFive [102, 110, 108, 78, 46, 32770, 16388, 76, 32800, 32776, 32772, 16448, 16392, 16386, 4100, 1088, 1028, 100, 70, 44, 38, 1064, 32768, 16384, 42, 14, 1056, 1032, 68, 12, 1024, 40, 36, 34, 10, 6, 32, 4, 2]
def owns_s13 : List Nat := rows_s13.map (fun r => r.1.1)
def codes_s13 : List Nat := [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma owned_s13_checked : ownCheck topC gate_s13 acc_extraFive [] rows_s13 = true := by decide +kernel
lemma owned_s13_bounds : ∀ x ∈ acc_extraFive, x.1 ∈ owns_s13 → Imp [gate_s13] x.1 x.2 := by
  have h := ownCheck_imp topC_ok (e := gate_s13) (by decide) accBounds_extraFive own0 owned_s13_checked
  simpa only [owns_s13, List.append_nil] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma shape_s13_checked : okTy prior_s13 acc_extraFive 12 prior_s13.length gate_s13 owns_s13 codes_s13 (201, ((((((0x4 <<< 64) + 0x002200000500c600) <<< 64) + 0x0801402000890801) <<< 64) + 0x1800054500080412)) [List.range 13] = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma search_s13_checked : [List.range 13].all (okTs acc_extraFive 12 gate_s13 owns_s13 codes_s13 (201, ((((((0x4 <<< 64) + 0x002200000500c600) <<< 64) + 0x0801402000890801) <<< 64) + 0x1800054500080412))) = true := by decide +kernel
lemma case_s13_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior_s13, Imp [f] 0 13) : Imp [gate_s13] 0 13 :=
  ty_imp accBounds_extraFive owned_s13_bounds shape_s13_checked search_s13_checked (by decide) h0 (by simpa using hF)
end PEqualNP.Outside.L_meta_10760_first
