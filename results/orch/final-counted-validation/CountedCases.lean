namespace PEqualNP.Outside.L_meta_10760
def gate0 : Gt := (false, 0, 2)
def rows0 : List ((Nat × Nat) × List Nat) := ownRows acc_extraFive [90, 32784, 32770, 16400, 40960, 24576, 12288, 33792, 32800, 32776, 16448, 16392, 16386, 8256, 8224, 8200, 32768, 16384, 74, 26, 8194, 72, 8192, 24, 18, 10, 64, 16, 8, 2]
def owns0 : List Nat := rows0.map (fun r => r.1.1)
def codes0 : List Nat := [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def owned0_checked : ownCheck topC gate0 acc_extraFive [] rows0 = true := by decide +kernel
lemma owned0_bounds : ∀ x ∈ acc_extraFive, x.1 ∈ owns0 → Imp [gate0] x.1 x.2 := by
  have h := ownCheck_imp topC_ok (e := gate0) (by decide) accBounds_extraFive own0 owned0_checked
  simpa only [owns0, List.append_nil] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def shape0_checked : okTy [] acc_extraFive 12 0 gate0 owns0 codes0 (1, 0) [List.range 13] = true := by decide +kernel
def masks_base0 : List (Nat × Nat) := [(0, 1), ((2 ^ 3 - 1), 0), (((2 ^ 1 - 1) <<< 3), 0), (((2 ^ 1 - 1) <<< 4), 0), (((2 ^ 1 - 1) <<< 5), 0), (((2 ^ 7 - 1) <<< 6), 0), (((2 ^ 13 - 1) <<< 13), 0), (((2 ^ 27 - 1) <<< 26), 0), (((2 ^ 6 - 1) <<< 53), 0), (((2 ^ 3 - 1) <<< 59), 0), (((2 ^ 2 - 1) <<< 62), 0), (((2 ^ 1 - 1) <<< 64), 0), (((2 ^ 1 - 1) <<< 65), 0), (((2 ^ 14 - 1) <<< 66), 0), (((2 ^ 6 - 1) <<< 80), 0), (((2 ^ 3 - 1) <<< 86), 0), (((2 ^ 4 - 1) <<< 89), 0), (((2 ^ 14 - 1) <<< 93), 0), (((2 ^ 26 - 1) <<< 107), 0), (((2 ^ 13 - 1) <<< 133), 0), (((2 ^ 7 - 1) <<< 146), 0), (((2 ^ 7 - 1) <<< 153), 0), (((2 ^ 54 - 1) <<< 160), 0)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def masks_base0_full : mFull masks_base0 = true := by decide +kernel
noncomputable def run_base0 (p : Nat × Nat) : Bool :=
  chkT topC [gate0] (tabE gate0 owns0 (pick acc_extraFive codes0)) (1, 0) 0 12 [1] p.1 p.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base0_0 : run_base0 (0, 1) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base0_1 : run_base0 ((2 ^ 3 - 1), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base0_2 : run_base0 (((2 ^ 1 - 1) <<< 3), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base0_3 : run_base0 (((2 ^ 1 - 1) <<< 4), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base0_4 : run_base0 (((2 ^ 1 - 1) <<< 5), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base0_5 : run_base0 (((2 ^ 7 - 1) <<< 6), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base0_6 : run_base0 (((2 ^ 13 - 1) <<< 13), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base0_7 : run_base0 (((2 ^ 27 - 1) <<< 26), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base0_8 : run_base0 (((2 ^ 6 - 1) <<< 53), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base0_9 : run_base0 (((2 ^ 3 - 1) <<< 59), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base0_10 : run_base0 (((2 ^ 2 - 1) <<< 62), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base0_11 : run_base0 (((2 ^ 1 - 1) <<< 64), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base0_12 : run_base0 (((2 ^ 1 - 1) <<< 65), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base0_13 : run_base0 (((2 ^ 14 - 1) <<< 66), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base0_14 : run_base0 (((2 ^ 6 - 1) <<< 80), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base0_15 : run_base0 (((2 ^ 3 - 1) <<< 86), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base0_16 : run_base0 (((2 ^ 4 - 1) <<< 89), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base0_17 : run_base0 (((2 ^ 14 - 1) <<< 93), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base0_18 : run_base0 (((2 ^ 26 - 1) <<< 107), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base0_19 : run_base0 (((2 ^ 13 - 1) <<< 133), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base0_20 : run_base0 (((2 ^ 7 - 1) <<< 146), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base0_21 : run_base0 (((2 ^ 7 - 1) <<< 153), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base0_22 : run_base0 (((2 ^ 54 - 1) <<< 160), 0) = false := by decide +kernel
lemma case0_bound (h0 : Imp [] 0 13) : ImpT [gate0] 0 13 1 := by
  have hc : ∀ p ∈ masks_base0, run_base0 p = false := by
    intro p hp
    simp only [masks_base0, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact split_base0_0
    · exact split_base0_1
    · exact split_base0_2
    · exact split_base0_3
    · exact split_base0_4
    · exact split_base0_5
    · exact split_base0_6
    · exact split_base0_7
    · exact split_base0_8
    · exact split_base0_9
    · exact split_base0_10
    · exact split_base0_11
    · exact split_base0_12
    · exact split_base0_13
    · exact split_base0_14
    · exact split_base0_15
    · exact split_base0_16
    · exact split_base0_17
    · exact split_base0_18
    · exact split_base0_19
    · exact split_base0_20
    · exact split_base0_21
    · exact split_base0_22
  exact ty_imp_shards_t accBounds_extraFive owned0_bounds shape0_checked masks_base0_full hc h0 (by simp)
def gate1 : Gt := (false, 0, 5)
def prior1 : List Gt := [(false, 0, 2)]
def rows1 : List ((Nat × Nat) × List Nat) := ownRows acc_extraFive [92, 90, 86, 78, 32784, 32770, 76, 40960, 12288, 6144, 33792, 3072, 32776, 32772, 8256, 8200, 4112, 4100, 2056, 2050, 1088, 1028, 88, 82, 70, 8198, 4162, 2128, 1048, 32768, 84, 74, 28, 26, 22, 14, 8196, 8194, 4160, 4098, 2112, 2064, 1040, 1032, 72, 68, 12, 8192, 4096, 2048, 1024, 80, 66, 24, 20, 18, 10, 6, 64, 16, 8, 4, 2]
def owns1 : List Nat := rows1.map (fun r => r.1.1)
def codes1 : List Nat := [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def owned1_checked : ownCheck topC gate1 acc_extraFive [] rows1 = true := by decide +kernel
lemma owned1_bounds : ∀ x ∈ acc_extraFive, x.1 ∈ owns1 → Imp [gate1] x.1 x.2 := by
  have h := ownCheck_imp topC_ok (e := gate1) (by decide) accBounds_extraFive own0 owned1_checked
  simpa only [owns1, List.append_nil] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def shape1_checked : okTy prior1 acc_extraFive 12 prior1.length gate1 owns1 codes1 (20, 64) [List.range 13] = true := by decide +kernel
def masks_base1 : List (Nat × Nat) := [(0, 1), ((2 ^ 53 - 1), 0), (((2 ^ 54 - 1) <<< 53), 0), (((2 ^ 53 - 1) <<< 107), 0), (((2 ^ 54 - 1) <<< 160), 0)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def masks_base1_full : mFull masks_base1 = true := by decide +kernel
noncomputable def run_base1 (p : Nat × Nat) : Bool :=
  chkT topC [gate1] (tabE gate1 owns1 (pick acc_extraFive codes1)) (20, 64) 0 12 [1] p.1 p.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base1_0 : run_base1 (0, 1) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base1_1 : run_base1 ((2 ^ 53 - 1), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base1_2 : run_base1 (((2 ^ 54 - 1) <<< 53), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base1_3 : run_base1 (((2 ^ 53 - 1) <<< 107), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base1_4 : run_base1 (((2 ^ 54 - 1) <<< 160), 0) = false := by decide +kernel
lemma case1_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior1, ImpT [f] 0 13 1) : ImpT [gate1] 0 13 1 := by
  have hc : ∀ p ∈ masks_base1, run_base1 p = false := by
    intro p hp
    simp only [masks_base1, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact split_base1_0
    · exact split_base1_1
    · exact split_base1_2
    · exact split_base1_3
    · exact split_base1_4
  exact ty_imp_shards_t accBounds_extraFive owned1_bounds shape1_checked masks_base1_full hc h0 (by simpa using hF)
def gate2 : Gt := (false, 0, 6)
def prior2 : List Gt := [(false, 0, 2), (false, 0, 5)]
def rows2 : List ((Nat × Nat) × List Nat) := ownRows acc_extraFive [54, 46, 16400, 16388, 24576, 12288, 18432, 6144, 3072, 16392, 16386, 8224, 8200, 4112, 4100, 2080, 2056, 2050, 38, 8198, 4130, 16384, 50, 42, 22, 14, 8196, 8194, 4128, 4098, 2064, 12, 8192, 4096, 2048, 40, 34, 20, 18, 10, 6, 32, 16, 8, 4, 2]
def owns2 : List Nat := rows2.map (fun r => r.1.1)
def codes2 : List Nat := [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def owned2_checked : ownCheck topC gate2 acc_extraFive [] rows2 = true := by decide +kernel
lemma owned2_bounds : ∀ x ∈ acc_extraFive, x.1 ∈ owns2 → Imp [gate2] x.1 x.2 := by
  have h := ownCheck_imp topC_ok (e := gate2) (by decide) accBounds_extraFive own0 owned2_checked
  simpa only [owns2, List.append_nil] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def shape2_checked : okTy prior2 acc_extraFive 12 prior2.length gate2 owns2 codes2 (26, 4198400) [List.range 13] = true := by decide +kernel
def masks_base2 : List (Nat × Nat) := [(0, 1), ((2 ^ 26 - 1), 0), (((2 ^ 27 - 1) <<< 26), 0), (((2 ^ 27 - 1) <<< 53), 0), (((2 ^ 27 - 1) <<< 80), 0), (((2 ^ 26 - 1) <<< 107), 0), (((2 ^ 13 - 1) <<< 133), 0), (((2 ^ 14 - 1) <<< 146), 0), (((2 ^ 27 - 1) <<< 160), 0), (((2 ^ 27 - 1) <<< 187), 0)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def masks_base2_full : mFull masks_base2 = true := by decide +kernel
noncomputable def run_base2 (p : Nat × Nat) : Bool :=
  chkT topC [gate2] (tabE gate2 owns2 (pick acc_extraFive codes2)) (26, 4198400) 0 12 [1] p.1 p.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base2_0 : run_base2 (0, 1) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base2_1 : run_base2 ((2 ^ 26 - 1), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base2_2 : run_base2 (((2 ^ 27 - 1) <<< 26), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base2_3 : run_base2 (((2 ^ 27 - 1) <<< 53), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base2_4 : run_base2 (((2 ^ 27 - 1) <<< 80), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base2_5 : run_base2 (((2 ^ 26 - 1) <<< 107), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base2_6 : run_base2 (((2 ^ 13 - 1) <<< 133), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base2_7 : run_base2 (((2 ^ 14 - 1) <<< 146), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base2_8 : run_base2 (((2 ^ 27 - 1) <<< 160), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base2_9 : run_base2 (((2 ^ 27 - 1) <<< 187), 0) = false := by decide +kernel
lemma case2_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior2, ImpT [f] 0 13 1) : ImpT [gate2] 0 13 1 := by
  have hc : ∀ p ∈ masks_base2, run_base2 p = false := by
    intro p hp
    simp only [masks_base2, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact split_base2_0
    · exact split_base2_1
    · exact split_base2_2
    · exact split_base2_3
    · exact split_base2_4
    · exact split_base2_5
    · exact split_base2_6
    · exact split_base2_7
    · exact split_base2_8
    · exact split_base2_9
  exact ty_imp_shards_t accBounds_extraFive owned2_bounds shape2_checked masks_base2_full hc h0 (by simpa using hF)
def gate4 : Gt := (true, 1, 2)
def prior4 : List Gt := [(false, 0, 2), (false, 0, 5), (false, 0, 6), (false, 5, 6)]
def rows4 : List ((Nat × Nat) × List Nat) := ownRows acc_extraFive [120, 113, 89, 57, 32784, 16400, 520, 112, 32800, 32776, 32769, 16448, 16392, 16385, 4112, 4097, 576, 544, 528, 88, 81, 56, 49, 25, 4192, 32768, 16384, 512, 4160, 4128, 72, 4096, 80, 48, 40, 24, 17, 64, 32, 16, 8]
def owns4 : List Nat := rows4.map (fun r => r.1.1)
def codes4 : List Nat := [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def owned4_checked : ownCheck topC gate4 acc_extraFive [] rows4 = true := by decide +kernel
lemma owned4_bounds : ∀ x ∈ acc_extraFive, x.1 ∈ owns4 → Imp [gate4] x.1 x.2 := by
  have h := ownCheck_imp topC_ok (e := gate4) (by decide) accBounds_extraFive own0 owned4_checked
  simpa only [owns4, List.append_nil] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def shape4_checked : okTy prior4 acc_extraFive 12 prior4.length gate4 owns4 codes4 (46, 4415494816768) [List.range 13] = true := by decide +kernel
def masks_base4 : List (Nat × Nat) := [(0, 1), ((2 ^ 53 - 1), 0), (((2 ^ 27 - 1) <<< 53), 0), (((2 ^ 27 - 1) <<< 80), 0), (((2 ^ 26 - 1) <<< 107), 0), (((2 ^ 13 - 1) <<< 133), 0), (((2 ^ 14 - 1) <<< 146), 0), (((2 ^ 54 - 1) <<< 160), 0)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def masks_base4_full : mFull masks_base4 = true := by decide +kernel
noncomputable def run_base4 (p : Nat × Nat) : Bool :=
  chkT topC [gate4] (tabE gate4 owns4 (pick acc_extraFive codes4)) (46, 4415494816768) 0 12 [1] p.1 p.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base4_0 : run_base4 (0, 1) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base4_1 : run_base4 ((2 ^ 53 - 1), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base4_2 : run_base4 (((2 ^ 27 - 1) <<< 53), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base4_3 : run_base4 (((2 ^ 27 - 1) <<< 80), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base4_4 : run_base4 (((2 ^ 26 - 1) <<< 107), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base4_5 : run_base4 (((2 ^ 13 - 1) <<< 133), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base4_6 : run_base4 (((2 ^ 14 - 1) <<< 146), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base4_7 : run_base4 (((2 ^ 54 - 1) <<< 160), 0) = false := by decide +kernel
lemma case4_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior4, ImpT [f] 0 13 1) : ImpT [gate4] 0 13 1 := by
  have hc : ∀ p ∈ masks_base4, run_base4 p = false := by
    intro p hp
    simp only [masks_base4, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact split_base4_0
    · exact split_base4_1
    · exact split_base4_2
    · exact split_base4_3
    · exact split_base4_4
    · exact split_base4_5
    · exact split_base4_6
    · exact split_base4_7
  exact ty_imp_shards_t accBounds_extraFive owned4_bounds shape4_checked masks_base4_full hc h0 (by simpa using hF)
def gate5 : Gt := (false, 1, 4)
def prior5 : List Gt := [(false, 0, 2), (false, 0, 5), (false, 0, 6), (false, 5, 6), (true, 1, 2)]
def rows5 : List ((Nat × Nat) × List Nat) := ownRows acc_extraFive [108, 105, 101, 77, 16388, 520, 76, 18432, 6144, 4608, 16448, 16392, 16385, 4100, 4097, 2080, 2056, 576, 544, 516, 100, 97, 73, 4192, 2113, 16384, 512, 104, 69, 4160, 4128, 2112, 2049, 72, 68, 12, 4096, 2048, 96, 65, 64, 8, 4]
def owns5 : List Nat := rows5.map (fun r => r.1.1)
def codes5 : List Nat := [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def owned5_checked : ownCheck topC gate5 acc_extraFive [] rows5 = true := by decide +kernel
lemma owned5_bounds : ∀ x ∈ acc_extraFive, x.1 ∈ owns5 → Imp [gate5] x.1 x.2 := by
  have h := ownCheck_imp topC_ok (e := gate5) (by decide) accBounds_extraFive own0 owned5_checked
  simpa only [owns5, List.append_nil] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def shape5_checked : okTy prior5 acc_extraFive 12 prior5.length gate5 owns5 codes5 (46, 4415494816770) [List.range 13] = true := by decide +kernel
def masks_base5 : List (Nat × Nat) := [(0, 1), ((2 ^ 26 - 1), 0), (((2 ^ 27 - 1) <<< 26), 0), (((2 ^ 13 - 1) <<< 53), 0), (((2 ^ 7 - 1) <<< 66), 0), (((2 ^ 7 - 1) <<< 73), 0), (((2 ^ 27 - 1) <<< 80), 0), (((2 ^ 26 - 1) <<< 107), 0), (((2 ^ 6 - 1) <<< 133), 0), (((2 ^ 7 - 1) <<< 139), 0), (((2 ^ 14 - 1) <<< 146), 0), (((2 ^ 27 - 1) <<< 160), 0), (((2 ^ 27 - 1) <<< 187), 0)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def masks_base5_full : mFull masks_base5 = true := by decide +kernel
noncomputable def run_base5 (p : Nat × Nat) : Bool :=
  chkT topC [gate5] (tabE gate5 owns5 (pick acc_extraFive codes5)) (46, 4415494816770) 0 12 [1] p.1 p.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base5_0 : run_base5 (0, 1) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base5_1 : run_base5 ((2 ^ 26 - 1), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base5_2 : run_base5 (((2 ^ 27 - 1) <<< 26), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base5_3 : run_base5 (((2 ^ 13 - 1) <<< 53), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base5_4 : run_base5 (((2 ^ 7 - 1) <<< 66), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base5_5 : run_base5 (((2 ^ 7 - 1) <<< 73), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base5_6 : run_base5 (((2 ^ 27 - 1) <<< 80), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base5_7 : run_base5 (((2 ^ 26 - 1) <<< 107), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base5_8 : run_base5 (((2 ^ 6 - 1) <<< 133), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base5_9 : run_base5 (((2 ^ 7 - 1) <<< 139), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base5_10 : run_base5 (((2 ^ 14 - 1) <<< 146), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base5_11 : run_base5 (((2 ^ 27 - 1) <<< 160), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_base5_12 : run_base5 (((2 ^ 27 - 1) <<< 187), 0) = false := by decide +kernel
lemma case5_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior5, ImpT [f] 0 13 1) : ImpT [gate5] 0 13 1 := by
  have hc : ∀ p ∈ masks_base5, run_base5 p = false := by
    intro p hp
    simp only [masks_base5, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact split_base5_0
    · exact split_base5_1
    · exact split_base5_2
    · exact split_base5_3
    · exact split_base5_4
    · exact split_base5_5
    · exact split_base5_6
    · exact split_base5_7
    · exact split_base5_8
    · exact split_base5_9
    · exact split_base5_10
    · exact split_base5_11
    · exact split_base5_12
  exact ty_imp_shards_t accBounds_extraFive owned5_bounds shape5_checked masks_base5_full hc h0 (by simpa using hF)
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
def masks_sym0 : List (Nat × Nat) := [((2 ^ 214 - 1), 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def masks_sym0_full : mFull masks_sym0 = true := by decide +kernel
noncomputable def run_sym0 (p : Nat × Nat) : Bool :=
  chkT topC [gate_s0] (tabE gate_s0 owns_s0 (pick acc_extraFive codes_s0)) (121, ((0x80c000000080 <<< 64) + 0x8200020000000400)) 0 12 [1] p.1 p.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym0_0 : run_sym0 ((2 ^ 214 - 1), 1) = false := by decide +kernel
lemma case_s0_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior_s0, ImpT [f] 0 13 1) : ImpT [gate_s0] 0 13 1 := by
  have hc : ∀ p ∈ masks_sym0, run_sym0 p = false := by
    intro p hp
    simp only [masks_sym0, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    · exact split_sym0_0
  exact ty_imp_shards_t accBounds_extraFive owned_s0_bounds shape_s0_checked masks_sym0_full hc h0 (by simpa using hF)
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
def masks_sym1 : List (Nat × Nat) := [((2 ^ 214 - 1), 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def masks_sym1_full : mFull masks_sym1 = true := by decide +kernel
noncomputable def run_sym1 (p : Nat × Nat) : Bool :=
  chkT topC [gate_s1] (tabE gate_s1 owns_s1 (pick acc_extraFive codes_s1)) (125, ((0x1000000100082000 <<< 64) + 0x0000200000401004)) 0 12 [1] p.1 p.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym1_0 : run_sym1 ((2 ^ 214 - 1), 1) = false := by decide +kernel
lemma case_s1_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior_s1, ImpT [f] 0 13 1) : ImpT [gate_s1] 0 13 1 := by
  have hc : ∀ p ∈ masks_sym1, run_sym1 p = false := by
    intro p hp
    simp only [masks_sym1, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    · exact split_sym1_0
  exact ty_imp_shards_t accBounds_extraFive owned_s1_bounds shape_s1_checked masks_sym1_full hc h0 (by simpa using hF)
def gate_s2 : Gt := (false, 1, 2)
def prior_s2 : List Gt := [(false, 0, 2), (false, 3, 5), (false, 0, 5), (false, 0, 6), (false, 5, 6), (true, 1, 2), (true, 3, 4), (false, 1, 4), (false, 0, 1), (false, 4, 5), (false, 0, 3), (false, 2, 5)]
def rows_s2 : List ((Nat × Nat) × List Nat) := ownRows acc_extraFive [120, 113, 89, 57, 105, 32784, 16400, 520, 112, 40960, 24576, 12288, 4608, 32800, 32776, 32769, 16448, 16392, 16385, 8256, 8224, 8200, 4112, 4097, 576, 544, 528, 97, 88, 81, 73, 56, 49, 41, 25, 4192, 32768, 16384, 512, 104, 8193, 4160, 4128, 72, 8192, 4096, 96, 80, 65, 48, 40, 33, 24, 17, 9, 64, 32, 16, 8, 1]
def owns_s2 : List Nat := rows_s2.map (fun r => r.1.1)
def codes_s2 : List Nat := [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma owned_s2_checked : ownCheck topC gate_s2 acc_extraFive [] rows_s2 = true := by decide +kernel
lemma owned_s2_bounds : ∀ x ∈ acc_extraFive, x.1 ∈ owns_s2 → Imp [gate_s2] x.1 x.2 := by
  have h := ownCheck_imp topC_ok (e := gate_s2) (by decide) accBounds_extraFive own0 owned_s2_checked
  simpa only [owns_s2, List.append_nil] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma shape_s2_checked : okTy prior_s2 acc_extraFive 12 prior_s2.length gate_s2 owns_s2 codes_s2 (78, ((0x2c41 <<< 64) + 0x0400000141000094)) [List.range 13] = true := by decide +kernel
def masks_sym2 : List (Nat × Nat) := [((2 ^ 214 - 1), 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def masks_sym2_full : mFull masks_sym2 = true := by decide +kernel
noncomputable def run_sym2 (p : Nat × Nat) : Bool :=
  chkT topC [gate_s2] (tabE gate_s2 owns_s2 (pick acc_extraFive codes_s2)) (78, ((0x2c41 <<< 64) + 0x0400000141000094)) 0 12 [1] p.1 p.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym2_0 : run_sym2 ((2 ^ 214 - 1), 1) = false := by decide +kernel
lemma case_s2_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior_s2, ImpT [f] 0 13 1) : ImpT [gate_s2] 0 13 1 := by
  have hc : ∀ p ∈ masks_sym2, run_sym2 p = false := by
    intro p hp
    simp only [masks_sym2, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    · exact split_sym2_0
  exact ty_imp_shards_t accBounds_extraFive owned_s2_bounds shape_s2_checked masks_sym2_full hc h0 (by simpa using hF)
def gate_s3 : Gt := (false, 1, 6)
def prior_s3 : List Gt := [(false, 0, 2), (false, 3, 5), (false, 0, 5), (false, 0, 6), (false, 5, 6), (true, 1, 2), (true, 3, 4), (false, 1, 4), (false, 0, 1), (false, 4, 5), (false, 0, 3), (false, 2, 5), (false, 1, 2), (false, 3, 4)]
def rows_s3 : List ((Nat × Nat) × List Nat) := ownRows acc_extraFive [60, 57, 45, 53, 29, 16400, 16388, 520, 24576, 12288, 18432, 6144, 4608, 16392, 16385, 8224, 8200, 4112, 4100, 4097, 2080, 2056, 544, 528, 516, 56, 52, 49, 44, 41, 37, 25, 13, 8197, 2065, 16384, 512, 28, 21, 8196, 8193, 4128, 2064, 2049, 12, 8192, 4096, 2048, 48, 40, 36, 33, 24, 20, 17, 9, 5, 32, 16, 8, 4, 1]
def owns_s3 : List Nat := rows_s3.map (fun r => r.1.1)
def codes_s3 : List Nat := [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def owned_s3_checked : ownCheck topC gate_s3 acc_extraFive [] rows_s3 = true := by decide +kernel
lemma owned_s3_bounds : ∀ x ∈ acc_extraFive, x.1 ∈ owns_s3 → Imp [gate_s3] x.1 x.2 := by
  have h := ownCheck_imp topC_ok (e := gate_s3) (by decide) accBounds_extraFive own0 owned_s3_checked
  simpa only [owns_s3, List.append_nil] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def shape_s3_checked : okTy prior_s3 acc_extraFive 12 prior_s3.length gate_s3 owns_s3 codes_s3 (114, ((0xb1010001000 <<< 64) + 0x0010002001201112)) [List.range 13] = true := by decide +kernel
def masks_sym3 : List (Nat × Nat) := [(0, 1), ((2 ^ 53 - 1), 0), (((2 ^ 54 - 1) <<< 53), 0), (((2 ^ 53 - 1) <<< 107), 0), (((2 ^ 54 - 1) <<< 160), 0)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def masks_sym3_full : mFull masks_sym3 = true := by decide +kernel
noncomputable def run_sym3 (p : Nat × Nat) : Bool :=
  chkT topC [gate_s3] (tabE gate_s3 owns_s3 (pick acc_extraFive codes_s3)) (114, ((0xb1010001000 <<< 64) + 0x0010002001201112)) 0 12 [1] p.1 p.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym3_0 : run_sym3 (0, 1) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym3_1 : run_sym3 ((2 ^ 53 - 1), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym3_2 : run_sym3 (((2 ^ 54 - 1) <<< 53), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym3_3 : run_sym3 (((2 ^ 53 - 1) <<< 107), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym3_4 : run_sym3 (((2 ^ 54 - 1) <<< 160), 0) = false := by decide +kernel
lemma case_s3_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior_s3, ImpT [f] 0 13 1) : ImpT [gate_s3] 0 13 1 := by
  have hc : ∀ p ∈ masks_sym3, run_sym3 p = false := by
    intro p hp
    simp only [masks_sym3, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact split_sym3_0
    · exact split_sym3_1
    · exact split_sym3_2
    · exact split_sym3_3
    · exact split_sym3_4
  exact ty_imp_shards_t accBounds_extraFive owned_s3_bounds shape_s3_checked masks_sym3_full hc h0 (by simpa using hF)
def gate_s4 : Gt := (false, 2, 3)
def prior_s4 : List Gt := [(false, 0, 2), (false, 3, 5), (false, 0, 5), (false, 0, 6), (false, 5, 6), (true, 1, 2), (true, 3, 4), (false, 1, 4), (false, 0, 1), (false, 4, 5), (false, 0, 3), (false, 2, 5), (false, 1, 2), (false, 3, 4), (false, 1, 6), (false, 4, 6)]
def rows_s4 : List ((Nat × Nat) × List Nat) := ownRows acc_extraFive [114, 113, 99, 83, 51, 32784, 32770, 16400, 514, 112, 67, 40960, 24576, 33792, 1536, 32800, 32769, 16448, 16386, 16385, 8256, 8224, 1088, 1025, 576, 544, 528, 98, 97, 82, 81, 49, 35, 8195, 1072, 32768, 16384, 512, 50, 19, 8194, 8193, 1056, 1040, 8192, 1024, 96, 80, 66, 65, 48, 34, 33, 18, 17, 3, 64, 32, 16, 2, 1]
def owns_s4 : List Nat := rows_s4.map (fun r => r.1.1)
def codes_s4 : List Nat := [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def owned_s4_checked : ownCheck topC gate_s4 acc_extraFive [] rows_s4 = true := by decide +kernel
lemma owned_s4_bounds : ∀ x ∈ acc_extraFive, x.1 ∈ owns_s4 → Imp [gate_s4] x.1 x.2 := by
  have h := ownCheck_imp topC_ok (e := gate_s4) (by decide) accBounds_extraFive own0 owned_s4_checked
  simpa only [owns_s4, List.append_nil] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def shape_s4_checked : okTy prior_s4 acc_extraFive 12 prior_s4.length gate_s4 owns_s4 codes_s4 (150, ((((0x100000 <<< 64) + 0x0000008220000000) <<< 64) + 0x4470c00009100004)) [List.range 13] = true := by decide +kernel
def masks_sym4 : List (Nat × Nat) := [(0, 1), ((2 ^ 53 - 1), 0), (((2 ^ 54 - 1) <<< 53), 0), (((2 ^ 53 - 1) <<< 107), 0), (((2 ^ 54 - 1) <<< 160), 0)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def masks_sym4_full : mFull masks_sym4 = true := by decide +kernel
noncomputable def run_sym4 (p : Nat × Nat) : Bool :=
  chkT topC [gate_s4] (tabE gate_s4 owns_s4 (pick acc_extraFive codes_s4)) (150, ((((0x100000 <<< 64) + 0x0000008220000000) <<< 64) + 0x4470c00009100004)) 0 12 [1] p.1 p.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym4_0 : run_sym4 (0, 1) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym4_1 : run_sym4 ((2 ^ 53 - 1), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym4_2 : run_sym4 (((2 ^ 54 - 1) <<< 53), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym4_3 : run_sym4 (((2 ^ 53 - 1) <<< 107), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym4_4 : run_sym4 (((2 ^ 54 - 1) <<< 160), 0) = false := by decide +kernel
lemma case_s4_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior_s4, ImpT [f] 0 13 1) : ImpT [gate_s4] 0 13 1 := by
  have hc : ∀ p ∈ masks_sym4, run_sym4 p = false := by
    intro p hp
    simp only [masks_sym4, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact split_sym4_0
    · exact split_sym4_1
    · exact split_sym4_2
    · exact split_sym4_3
    · exact split_sym4_4
  exact ty_imp_shards_t accBounds_extraFive owned_s4_bounds shape_s4_checked masks_sym4_full hc h0 (by simpa using hF)
def gate_s5 : Gt := (false, 0, 4)
def prior_s5 : List Gt := [(false, 0, 2), (false, 3, 5), (false, 0, 5), (false, 0, 6), (false, 5, 6), (true, 1, 2), (true, 3, 4), (false, 1, 4), (false, 0, 1), (false, 4, 5), (false, 0, 3), (false, 2, 5), (false, 1, 2), (false, 3, 4), (false, 1, 6), (false, 4, 6), (false, 2, 3)]
def rows_s5 : List ((Nat × Nat) × List Nat) := ownRows acc_extraFive [108, 78, 46, 32770, 16388, 76, 18432, 6144, 33792, 3072, 32800, 32776, 32772, 16448, 16392, 16386, 2080, 2056, 2050, 1088, 1028, 44, 1064, 32768, 16384, 104, 74, 42, 14, 2112, 1056, 1032, 72, 68, 12, 2048, 1024, 40, 34, 10, 64, 32, 8, 4, 2]
def owns_s5 : List Nat := rows_s5.map (fun r => r.1.1)
def codes_s5 : List Nat := [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def owned_s5_checked : ownCheck topC gate_s5 acc_extraFive [] rows_s5 = true := by decide +kernel
lemma owned_s5_bounds : ∀ x ∈ acc_extraFive, x.1 ∈ owns_s5 → Imp [gate_s5] x.1 x.2 := by
  have h := ownCheck_imp topC_ok (e := gate_s5) (by decide) accBounds_extraFive own0 owned_s5_checked
  simpa only [owns_s5, List.append_nil] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def shape_s5_checked : okTy prior_s5 acc_extraFive 12 prior_s5.length gate_s5 owns_s5 codes_s5 (139, ((((0x188 <<< 64) + 0x00c0000000058400) <<< 64) + 0x5020021000400001)) [List.range 13] = true := by decide +kernel
def masks_sym5 : List (Nat × Nat) := [(0, 1), ((2 ^ 26 - 1), 0), (((2 ^ 27 - 1) <<< 26), 0), (((2 ^ 54 - 1) <<< 53), 0), (((2 ^ 53 - 1) <<< 107), 0), (((2 ^ 54 - 1) <<< 160), 0)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def masks_sym5_full : mFull masks_sym5 = true := by decide +kernel
noncomputable def run_sym5 (p : Nat × Nat) : Bool :=
  chkT topC [gate_s5] (tabE gate_s5 owns_s5 (pick acc_extraFive codes_s5)) (139, ((((0x188 <<< 64) + 0x00c0000000058400) <<< 64) + 0x5020021000400001)) 0 12 [1] p.1 p.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym5_0 : run_sym5 (0, 1) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym5_1 : run_sym5 ((2 ^ 26 - 1), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym5_2 : run_sym5 (((2 ^ 27 - 1) <<< 26), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym5_3 : run_sym5 (((2 ^ 54 - 1) <<< 53), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym5_4 : run_sym5 (((2 ^ 53 - 1) <<< 107), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym5_5 : run_sym5 (((2 ^ 54 - 1) <<< 160), 0) = false := by decide +kernel
lemma case_s5_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior_s5, ImpT [f] 0 13 1) : ImpT [gate_s5] 0 13 1 := by
  have hc : ∀ p ∈ masks_sym5, run_sym5 p = false := by
    intro p hp
    simp only [masks_sym5, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact split_sym5_0
    · exact split_sym5_1
    · exact split_sym5_2
    · exact split_sym5_3
    · exact split_sym5_4
    · exact split_sym5_5
  exact ty_imp_shards_t accBounds_extraFive owned_s5_bounds shape_s5_checked masks_sym5_full hc h0 (by simpa using hF)
def gate_s6 : Gt := (false, 1, 3)
def prior_s6 : List Gt := [(false, 0, 2), (false, 3, 5), (false, 0, 5), (false, 0, 6), (false, 5, 6), (true, 1, 2), (true, 3, 4), (false, 1, 4), (false, 0, 1), (false, 4, 5), (false, 0, 3), (false, 2, 5), (false, 1, 2), (false, 3, 4), (false, 1, 6), (false, 4, 6), (false, 2, 3), (false, 0, 4), (false, 1, 5)]
def rows_s6 : List ((Nat × Nat) × List Nat) := ownRows acc_extraFive [101, 53, 32784, 16400, 16388, 40960, 24576, 18432, 32800, 32772, 32769, 16448, 16385, 8256, 8224, 37, 8197, 32768, 16384, 69, 21, 8196, 8193, 68, 8192, 20, 17, 5, 64, 16, 4, 1]
def owns_s6 : List Nat := rows_s6.map (fun r => r.1.1)
def codes_s6 : List Nat := [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def owned_s6_checked : ownCheck topC gate_s6 acc_extraFive [] rows_s6 = true := by decide +kernel
lemma owned_s6_bounds : ∀ x ∈ acc_extraFive, x.1 ∈ owns_s6 → Imp [gate_s6] x.1 x.2 := by
  have h := ownCheck_imp topC_ok (e := gate_s6) (by decide) accBounds_extraFive own0 owned_s6_checked
  simpa only [owns_s6, List.append_nil] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def shape_s6_checked : okTy prior_s6 acc_extraFive 12 prior_s6.length gate_s6 owns_s6 codes_s6 (108, ((0xc1040 <<< 64) + 0x00800044e4214b01)) [List.range 13] = true := by decide +kernel
def masks_sym6 : List (Nat × Nat) := [(0, 1), ((2 ^ 26 - 1), 0), (((2 ^ 6 - 1) <<< 26), 0), (((2 ^ 7 - 1) <<< 32), 0), (((2 ^ 7 - 1) <<< 39), 0), (((2 ^ 1 - 1) <<< 46), 0), (((2 ^ 1 - 1) <<< 47), 0), (((2 ^ 1 - 1) <<< 48), 0), (((2 ^ 4 - 1) <<< 49), 0), (((2 ^ 3 - 1) <<< 53), 0), (((2 ^ 3 - 1) <<< 56), 0), (((2 ^ 7 - 1) <<< 59), 0), (((2 ^ 14 - 1) <<< 66), 0), (((2 ^ 27 - 1) <<< 80), 0), (((2 ^ 13 - 1) <<< 107), 0), (((2 ^ 13 - 1) <<< 120), 0), (((2 ^ 13 - 1) <<< 133), 0), (((2 ^ 7 - 1) <<< 146), 0), (((2 ^ 7 - 1) <<< 153), 0), (((2 ^ 54 - 1) <<< 160), 0)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def masks_sym6_full : mFull masks_sym6 = true := by decide +kernel
noncomputable def run_sym6 (p : Nat × Nat) : Bool :=
  chkT topC [gate_s6] (tabE gate_s6 owns_s6 (pick acc_extraFive codes_s6)) (108, ((0xc1040 <<< 64) + 0x00800044e4214b01)) 0 12 [1] p.1 p.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym6_0 : run_sym6 (0, 1) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym6_1 : run_sym6 ((2 ^ 26 - 1), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym6_2 : run_sym6 (((2 ^ 6 - 1) <<< 26), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym6_3 : run_sym6 (((2 ^ 7 - 1) <<< 32), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym6_4 : run_sym6 (((2 ^ 7 - 1) <<< 39), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym6_5 : run_sym6 (((2 ^ 1 - 1) <<< 46), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym6_6 : run_sym6 (((2 ^ 1 - 1) <<< 47), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym6_7 : run_sym6 (((2 ^ 1 - 1) <<< 48), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym6_8 : run_sym6 (((2 ^ 4 - 1) <<< 49), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym6_9 : run_sym6 (((2 ^ 3 - 1) <<< 53), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym6_10 : run_sym6 (((2 ^ 3 - 1) <<< 56), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym6_11 : run_sym6 (((2 ^ 7 - 1) <<< 59), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym6_12 : run_sym6 (((2 ^ 14 - 1) <<< 66), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym6_13 : run_sym6 (((2 ^ 27 - 1) <<< 80), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym6_14 : run_sym6 (((2 ^ 13 - 1) <<< 107), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym6_15 : run_sym6 (((2 ^ 13 - 1) <<< 120), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym6_16 : run_sym6 (((2 ^ 13 - 1) <<< 133), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym6_17 : run_sym6 (((2 ^ 7 - 1) <<< 146), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym6_18 : run_sym6 (((2 ^ 7 - 1) <<< 153), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym6_19 : run_sym6 (((2 ^ 54 - 1) <<< 160), 0) = false := by decide +kernel
lemma case_s6_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior_s6, ImpT [f] 0 13 1) : ImpT [gate_s6] 0 13 1 := by
  have hc : ∀ p ∈ masks_sym6, run_sym6 p = false := by
    intro p hp
    simp only [masks_sym6, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact split_sym6_0
    · exact split_sym6_1
    · exact split_sym6_2
    · exact split_sym6_3
    · exact split_sym6_4
    · exact split_sym6_5
    · exact split_sym6_6
    · exact split_sym6_7
    · exact split_sym6_8
    · exact split_sym6_9
    · exact split_sym6_10
    · exact split_sym6_11
    · exact split_sym6_12
    · exact split_sym6_13
    · exact split_sym6_14
    · exact split_sym6_15
    · exact split_sym6_16
    · exact split_sym6_17
    · exact split_sym6_18
    · exact split_sym6_19
  exact ty_imp_shards_t accBounds_extraFive owned_s6_bounds shape_s6_checked masks_sym6_full hc h0 (by simpa using hF)
def gate_s7 : Gt := (false, 2, 6)
def prior_s7 : List Gt := [(false, 0, 2), (false, 3, 5), (false, 0, 5), (false, 0, 6), (false, 5, 6), (true, 1, 2), (true, 3, 4), (false, 1, 4), (false, 0, 1), (false, 4, 5), (false, 0, 3), (false, 2, 5), (false, 1, 2), (false, 3, 4), (false, 1, 6), (false, 4, 6), (false, 2, 3), (false, 0, 4), (false, 1, 5), (false, 1, 3), (false, 2, 4)]
def rows_s7 : List ((Nat × Nat) × List Nat) := ownRows acc_extraFive [51, 43, 27, 16400, 520, 514, 24576, 12288, 4608, 1536, 16392, 16386, 16385, 8224, 8200, 4112, 4097, 544, 528, 35, 11, 8195, 4130, 16384, 512, 50, 42, 26, 19, 8194, 8193, 4128, 4098, 8192, 4096, 40, 34, 24, 18, 10, 3, 32, 16, 8, 2]
def owns_s7 : List Nat := rows_s7.map (fun r => r.1.1)
def codes_s7 : List Nat := [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def owned_s7_checked : ownCheck topC gate_s7 acc_extraFive [] rows_s7 = true := by decide +kernel
lemma owned_s7_bounds : ∀ x ∈ acc_extraFive, x.1 ∈ owns_s7 → Imp [gate_s7] x.1 x.2 := by
  have h := ownCheck_imp topC_ok (e := gate_s7) (by decide) accBounds_extraFive own0 owned_s7_checked
  simpa only [owns_s7, List.append_nil] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def shape_s7_checked : okTy prior_s7 acc_extraFive 12 prior_s7.length gate_s7 owns_s7 codes_s7 (206, ((((((0x400 <<< 64) + 0x4200000004000101) <<< 64) + 0x2000000000008306) <<< 64) + 0x2400040001081800)) [List.range 13] = true := by decide +kernel
def masks_sym7 : List (Nat × Nat) := [(0, 1), ((2 ^ 26 - 1), 0), (((2 ^ 27 - 1) <<< 26), 0), (((2 ^ 54 - 1) <<< 53), 0), (((2 ^ 26 - 1) <<< 107), 0), (((2 ^ 13 - 1) <<< 133), 0), (((2 ^ 14 - 1) <<< 146), 0), (((2 ^ 54 - 1) <<< 160), 0)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def masks_sym7_full : mFull masks_sym7 = true := by decide +kernel
noncomputable def run_sym7 (p : Nat × Nat) : Bool :=
  chkT topC [gate_s7] (tabE gate_s7 owns_s7 (pick acc_extraFive codes_s7)) (206, ((((((0x400 <<< 64) + 0x4200000004000101) <<< 64) + 0x2000000000008306) <<< 64) + 0x2400040001081800)) 0 12 [1] p.1 p.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym7_0 : run_sym7 (0, 1) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym7_1 : run_sym7 ((2 ^ 26 - 1), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym7_2 : run_sym7 (((2 ^ 27 - 1) <<< 26), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym7_3 : run_sym7 (((2 ^ 54 - 1) <<< 53), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym7_4 : run_sym7 (((2 ^ 26 - 1) <<< 107), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym7_5 : run_sym7 (((2 ^ 13 - 1) <<< 133), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym7_6 : run_sym7 (((2 ^ 14 - 1) <<< 146), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym7_7 : run_sym7 (((2 ^ 54 - 1) <<< 160), 0) = false := by decide +kernel
lemma case_s7_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior_s7, ImpT [f] 0 13 1) : ImpT [gate_s7] 0 13 1 := by
  have hc : ∀ p ∈ masks_sym7, run_sym7 p = false := by
    intro p hp
    simp only [masks_sym7, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact split_sym7_0
    · exact split_sym7_1
    · exact split_sym7_2
    · exact split_sym7_3
    · exact split_sym7_4
    · exact split_sym7_5
    · exact split_sym7_6
    · exact split_sym7_7
  exact ty_imp_shards_t accBounds_extraFive owned_s7_bounds shape_s7_checked masks_sym7_full hc h0 (by simpa using hF)
def gate_s8 : Gt := (true, 0, 1)
def prior_s8 : List Gt := [(false, 0, 2), (false, 3, 5), (false, 0, 5), (false, 0, 6), (false, 5, 6), (true, 1, 2), (true, 3, 4), (false, 1, 4), (false, 0, 1), (false, 4, 5), (false, 0, 3), (false, 2, 5), (false, 1, 2), (false, 3, 4), (false, 1, 6), (false, 4, 6), (false, 2, 3), (false, 0, 4), (false, 1, 5), (false, 1, 3), (false, 2, 4), (false, 2, 6), (false, 3, 6)]
def rows_s8 : List ((Nat × Nat) × List Nat) := ownRows acc_extraFive [120, 116, 60, 32784, 112, 32800, 32776, 32772, 4112, 4100, 2080, 2056, 56, 52, 4192, 2128, 32768, 4160, 4128, 2112, 2064, 4096, 2048, 48, 40, 24, 20, 32, 16]
def owns_s8 : List Nat := rows_s8.map (fun r => r.1.1)
def codes_s8 : List Nat := [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def owned_s8_checked : ownCheck topC gate_s8 acc_extraFive [] rows_s8 = true := by decide +kernel
lemma owned_s8_bounds : ∀ x ∈ acc_extraFive, x.1 ∈ owns_s8 → Imp [gate_s8] x.1 x.2 := by
  have h := ownCheck_imp topC_ok (e := gate_s8) (by decide) accBounds_extraFive own0 owned_s8_checked
  simpa only [owns_s8, List.append_nil] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def shape_s8_checked : okTy prior_s8 acc_extraFive 12 prior_s8.length gate_s8 owns_s8 codes_s8 (220, ((((((0x400400a <<< 64) + 0x6000402000404000) <<< 64) + 0x1823000000804209) <<< 64) + 0x0010002008000000)) [List.range 13] = true := by decide +kernel
def masks_sym8 : List (Nat × Nat) := [(0, 1), ((2 ^ 13 - 1), 0), (((2 ^ 13 - 1) <<< 13), 0), (((2 ^ 6 - 1) <<< 26), 0), (((2 ^ 7 - 1) <<< 32), 0), (((2 ^ 14 - 1) <<< 39), 0), (((2 ^ 27 - 1) <<< 53), 0), (((2 ^ 27 - 1) <<< 80), 0), (((2 ^ 13 - 1) <<< 107), 0), (((2 ^ 13 - 1) <<< 120), 0), (((2 ^ 13 - 1) <<< 133), 0), (((2 ^ 7 - 1) <<< 146), 0), (((2 ^ 7 - 1) <<< 153), 0), (((2 ^ 6 - 1) <<< 160), 0), (((2 ^ 7 - 1) <<< 166), 0), (((2 ^ 14 - 1) <<< 173), 0), (((2 ^ 27 - 1) <<< 187), 0)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def masks_sym8_full : mFull masks_sym8 = true := by decide +kernel
noncomputable def run_sym8 (p : Nat × Nat) : Bool :=
  chkT topC [gate_s8] (tabE gate_s8 owns_s8 (pick acc_extraFive codes_s8)) (220, ((((((0x400400a <<< 64) + 0x6000402000404000) <<< 64) + 0x1823000000804209) <<< 64) + 0x0010002008000000)) 0 12 [1] p.1 p.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym8_0 : run_sym8 (0, 1) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym8_1 : run_sym8 ((2 ^ 13 - 1), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym8_2 : run_sym8 (((2 ^ 13 - 1) <<< 13), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym8_3 : run_sym8 (((2 ^ 6 - 1) <<< 26), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym8_4 : run_sym8 (((2 ^ 7 - 1) <<< 32), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym8_5 : run_sym8 (((2 ^ 14 - 1) <<< 39), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym8_6 : run_sym8 (((2 ^ 27 - 1) <<< 53), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym8_7 : run_sym8 (((2 ^ 27 - 1) <<< 80), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym8_8 : run_sym8 (((2 ^ 13 - 1) <<< 107), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym8_9 : run_sym8 (((2 ^ 13 - 1) <<< 120), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym8_10 : run_sym8 (((2 ^ 13 - 1) <<< 133), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym8_11 : run_sym8 (((2 ^ 7 - 1) <<< 146), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym8_12 : run_sym8 (((2 ^ 7 - 1) <<< 153), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym8_13 : run_sym8 (((2 ^ 6 - 1) <<< 160), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym8_14 : run_sym8 (((2 ^ 7 - 1) <<< 166), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym8_15 : run_sym8 (((2 ^ 14 - 1) <<< 173), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym8_16 : run_sym8 (((2 ^ 27 - 1) <<< 187), 0) = false := by decide +kernel
lemma case_s8_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior_s8, ImpT [f] 0 13 1) : ImpT [gate_s8] 0 13 1 := by
  have hc : ∀ p ∈ masks_sym8, run_sym8 p = false := by
    intro p hp
    simp only [masks_sym8, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact split_sym8_0
    · exact split_sym8_1
    · exact split_sym8_2
    · exact split_sym8_3
    · exact split_sym8_4
    · exact split_sym8_5
    · exact split_sym8_6
    · exact split_sym8_7
    · exact split_sym8_8
    · exact split_sym8_9
    · exact split_sym8_10
    · exact split_sym8_11
    · exact split_sym8_12
    · exact split_sym8_13
    · exact split_sym8_14
    · exact split_sym8_15
    · exact split_sym8_16
  exact ty_imp_shards_t accBounds_extraFive owned_s8_bounds shape_s8_checked masks_sym8_full hc h0 (by simpa using hF)
def gate_s9 : Gt := (true, 0, 3)
def prior_s9 : List Gt := [(false, 0, 2), (false, 3, 5), (false, 0, 5), (false, 0, 6), (false, 5, 6), (true, 1, 2), (true, 3, 4), (false, 1, 4), (false, 0, 1), (false, 4, 5), (false, 0, 3), (false, 2, 5), (false, 1, 2), (false, 3, 4), (false, 1, 6), (false, 4, 6), (false, 2, 3), (false, 0, 4), (false, 1, 5), (false, 1, 3), (false, 2, 4), (false, 2, 6), (false, 3, 6), (true, 0, 1), (true, 4, 5)]
def rows_s9 : List ((Nat × Nat) × List Nat) := ownRows acc_extraFive [116, 114, 102, 112, 8256, 8224, 2080, 2050, 1088, 1028, 100, 98, 8198, 2128, 1072, 8196, 8194, 2112, 2064, 1056, 1040, 68, 8192, 2048, 1024, 96, 34, 64, 32]
def owns_s9 : List Nat := rows_s9.map (fun r => r.1.1)
def codes_s9 : List Nat := [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def owned_s9_checked : ownCheck topC gate_s9 acc_extraFive [] rows_s9 = true := by decide +kernel
lemma owned_s9_bounds : ∀ x ∈ acc_extraFive, x.1 ∈ owns_s9 → Imp [gate_s9] x.1 x.2 := by
  have h := ownCheck_imp topC_ok (e := gate_s9) (by decide) accBounds_extraFive own0 owned_s9_checked
  simpa only [owns_s9, List.append_nil] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def shape_s9_checked : okTy prior_s9 acc_extraFive 12 prior_s9.length gate_s9 owns_s9 codes_s9 (182, ((((0x20011a52000000 <<< 64) + 0x00a0084000042420) <<< 64) + 0x2400000128060002)) [List.range 13] = true := by decide +kernel
def masks_sym9 : List (Nat × Nat) := [(0, 1), ((2 ^ 26 - 1), 0), (((2 ^ 13 - 1) <<< 26), 0), (((2 ^ 7 - 1) <<< 39), 0), (((2 ^ 1 - 1) <<< 46), 0), (((2 ^ 2 - 1) <<< 47), 0), (((2 ^ 4 - 1) <<< 49), 0), (((2 ^ 27 - 1) <<< 53), 0), (((2 ^ 27 - 1) <<< 80), 0), (((2 ^ 26 - 1) <<< 107), 0), (((2 ^ 13 - 1) <<< 133), 0), (((2 ^ 14 - 1) <<< 146), 0), (((2 ^ 54 - 1) <<< 160), 0)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def masks_sym9_full : mFull masks_sym9 = true := by decide +kernel
noncomputable def run_sym9 (p : Nat × Nat) : Bool :=
  chkT topC [gate_s9] (tabE gate_s9 owns_s9 (pick acc_extraFive codes_s9)) (182, ((((0x20011a52000000 <<< 64) + 0x00a0084000042420) <<< 64) + 0x2400000128060002)) 0 12 [1] p.1 p.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym9_0 : run_sym9 (0, 1) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym9_1 : run_sym9 ((2 ^ 26 - 1), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym9_2 : run_sym9 (((2 ^ 13 - 1) <<< 26), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym9_3 : run_sym9 (((2 ^ 7 - 1) <<< 39), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym9_4 : run_sym9 (((2 ^ 1 - 1) <<< 46), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym9_5 : run_sym9 (((2 ^ 2 - 1) <<< 47), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym9_6 : run_sym9 (((2 ^ 4 - 1) <<< 49), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym9_7 : run_sym9 (((2 ^ 27 - 1) <<< 53), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym9_8 : run_sym9 (((2 ^ 27 - 1) <<< 80), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym9_9 : run_sym9 (((2 ^ 26 - 1) <<< 107), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym9_10 : run_sym9 (((2 ^ 13 - 1) <<< 133), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym9_11 : run_sym9 (((2 ^ 14 - 1) <<< 146), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym9_12 : run_sym9 (((2 ^ 54 - 1) <<< 160), 0) = false := by decide +kernel
lemma case_s9_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior_s9, ImpT [f] 0 13 1) : ImpT [gate_s9] 0 13 1 := by
  have hc : ∀ p ∈ masks_sym9, run_sym9 p = false := by
    intro p hp
    simp only [masks_sym9, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact split_sym9_0
    · exact split_sym9_1
    · exact split_sym9_2
    · exact split_sym9_3
    · exact split_sym9_4
    · exact split_sym9_5
    · exact split_sym9_6
    · exact split_sym9_7
    · exact split_sym9_8
    · exact split_sym9_9
    · exact split_sym9_10
    · exact split_sym9_11
    · exact split_sym9_12
  exact ty_imp_shards_t accBounds_extraFive owned_s9_bounds shape_s9_checked masks_sym9_full hc h0 (by simpa using hF)
def gate_s10 : Gt := (true, 1, 6)
def prior_s10 : List Gt := [(false, 0, 2), (false, 3, 5), (false, 0, 5), (false, 0, 6), (false, 5, 6), (true, 1, 2), (true, 3, 4), (false, 1, 4), (false, 0, 1), (false, 4, 5), (false, 0, 3), (false, 2, 5), (false, 1, 2), (false, 3, 4), (false, 1, 6), (false, 4, 6), (false, 2, 3), (false, 0, 4), (false, 1, 5), (false, 1, 3), (false, 2, 4), (false, 2, 6), (false, 3, 6), (true, 0, 1), (true, 4, 5), (true, 0, 3), (true, 2, 5)]
def rows_s10 : List ((Nat × Nat) × List Nat) := ownRows acc_extraFive [60, 57, 45, 520, 8224, 8200, 2080, 2056, 544, 528, 516, 56, 44, 41, 8197, 2065, 512, 8196, 8193, 2064, 2049, 12, 8192, 2048, 40, 24, 8]
def owns_s10 : List Nat := rows_s10.map (fun r => r.1.1)
def codes_s10 : List Nat := [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def owned_s10_checked : ownCheck topC gate_s10 acc_extraFive [] rows_s10 = true := by decide +kernel
lemma owned_s10_bounds : ∀ x ∈ acc_extraFive, x.1 ∈ owns_s10 → Imp [gate_s10] x.1 x.2 := by
  have h := ownCheck_imp topC_ok (e := gate_s10) (by decide) accBounds_extraFive own0 owned_s10_checked
  simpa only [owns_s10, List.append_nil] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def shape_s10_checked : okTy prior_s10 acc_extraFive 12 prior_s10.length gate_s10 owns_s10 codes_s10 (206, ((((((0x400 <<< 64) + 0x4200000006000101) <<< 64) + 0x2020000200008306) <<< 64) + 0x2400048009081800)) [List.range 13] = true := by decide +kernel
def masks_sym10 : List (Nat × Nat) := [(0, 1), ((2 ^ 26 - 1), 0), (((2 ^ 27 - 1) <<< 26), 0), (((2 ^ 27 - 1) <<< 53), 0), (((2 ^ 27 - 1) <<< 80), 0), (((2 ^ 26 - 1) <<< 107), 0), (((2 ^ 13 - 1) <<< 133), 0), (((2 ^ 7 - 1) <<< 146), 0), (((2 ^ 7 - 1) <<< 153), 0), (((2 ^ 27 - 1) <<< 160), 0), (((2 ^ 27 - 1) <<< 187), 0)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def masks_sym10_full : mFull masks_sym10 = true := by decide +kernel
noncomputable def run_sym10 (p : Nat × Nat) : Bool :=
  chkT topC [gate_s10] (tabE gate_s10 owns_s10 (pick acc_extraFive codes_s10)) (206, ((((((0x400 <<< 64) + 0x4200000006000101) <<< 64) + 0x2020000200008306) <<< 64) + 0x2400048009081800)) 0 12 [1] p.1 p.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym10_0 : run_sym10 (0, 1) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym10_1 : run_sym10 ((2 ^ 26 - 1), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym10_2 : run_sym10 (((2 ^ 27 - 1) <<< 26), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym10_3 : run_sym10 (((2 ^ 27 - 1) <<< 53), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym10_4 : run_sym10 (((2 ^ 27 - 1) <<< 80), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym10_5 : run_sym10 (((2 ^ 26 - 1) <<< 107), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym10_6 : run_sym10 (((2 ^ 13 - 1) <<< 133), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym10_7 : run_sym10 (((2 ^ 7 - 1) <<< 146), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym10_8 : run_sym10 (((2 ^ 7 - 1) <<< 153), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym10_9 : run_sym10 (((2 ^ 27 - 1) <<< 160), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym10_10 : run_sym10 (((2 ^ 27 - 1) <<< 187), 0) = false := by decide +kernel
lemma case_s10_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior_s10, ImpT [f] 0 13 1) : ImpT [gate_s10] 0 13 1 := by
  have hc : ∀ p ∈ masks_sym10, run_sym10 p = false := by
    intro p hp
    simp only [masks_sym10, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact split_sym10_0
    · exact split_sym10_1
    · exact split_sym10_2
    · exact split_sym10_3
    · exact split_sym10_4
    · exact split_sym10_5
    · exact split_sym10_6
    · exact split_sym10_7
    · exact split_sym10_8
    · exact split_sym10_9
    · exact split_sym10_10
  exact ty_imp_shards_t accBounds_extraFive owned_s10_bounds shape_s10_checked masks_sym10_full hc h0 (by simpa using hF)
def gate_s11 : Gt := (true, 2, 3)
def prior_s11 : List Gt := [(false, 0, 2), (false, 3, 5), (false, 0, 5), (false, 0, 6), (false, 5, 6), (true, 1, 2), (true, 3, 4), (false, 1, 4), (false, 0, 1), (false, 4, 5), (false, 0, 3), (false, 2, 5), (false, 1, 2), (false, 3, 4), (false, 1, 6), (false, 4, 6), (false, 2, 3), (false, 0, 4), (false, 1, 5), (false, 1, 3), (false, 2, 4), (false, 2, 6), (false, 3, 6), (true, 0, 1), (true, 4, 5), (true, 0, 3), (true, 2, 5), (true, 1, 6), (true, 4, 6)]
def rows_s11 : List ((Nat × Nat) × List Nat) := ownRows acc_extraFive [114, 113, 99, 83, 16400, 514, 112, 67, 16448, 16386, 16385, 8256, 8224, 1088, 1025, 576, 544, 528, 98, 97, 82, 81, 8195, 1072, 16384, 512, 8194, 8193, 1056, 1040, 8192, 1024, 96, 80, 66, 65, 34, 18, 17, 64, 32, 16, 2, 1]
def owns_s11 : List Nat := rows_s11.map (fun r => r.1.1)
def codes_s11 : List Nat := [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def owned_s11_checked : ownCheck topC gate_s11 acc_extraFive [] rows_s11 = true := by decide +kernel
lemma owned_s11_bounds : ∀ x ∈ acc_extraFive, x.1 ∈ owns_s11 → Imp [gate_s11] x.1 x.2 := by
  have h := ownCheck_imp topC_ok (e := gate_s11) (by decide) accBounds_extraFive own0 owned_s11_checked
  simpa only [owns_s11, List.append_nil] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def shape_s11_checked : okTy prior_s11 acc_extraFive 12 prior_s11.length gate_s11 owns_s11 codes_s11 (149, ((((0x18100 <<< 64) + 0x2001025204050710) <<< 64) + 0x4900204020000690)) [List.range 13] = true := by decide +kernel
def masks_sym11 : List (Nat × Nat) := [(0, 1), ((2 ^ 53 - 1), 0), (((2 ^ 54 - 1) <<< 53), 0), (((2 ^ 53 - 1) <<< 107), 0), (((2 ^ 54 - 1) <<< 160), 0)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def masks_sym11_full : mFull masks_sym11 = true := by decide +kernel
noncomputable def run_sym11 (p : Nat × Nat) : Bool :=
  chkT topC [gate_s11] (tabE gate_s11 owns_s11 (pick acc_extraFive codes_s11)) (149, ((((0x18100 <<< 64) + 0x2001025204050710) <<< 64) + 0x4900204020000690)) 0 12 [1] p.1 p.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym11_0 : run_sym11 (0, 1) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym11_1 : run_sym11 ((2 ^ 53 - 1), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym11_2 : run_sym11 (((2 ^ 54 - 1) <<< 53), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym11_3 : run_sym11 (((2 ^ 53 - 1) <<< 107), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym11_4 : run_sym11 (((2 ^ 54 - 1) <<< 160), 0) = false := by decide +kernel
lemma case_s11_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior_s11, ImpT [f] 0 13 1) : ImpT [gate_s11] 0 13 1 := by
  have hc : ∀ p ∈ masks_sym11, run_sym11 p = false := by
    intro p hp
    simp only [masks_sym11, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact split_sym11_0
    · exact split_sym11_1
    · exact split_sym11_2
    · exact split_sym11_3
    · exact split_sym11_4
  exact ty_imp_shards_t accBounds_extraFive owned_s11_bounds shape_s11_checked masks_sym11_full hc h0 (by simpa using hF)
def gate_s12 : Gt := (true, 0, 2)
def prior_s12 : List Gt := [(false, 0, 2), (false, 3, 5), (false, 0, 5), (false, 0, 6), (false, 5, 6), (true, 1, 2), (true, 3, 4), (false, 1, 4), (false, 0, 1), (false, 4, 5), (false, 0, 3), (false, 2, 5), (false, 1, 2), (false, 3, 4), (false, 1, 6), (false, 4, 6), (false, 2, 3), (false, 0, 4), (false, 1, 5), (false, 1, 3), (false, 2, 4), (false, 2, 6), (false, 3, 6), (true, 0, 1), (true, 4, 5), (true, 0, 3), (true, 2, 5), (true, 1, 6), (true, 4, 6), (true, 2, 3)]
def rows_s12 : List ((Nat × Nat) × List Nat) := ownRows acc_extraFive [120, 114, 122, 90, 16400, 112, 16448, 16392, 16386, 4112, 1088, 88, 82, 16384, 26, 72, 80, 24, 18, 64, 16]
def owns_s12 : List Nat := rows_s12.map (fun r => r.1.1)
def codes_s12 : List Nat := [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def owned_s12_checked : ownCheck topC gate_s12 acc_extraFive [] rows_s12 = true := by decide +kernel
lemma owned_s12_bounds : ∀ x ∈ acc_extraFive, x.1 ∈ owns_s12 → Imp [gate_s12] x.1 x.2 := by
  have h := ownCheck_imp topC_ok (e := gate_s12) (by decide) accBounds_extraFive own0 owned_s12_checked
  simpa only [owns_s12, List.append_nil] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def shape_s12_checked : okTy prior_s12 acc_extraFive 12 prior_s12.length gate_s12 owns_s12 codes_s12 (234, ((((((0x2088080 <<< 64) + 0x009020010a004106) <<< 64) + 0x00a00000002104c8) <<< 64) + 0x00a2000140000128)) [List.range 13] = true := by decide +kernel
def masks_sym12 : List (Nat × Nat) := [(0, 1), ((2 ^ 53 - 1), 0), (((2 ^ 6 - 1) <<< 53), 0), (((2 ^ 7 - 1) <<< 59), 0), (((2 ^ 14 - 1) <<< 66), 0), (((2 ^ 27 - 1) <<< 80), 0), (((2 ^ 26 - 1) <<< 107), 0), (((2 ^ 13 - 1) <<< 133), 0), (((2 ^ 14 - 1) <<< 146), 0), (((2 ^ 54 - 1) <<< 160), 0)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def masks_sym12_full : mFull masks_sym12 = true := by decide +kernel
noncomputable def run_sym12 (p : Nat × Nat) : Bool :=
  chkT topC [gate_s12] (tabE gate_s12 owns_s12 (pick acc_extraFive codes_s12)) (234, ((((((0x2088080 <<< 64) + 0x009020010a004106) <<< 64) + 0x00a00000002104c8) <<< 64) + 0x00a2000140000128)) 0 12 [1] p.1 p.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym12_0 : run_sym12 (0, 1) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym12_1 : run_sym12 ((2 ^ 53 - 1), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym12_2 : run_sym12 (((2 ^ 6 - 1) <<< 53), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym12_3 : run_sym12 (((2 ^ 7 - 1) <<< 59), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym12_4 : run_sym12 (((2 ^ 14 - 1) <<< 66), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym12_5 : run_sym12 (((2 ^ 27 - 1) <<< 80), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym12_6 : run_sym12 (((2 ^ 26 - 1) <<< 107), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym12_7 : run_sym12 (((2 ^ 13 - 1) <<< 133), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym12_8 : run_sym12 (((2 ^ 14 - 1) <<< 146), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym12_9 : run_sym12 (((2 ^ 54 - 1) <<< 160), 0) = false := by decide +kernel
lemma case_s12_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior_s12, ImpT [f] 0 13 1) : ImpT [gate_s12] 0 13 1 := by
  have hc : ∀ p ∈ masks_sym12, run_sym12 p = false := by
    intro p hp
    simp only [masks_sym12, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact split_sym12_0
    · exact split_sym12_1
    · exact split_sym12_2
    · exact split_sym12_3
    · exact split_sym12_4
    · exact split_sym12_5
    · exact split_sym12_6
    · exact split_sym12_7
    · exact split_sym12_8
    · exact split_sym12_9
  exact ty_imp_shards_t accBounds_extraFive owned_s12_bounds shape_s12_checked masks_sym12_full hc h0 (by simpa using hF)
def gate_s13 : Gt := (true, 0, 4)
def prior_s13 : List Gt := [(false, 0, 2), (false, 3, 5), (false, 0, 5), (false, 0, 6), (false, 5, 6), (true, 1, 2), (true, 3, 4), (false, 1, 4), (false, 0, 1), (false, 4, 5), (false, 0, 3), (false, 2, 5), (false, 1, 2), (false, 3, 4), (false, 1, 6), (false, 4, 6), (false, 2, 3), (false, 0, 4), (false, 1, 5), (false, 1, 3), (false, 2, 4), (false, 2, 6), (false, 3, 6), (true, 0, 1), (true, 4, 5), (true, 0, 3), (true, 2, 5), (true, 1, 6), (true, 4, 6), (true, 2, 3), (true, 0, 2), (true, 3, 5)]
def rows_s13 : List ((Nat × Nat) × List Nat) := ownRows acc_extraFive [102, 110, 108, 78, 46, 32770, 16388, 76, 32800, 32776, 32772, 16448, 16392, 16386, 4100, 1088, 1028, 100, 70, 44, 38, 1064, 32768, 16384, 42, 14, 1056, 1032, 68, 12, 1024, 40, 36, 34, 10, 6, 32, 4, 2]
def owns_s13 : List Nat := rows_s13.map (fun r => r.1.1)
def codes_s13 : List Nat := [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def owned_s13_checked : ownCheck topC gate_s13 acc_extraFive [] rows_s13 = true := by decide +kernel
lemma owned_s13_bounds : ∀ x ∈ acc_extraFive, x.1 ∈ owns_s13 → Imp [gate_s13] x.1 x.2 := by
  have h := ownCheck_imp topC_ok (e := gate_s13) (by decide) accBounds_extraFive own0 owned_s13_checked
  simpa only [owns_s13, List.append_nil] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def shape_s13_checked : okTy prior_s13 acc_extraFive 12 prior_s13.length gate_s13 owns_s13 codes_s13 (201, ((((((0x4 <<< 64) + 0x002200000500c600) <<< 64) + 0x0801402000890801) <<< 64) + 0x1800054500080412)) [List.range 13] = true := by decide +kernel
def masks_sym13 : List (Nat × Nat) := [(0, 1), ((2 ^ 53 - 1), 0), (((2 ^ 54 - 1) <<< 53), 0), (((2 ^ 53 - 1) <<< 107), 0), (((2 ^ 54 - 1) <<< 160), 0)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def masks_sym13_full : mFull masks_sym13 = true := by decide +kernel
noncomputable def run_sym13 (p : Nat × Nat) : Bool :=
  chkT topC [gate_s13] (tabE gate_s13 owns_s13 (pick acc_extraFive codes_s13)) (201, ((((((0x4 <<< 64) + 0x002200000500c600) <<< 64) + 0x0801402000890801) <<< 64) + 0x1800054500080412)) 0 12 [1] p.1 p.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym13_0 : run_sym13 (0, 1) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym13_1 : run_sym13 ((2 ^ 53 - 1), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym13_2 : run_sym13 (((2 ^ 54 - 1) <<< 53), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym13_3 : run_sym13 (((2 ^ 53 - 1) <<< 107), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym13_4 : run_sym13 (((2 ^ 54 - 1) <<< 160), 0) = false := by decide +kernel
lemma case_s13_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior_s13, ImpT [f] 0 13 1) : ImpT [gate_s13] 0 13 1 := by
  have hc : ∀ p ∈ masks_sym13, run_sym13 p = false := by
    intro p hp
    simp only [masks_sym13, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact split_sym13_0
    · exact split_sym13_1
    · exact split_sym13_2
    · exact split_sym13_3
    · exact split_sym13_4
  exact ty_imp_shards_t accBounds_extraFive owned_s13_bounds shape_s13_checked masks_sym13_full hc h0 (by simpa using hF)
def gate_s14 : Gt := (true, 0, 5)
def prior_s14 : List Gt := [(false, 0, 2), (false, 3, 5), (false, 0, 5), (false, 0, 6), (false, 5, 6), (true, 1, 2), (true, 3, 4), (false, 1, 4), (false, 0, 1), (false, 4, 5), (false, 0, 3), (false, 2, 5), (false, 1, 2), (false, 3, 4), (false, 1, 6), (false, 4, 6), (false, 2, 3), (false, 0, 4), (false, 1, 5), (false, 1, 3), (false, 2, 4), (false, 2, 6), (false, 3, 6), (true, 0, 1), (true, 4, 5), (true, 0, 3), (true, 2, 5), (true, 1, 6), (true, 4, 6), (true, 2, 3), (true, 0, 2), (true, 3, 5), (true, 0, 4), (true, 1, 5)]
def rows_s14 : List ((Nat × Nat) × List Nat) := ownRows acc_extraFive [94, 92, 90, 86, 78, 76, 8256, 8200, 4112, 4100, 2056, 2050, 1088, 1028, 88, 82, 70, 8198, 4162, 2128, 1048, 84, 74, 26, 22, 8196, 8194, 4160, 4098, 2112, 2064, 1040, 1032, 72, 68, 8192, 4096, 2048, 1024, 80, 66, 24, 20, 18, 10, 6, 64, 16, 2]
def owns_s14 : List Nat := rows_s14.map (fun r => r.1.1)
def codes_s14 : List Nat := [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def owned_s14_checked : ownCheck topC gate_s14 acc_extraFive [] rows_s14 = true := by decide +kernel
lemma owned_s14_bounds : ∀ x ∈ acc_extraFive, x.1 ∈ owns_s14 → Imp [gate_s14] x.1 x.2 := by
  have h := ownCheck_imp topC_ok (e := gate_s14) (by decide) accBounds_extraFive own0 owned_s14_checked
  simpa only [owns_s14, List.append_nil] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def shape_s14_checked : okTy prior_s14 acc_extraFive 12 prior_s14.length gate_s14 owns_s14 codes_s14 (215, ((((((0x604030 <<< 64) + 0x0000c00a04200190) <<< 64) + 0x0409004000200a88) <<< 64) + 0x4001084148080004)) [List.range 13] = true := by decide +kernel
def masks_sym14 : List (Nat × Nat) := [(0, 1), ((2 ^ 53 - 1), 0), (((2 ^ 54 - 1) <<< 53), 0), (((2 ^ 26 - 1) <<< 107), 0), (((2 ^ 13 - 1) <<< 133), 0), (((2 ^ 7 - 1) <<< 146), 0), (((2 ^ 7 - 1) <<< 153), 0), (((2 ^ 54 - 1) <<< 160), 0)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def masks_sym14_full : mFull masks_sym14 = true := by decide +kernel
noncomputable def run_sym14 (p : Nat × Nat) : Bool :=
  chkT topC [gate_s14] (tabE gate_s14 owns_s14 (pick acc_extraFive codes_s14)) (215, ((((((0x604030 <<< 64) + 0x0000c00a04200190) <<< 64) + 0x0409004000200a88) <<< 64) + 0x4001084148080004)) 0 12 [1] p.1 p.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym14_0 : run_sym14 (0, 1) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym14_1 : run_sym14 ((2 ^ 53 - 1), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym14_2 : run_sym14 (((2 ^ 54 - 1) <<< 53), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym14_3 : run_sym14 (((2 ^ 26 - 1) <<< 107), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym14_4 : run_sym14 (((2 ^ 13 - 1) <<< 133), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym14_5 : run_sym14 (((2 ^ 7 - 1) <<< 146), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym14_6 : run_sym14 (((2 ^ 7 - 1) <<< 153), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym14_7 : run_sym14 (((2 ^ 54 - 1) <<< 160), 0) = false := by decide +kernel
lemma case_s14_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior_s14, ImpT [f] 0 13 1) : ImpT [gate_s14] 0 13 1 := by
  have hc : ∀ p ∈ masks_sym14, run_sym14 p = false := by
    intro p hp
    simp only [masks_sym14, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact split_sym14_0
    · exact split_sym14_1
    · exact split_sym14_2
    · exact split_sym14_3
    · exact split_sym14_4
    · exact split_sym14_5
    · exact split_sym14_6
    · exact split_sym14_7
  exact ty_imp_shards_t accBounds_extraFive owned_s14_bounds shape_s14_checked masks_sym14_full hc h0 (by simpa using hF)
def gate_s15 : Gt := (true, 0, 6)
def prior_s15 : List Gt := [(false, 0, 2), (false, 3, 5), (false, 0, 5), (false, 0, 6), (false, 5, 6), (true, 1, 2), (true, 3, 4), (false, 1, 4), (false, 0, 1), (false, 4, 5), (false, 0, 3), (false, 2, 5), (false, 1, 2), (false, 3, 4), (false, 1, 6), (false, 4, 6), (false, 2, 3), (false, 0, 4), (false, 1, 5), (false, 1, 3), (false, 2, 4), (false, 2, 6), (false, 3, 6), (true, 0, 1), (true, 4, 5), (true, 0, 3), (true, 2, 5), (true, 1, 6), (true, 4, 6), (true, 2, 3), (true, 0, 2), (true, 3, 5), (true, 0, 4), (true, 1, 5), (true, 0, 5)]
def rows_s15 : List ((Nat × Nat) × List Nat) := ownRows acc_extraFive [60, 62, 54, 46, 8224, 8200, 4112, 4100, 1028, 52, 44, 38, 8198, 4130, 42, 22, 8196, 8194, 4128, 4098, 12, 8192, 4096, 40, 36, 34, 20, 6, 32, 4]
def owns_s15 : List Nat := rows_s15.map (fun r => r.1.1)
def codes_s15 : List Nat := [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def owned_s15_checked : ownCheck topC gate_s15 acc_extraFive [] rows_s15 = true := by decide +kernel
lemma owned_s15_bounds : ∀ x ∈ acc_extraFive, x.1 ∈ owns_s15 → Imp [gate_s15] x.1 x.2 := by
  have h := ownCheck_imp topC_ok (e := gate_s15) (by decide) accBounds_extraFive own0 owned_s15_checked
  simpa only [owns_s15, List.append_nil] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def shape_s15_checked : okTy prior_s15 acc_extraFive 12 prior_s15.length gate_s15 owns_s15 codes_s15 (181, ((((0x8081150200008 <<< 64) + 0x6110100250100020) <<< 64) + 0x800a850a84020360)) [List.range 13] = true := by decide +kernel
def masks_sym15 : List (Nat × Nat) := [(0, 1), ((2 ^ 53 - 1), 0), (((2 ^ 54 - 1) <<< 53), 0), (((2 ^ 53 - 1) <<< 107), 0), (((2 ^ 54 - 1) <<< 160), 0)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def masks_sym15_full : mFull masks_sym15 = true := by decide +kernel
noncomputable def run_sym15 (p : Nat × Nat) : Bool :=
  chkT topC [gate_s15] (tabE gate_s15 owns_s15 (pick acc_extraFive codes_s15)) (181, ((((0x8081150200008 <<< 64) + 0x6110100250100020) <<< 64) + 0x800a850a84020360)) 0 12 [1] p.1 p.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym15_0 : run_sym15 (0, 1) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym15_1 : run_sym15 ((2 ^ 53 - 1), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym15_2 : run_sym15 (((2 ^ 54 - 1) <<< 53), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym15_3 : run_sym15 (((2 ^ 53 - 1) <<< 107), 0) = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym15_4 : run_sym15 (((2 ^ 54 - 1) <<< 160), 0) = false := by decide +kernel
lemma case_s15_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior_s15, ImpT [f] 0 13 1) : ImpT [gate_s15] 0 13 1 := by
  have hc : ∀ p ∈ masks_sym15, run_sym15 p = false := by
    intro p hp
    simp only [masks_sym15, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact split_sym15_0
    · exact split_sym15_1
    · exact split_sym15_2
    · exact split_sym15_3
    · exact split_sym15_4
  exact ty_imp_shards_t accBounds_extraFive owned_s15_bounds shape_s15_checked masks_sym15_full hc h0 (by simpa using hF)
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
def masks_sym16 : List (Nat × Nat) := [((2 ^ 214 - 1), 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def masks_sym16_full : mFull masks_sym16 = true := by decide +kernel
noncomputable def run_sym16 (p : Nat × Nat) : Bool :=
  chkT topC [gate_s16] (tabE gate_s16 owns_s16 (pick acc_extraFive codes_s16)) (159, ((((0x40308a80 <<< 64) + 0x600aa45033080008) <<< 64) + 0x0500040022c20001)) 0 12 [1] p.1 p.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym16_0 : run_sym16 ((2 ^ 214 - 1), 1) = false := by decide +kernel
lemma case_s16_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior_s16, ImpT [f] 0 13 1) : ImpT [gate_s16] 0 13 1 := by
  have hc : ∀ p ∈ masks_sym16, run_sym16 p = false := by
    intro p hp
    simp only [masks_sym16, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    · exact split_sym16_0
  exact ty_imp_shards_t accBounds_extraFive owned_s16_bounds shape_s16_checked masks_sym16_full hc h0 (by simpa using hF)
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
def masks_sym17 : List (Nat × Nat) := [((2 ^ 214 - 1), 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def masks_sym17_full : mFull masks_sym17 = true := by decide +kernel
noncomputable def run_sym17 (p : Nat × Nat) : Bool :=
  chkT topC [gate_s17] (tabE gate_s17 owns_s17 (pick acc_extraFive codes_s17)) (229, ((((((0x140a002010 <<< 64) + 0x0040104101169400) <<< 64) + 0x2c42001044082000) <<< 64) + 0x004000080000a4d0)) 0 12 [1] p.1 p.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym17_0 : run_sym17 ((2 ^ 214 - 1), 1) = false := by decide +kernel
lemma case_s17_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior_s17, ImpT [f] 0 13 1) : ImpT [gate_s17] 0 13 1 := by
  have hc : ∀ p ∈ masks_sym17, run_sym17 p = false := by
    intro p hp
    simp only [masks_sym17, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    · exact split_sym17_0
  exact ty_imp_shards_t accBounds_extraFive owned_s17_bounds shape_s17_checked masks_sym17_full hc h0 (by simpa using hF)
def gate_s18 : Gt := (true, 2, 6)
def prior_s18 : List Gt := [(false, 0, 2), (false, 3, 5), (false, 0, 5), (false, 0, 6), (false, 5, 6), (true, 1, 2), (true, 3, 4), (false, 1, 4), (false, 0, 1), (false, 4, 5), (false, 0, 3), (false, 2, 5), (false, 1, 2), (false, 3, 4), (false, 1, 6), (false, 4, 6), (false, 2, 3), (false, 0, 4), (false, 1, 5), (false, 1, 3), (false, 2, 4), (false, 2, 6), (false, 3, 6), (true, 0, 1), (true, 4, 5), (true, 0, 3), (true, 2, 5), (true, 1, 6), (true, 4, 6), (true, 2, 3), (true, 0, 2), (true, 3, 5), (true, 0, 4), (true, 1, 5), (true, 0, 5), (true, 0, 6), (true, 5, 6), (true, 1, 3), (true, 2, 4), (true, 1, 4)]
def rows_s18 : List ((Nat × Nat) × List Nat) := ownRows acc_extraFive [57, 59, 51, 43, 27, 16400, 16392, 16386, 16385, 8224, 8200, 4112, 4097, 1025, 49, 41, 35, 25, 11, 8195, 4130, 16384, 42, 26, 19, 8194, 8193, 4128, 4098, 8192, 4096, 40, 34, 33, 24, 18, 17, 10, 9, 3, 32, 16, 2, 1]
def owns_s18 : List Nat := rows_s18.map (fun r => r.1.1)
def codes_s18 : List Nat := [32, 16, 8, 4, 2, 1, 64, 8192, 4096, 2048, 1024, 96, 80, 66, 65, 48, 40, 36, 34, 33, 24, 20, 18, 17, 10, 9, 6, 5, 3, 8196, 8194, 8193, 4160, 4128, 4098, 2112, 2064, 2049, 1056, 1040, 1032, 72, 68, 12]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma owned_s18_checked : ownCheck topC gate_s18 acc_extraFive [] rows_s18 = true := by decide +kernel
lemma owned_s18_bounds : ∀ x ∈ acc_extraFive, x.1 ∈ owns_s18 → Imp [gate_s18] x.1 x.2 := by
  have h := ownCheck_imp topC_ok (e := gate_s18) (by decide) accBounds_extraFive own0 owned_s18_checked
  simpa only [owns_s18, List.append_nil] using h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma shape_s18_checked : okTy prior_s18 acc_extraFive 12 prior_s18.length gate_s18 owns_s18 codes_s18 (159, ((((0x40308a80 <<< 64) + 0x620aa45033080408) <<< 64) + 0x0500040032c20001)) [List.range 13] = true := by decide +kernel
def masks_sym18 : List (Nat × Nat) := [((2 ^ 214 - 1), 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def masks_sym18_full : mFull masks_sym18 = true := by decide +kernel
noncomputable def run_sym18 (p : Nat × Nat) : Bool :=
  chkT topC [gate_s18] (tabE gate_s18 owns_s18 (pick acc_extraFive codes_s18)) (159, ((((0x40308a80 <<< 64) + 0x620aa45033080408) <<< 64) + 0x0500040032c20001)) 0 12 [1] p.1 p.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def split_sym18_0 : run_sym18 ((2 ^ 214 - 1), 1) = false := by decide +kernel
lemma case_s18_bound (h0 : Imp [] 0 13) (hF : ∀ f ∈ prior_s18, ImpT [f] 0 13 1) : ImpT [gate_s18] 0 13 1 := by
  have hc : ∀ p ∈ masks_sym18, run_sym18 p = false := by
    intro p hp
    simp only [masks_sym18, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    · exact split_sym18_0
  exact ty_imp_shards_t accBounds_extraFive owned_s18_bounds shape_s18_checked masks_sym18_full hc h0 (by simpa using hF)
end PEqualNP.Outside.L_meta_10760
