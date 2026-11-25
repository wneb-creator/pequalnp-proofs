import ReductionsIR

namespace PEqualNP.Outside.Pilot64Bridge

open PEqualNP.Library.LRAT
open PEqualNP.Outside.Pilot64KernelControl

set_option maxRecDepth 100000
set_option maxHeartbeats 0


def chunk0 : List (List Nat) := [[2], [6, 8, 10, 12], [7, 9], [23, 7], [23, 9], [22, 6, 8], [22, 11], [25, 22], [25, 11], [24, 23, 10], [24, 13], [27, 24], [27, 13], [26, 25, 12], [14, 16, 18, 20], [15, 17], [29, 15], [29, 17], [28, 14, 16], [28, 19], [31, 28], [31, 19], [30, 29, 18], [30, 21], [33, 30], [33, 21], [32, 31, 20], [7, 15], [9, 28], [11, 30], [13, 32], [36, 38, 40, 42, 44], [37, 39], [57, 37], [57, 39], [56, 36, 38], [56, 41], [59, 56], [59, 41], [58, 57, 40], [58, 43], [61, 58], [61, 43], [60, 59, 42], [60, 45], [63, 60], [63, 45], [62, 61, 44], [46, 48, 50, 52, 54], [47, 49], [65, 47], [65, 49], [64, 46, 48], [64, 51], [67, 64], [67, 51], [66, 65, 50], [66, 53], [69, 66], [69, 53], [68, 67, 52], [68, 55], [71, 68], [71, 55], [70, 69, 54], [37, 47], [39, 64], [41, 66], [43, 68], [45, 70], [74, 76, 78, 80, 82, 84], [75, 77], [99, 75], [99, 77], [98, 74, 76], [98, 79], [101, 98], [101, 79], [100, 99, 78], [100, 81], [103, 100], [103, 81], [102, 101, 80], [102, 83], [105, 102], [105, 83], [104, 103, 82], [104, 85], [107, 104], [107, 85], [106, 105, 84], [86, 88, 90, 92, 94, 96], [87, 89], [109, 87], [109, 89], [108, 86, 88], [108, 91], [111, 108], [111, 91], [110, 109, 90]]
theorem satChunk0 (c : Candidate) (hv : valid c)
    (hr : ∀ r : Fin 16, output c r = target r)
    (hl : derivativeLeft c = false) (hd : derivativeRight c = false) :
    ∀ cl ∈ chunk0, ClauseSat (assignment c) cl := by
  rcases hv with ⟨h0, h1, h2, h3, h4⟩
  have hc0 : ClauseSat (assignment c) [2] := by
    simp [ClauseSat, litVal, assignment_1]
  have hc1 : ClauseSat (assignment c) [6,8,10,12] := by
    have hb := c.a0.isLt
    simp [ClauseSat, litVal, assignment_3, assignment_4, assignment_5, assignment_6, v3, v4, v5, v6]
    omega
  have hc2 : ClauseSat (assignment c) [7,9] := by
    simp [ClauseSat, litVal, assignment_3, assignment_4, v3, v4]
    all_goals omega
  have hc3 : ClauseSat (assignment c) [23,7] := by
    cases ha0 : v3 c <;> cases ha1 : v4 c <;> simp [ClauseSat, litVal, assignment_3, assignment_11, v11, ha0, ha1]
  have hc4 : ClauseSat (assignment c) [23,9] := by
    cases ha0 : v3 c <;> cases ha1 : v4 c <;> simp [ClauseSat, litVal, assignment_4, assignment_11, v11, ha0, ha1]
  have hc5 : ClauseSat (assignment c) [22,6,8] := by
    cases ha0 : v3 c <;> cases ha1 : v4 c <;> simp [ClauseSat, litVal, assignment_3, assignment_4, assignment_11, v11, ha0, ha1]
  have hc6 : ClauseSat (assignment c) [22,11] := by
    simp [ClauseSat, litVal, assignment_5, assignment_11, v3, v4, v5, v11]
    all_goals omega
  have hc7 : ClauseSat (assignment c) [25,22] := by
    cases ha0 : v5 c <;> cases ha1 : v11 c <;> simp [ClauseSat, litVal, assignment_11, assignment_12, v12, ha0, ha1]
  have hc8 : ClauseSat (assignment c) [25,11] := by
    cases ha0 : v5 c <;> cases ha1 : v11 c <;> simp [ClauseSat, litVal, assignment_5, assignment_12, v12, ha0, ha1]
  have hc9 : ClauseSat (assignment c) [24,23,10] := by
    cases ha0 : v5 c <;> cases ha1 : v11 c <;> simp [ClauseSat, litVal, assignment_5, assignment_11, assignment_12, v12, ha0, ha1]
  have hc10 : ClauseSat (assignment c) [24,13] := by
    simp [ClauseSat, litVal, assignment_6, assignment_12, v3, v4, v5, v6, v11, v12]
    all_goals omega
  have hc11 : ClauseSat (assignment c) [27,24] := by
    cases ha0 : v6 c <;> cases ha1 : v12 c <;> simp [ClauseSat, litVal, assignment_12, assignment_13, v13, ha0, ha1]
  have hc12 : ClauseSat (assignment c) [27,13] := by
    cases ha0 : v6 c <;> cases ha1 : v12 c <;> simp [ClauseSat, litVal, assignment_6, assignment_13, v13, ha0, ha1]
  have hc13 : ClauseSat (assignment c) [26,25,12] := by
    cases ha0 : v6 c <;> cases ha1 : v12 c <;> simp [ClauseSat, litVal, assignment_6, assignment_12, assignment_13, v13, ha0, ha1]
  have hc14 : ClauseSat (assignment c) [14,16,18,20] := by
    have hb := c.b0.isLt
    simp [ClauseSat, litVal, assignment_7, assignment_8, assignment_9, assignment_10, v7, v8, v9, v10]
    omega
  have hc15 : ClauseSat (assignment c) [15,17] := by
    simp [ClauseSat, litVal, assignment_7, assignment_8, v7, v8]
    all_goals omega
  have hc16 : ClauseSat (assignment c) [29,15] := by
    cases ha0 : v7 c <;> cases ha1 : v8 c <;> simp [ClauseSat, litVal, assignment_7, assignment_14, v14, ha0, ha1]
  have hc17 : ClauseSat (assignment c) [29,17] := by
    cases ha0 : v7 c <;> cases ha1 : v8 c <;> simp [ClauseSat, litVal, assignment_8, assignment_14, v14, ha0, ha1]
  have hc18 : ClauseSat (assignment c) [28,14,16] := by
    cases ha0 : v7 c <;> cases ha1 : v8 c <;> simp [ClauseSat, litVal, assignment_7, assignment_8, assignment_14, v14, ha0, ha1]
  have hc19 : ClauseSat (assignment c) [28,19] := by
    simp [ClauseSat, litVal, assignment_9, assignment_14, v7, v8, v9, v14]
    all_goals omega
  have hc20 : ClauseSat (assignment c) [31,28] := by
    cases ha0 : v9 c <;> cases ha1 : v14 c <;> simp [ClauseSat, litVal, assignment_14, assignment_15, v15, ha0, ha1]
  have hc21 : ClauseSat (assignment c) [31,19] := by
    cases ha0 : v9 c <;> cases ha1 : v14 c <;> simp [ClauseSat, litVal, assignment_9, assignment_15, v15, ha0, ha1]
  have hc22 : ClauseSat (assignment c) [30,29,18] := by
    cases ha0 : v9 c <;> cases ha1 : v14 c <;> simp [ClauseSat, litVal, assignment_9, assignment_14, assignment_15, v15, ha0, ha1]
  have hc23 : ClauseSat (assignment c) [30,21] := by
    simp [ClauseSat, litVal, assignment_10, assignment_15, v7, v8, v9, v10, v14, v15]
    all_goals omega
  have hc24 : ClauseSat (assignment c) [33,30] := by
    cases ha0 : v10 c <;> cases ha1 : v15 c <;> simp [ClauseSat, litVal, assignment_15, assignment_16, v16, ha0, ha1]
  have hc25 : ClauseSat (assignment c) [33,21] := by
    cases ha0 : v10 c <;> cases ha1 : v15 c <;> simp [ClauseSat, litVal, assignment_10, assignment_16, v16, ha0, ha1]
  have hc26 : ClauseSat (assignment c) [32,31,20] := by
    cases ha0 : v10 c <;> cases ha1 : v15 c <;> simp [ClauseSat, litVal, assignment_10, assignment_15, assignment_16, v16, ha0, ha1]
  have hc27 : ClauseSat (assignment c) [7,15] := by
    simp [ClauseSat, litVal, assignment_3, assignment_7, v3, v7]
    all_goals omega
  have hc28 : ClauseSat (assignment c) [9,28] := by
    simp [ClauseSat, litVal, assignment_4, assignment_14, v4, v7, v8, v14]
    all_goals omega
  have hc29 : ClauseSat (assignment c) [11,30] := by
    simp [ClauseSat, litVal, assignment_5, assignment_15, v5, v7, v8, v9, v14, v15]
    all_goals omega
  have hc30 : ClauseSat (assignment c) [13,32] := by
    simp [ClauseSat, litVal, assignment_6, assignment_16, v6, v7, v8, v9, v10, v14, v15, v16]
    all_goals omega
  have hc31 : ClauseSat (assignment c) [36,38,40,42,44] := by
    have hb := c.a1.isLt
    simp [ClauseSat, litVal, assignment_18, assignment_19, assignment_20, assignment_21, assignment_22, v18, v19, v20, v21, v22]
    omega
  have hc32 : ClauseSat (assignment c) [37,39] := by
    simp [ClauseSat, litVal, assignment_18, assignment_19, v18, v19]
    all_goals omega
  have hc33 : ClauseSat (assignment c) [57,37] := by
    cases ha0 : v18 c <;> cases ha1 : v19 c <;> simp [ClauseSat, litVal, assignment_18, assignment_28, v28, ha0, ha1]
  have hc34 : ClauseSat (assignment c) [57,39] := by
    cases ha0 : v18 c <;> cases ha1 : v19 c <;> simp [ClauseSat, litVal, assignment_19, assignment_28, v28, ha0, ha1]
  have hc35 : ClauseSat (assignment c) [56,36,38] := by
    cases ha0 : v18 c <;> cases ha1 : v19 c <;> simp [ClauseSat, litVal, assignment_18, assignment_19, assignment_28, v28, ha0, ha1]
  have hc36 : ClauseSat (assignment c) [56,41] := by
    simp [ClauseSat, litVal, assignment_20, assignment_28, v18, v19, v20, v28]
    all_goals omega
  have hc37 : ClauseSat (assignment c) [59,56] := by
    cases ha0 : v20 c <;> cases ha1 : v28 c <;> simp [ClauseSat, litVal, assignment_28, assignment_29, v29, ha0, ha1]
  have hc38 : ClauseSat (assignment c) [59,41] := by
    cases ha0 : v20 c <;> cases ha1 : v28 c <;> simp [ClauseSat, litVal, assignment_20, assignment_29, v29, ha0, ha1]
  have hc39 : ClauseSat (assignment c) [58,57,40] := by
    cases ha0 : v20 c <;> cases ha1 : v28 c <;> simp [ClauseSat, litVal, assignment_20, assignment_28, assignment_29, v29, ha0, ha1]
  have hc40 : ClauseSat (assignment c) [58,43] := by
    simp [ClauseSat, litVal, assignment_21, assignment_29, v18, v19, v20, v21, v28, v29]
    all_goals omega
  have hc41 : ClauseSat (assignment c) [61,58] := by
    cases ha0 : v21 c <;> cases ha1 : v29 c <;> simp [ClauseSat, litVal, assignment_29, assignment_30, v30, ha0, ha1]
  have hc42 : ClauseSat (assignment c) [61,43] := by
    cases ha0 : v21 c <;> cases ha1 : v29 c <;> simp [ClauseSat, litVal, assignment_21, assignment_30, v30, ha0, ha1]
  have hc43 : ClauseSat (assignment c) [60,59,42] := by
    cases ha0 : v21 c <;> cases ha1 : v29 c <;> simp [ClauseSat, litVal, assignment_21, assignment_29, assignment_30, v30, ha0, ha1]
  have hc44 : ClauseSat (assignment c) [60,45] := by
    simp [ClauseSat, litVal, assignment_22, assignment_30, v18, v19, v20, v21, v22, v28, v29, v30]
    all_goals omega
  have hc45 : ClauseSat (assignment c) [63,60] := by
    cases ha0 : v22 c <;> cases ha1 : v30 c <;> simp [ClauseSat, litVal, assignment_30, assignment_31, v31, ha0, ha1]
  have hc46 : ClauseSat (assignment c) [63,45] := by
    cases ha0 : v22 c <;> cases ha1 : v30 c <;> simp [ClauseSat, litVal, assignment_22, assignment_31, v31, ha0, ha1]
  have hc47 : ClauseSat (assignment c) [62,61,44] := by
    cases ha0 : v22 c <;> cases ha1 : v30 c <;> simp [ClauseSat, litVal, assignment_22, assignment_30, assignment_31, v31, ha0, ha1]
  have hc48 : ClauseSat (assignment c) [46,48,50,52,54] := by
    have hb := c.b1.isLt
    simp [ClauseSat, litVal, assignment_23, assignment_24, assignment_25, assignment_26, assignment_27, v23, v24, v25, v26, v27]
    omega
  have hc49 : ClauseSat (assignment c) [47,49] := by
    simp [ClauseSat, litVal, assignment_23, assignment_24, v23, v24]
    all_goals omega
  have hc50 : ClauseSat (assignment c) [65,47] := by
    cases ha0 : v23 c <;> cases ha1 : v24 c <;> simp [ClauseSat, litVal, assignment_23, assignment_32, v32, ha0, ha1]
  have hc51 : ClauseSat (assignment c) [65,49] := by
    cases ha0 : v23 c <;> cases ha1 : v24 c <;> simp [ClauseSat, litVal, assignment_24, assignment_32, v32, ha0, ha1]
  have hc52 : ClauseSat (assignment c) [64,46,48] := by
    cases ha0 : v23 c <;> cases ha1 : v24 c <;> simp [ClauseSat, litVal, assignment_23, assignment_24, assignment_32, v32, ha0, ha1]
  have hc53 : ClauseSat (assignment c) [64,51] := by
    simp [ClauseSat, litVal, assignment_25, assignment_32, v23, v24, v25, v32]
    all_goals omega
  have hc54 : ClauseSat (assignment c) [67,64] := by
    cases ha0 : v25 c <;> cases ha1 : v32 c <;> simp [ClauseSat, litVal, assignment_32, assignment_33, v33, ha0, ha1]
  have hc55 : ClauseSat (assignment c) [67,51] := by
    cases ha0 : v25 c <;> cases ha1 : v32 c <;> simp [ClauseSat, litVal, assignment_25, assignment_33, v33, ha0, ha1]
  have hc56 : ClauseSat (assignment c) [66,65,50] := by
    cases ha0 : v25 c <;> cases ha1 : v32 c <;> simp [ClauseSat, litVal, assignment_25, assignment_32, assignment_33, v33, ha0, ha1]
  have hc57 : ClauseSat (assignment c) [66,53] := by
    simp [ClauseSat, litVal, assignment_26, assignment_33, v23, v24, v25, v26, v32, v33]
    all_goals omega
  have hc58 : ClauseSat (assignment c) [69,66] := by
    cases ha0 : v26 c <;> cases ha1 : v33 c <;> simp [ClauseSat, litVal, assignment_33, assignment_34, v34, ha0, ha1]
  have hc59 : ClauseSat (assignment c) [69,53] := by
    cases ha0 : v26 c <;> cases ha1 : v33 c <;> simp [ClauseSat, litVal, assignment_26, assignment_34, v34, ha0, ha1]
  have hc60 : ClauseSat (assignment c) [68,67,52] := by
    cases ha0 : v26 c <;> cases ha1 : v33 c <;> simp [ClauseSat, litVal, assignment_26, assignment_33, assignment_34, v34, ha0, ha1]
  have hc61 : ClauseSat (assignment c) [68,55] := by
    simp [ClauseSat, litVal, assignment_27, assignment_34, v23, v24, v25, v26, v27, v32, v33, v34]
    all_goals omega
  have hc62 : ClauseSat (assignment c) [71,68] := by
    cases ha0 : v27 c <;> cases ha1 : v34 c <;> simp [ClauseSat, litVal, assignment_34, assignment_35, v35, ha0, ha1]
  have hc63 : ClauseSat (assignment c) [71,55] := by
    cases ha0 : v27 c <;> cases ha1 : v34 c <;> simp [ClauseSat, litVal, assignment_27, assignment_35, v35, ha0, ha1]
  have hc64 : ClauseSat (assignment c) [70,69,54] := by
    cases ha0 : v27 c <;> cases ha1 : v34 c <;> simp [ClauseSat, litVal, assignment_27, assignment_34, assignment_35, v35, ha0, ha1]
  have hc65 : ClauseSat (assignment c) [37,47] := by
    simp [ClauseSat, litVal, assignment_18, assignment_23, v18, v23]
    all_goals omega
  have hc66 : ClauseSat (assignment c) [39,64] := by
    simp [ClauseSat, litVal, assignment_19, assignment_32, v19, v23, v24, v32]
    all_goals omega
  have hc67 : ClauseSat (assignment c) [41,66] := by
    simp [ClauseSat, litVal, assignment_20, assignment_33, v20, v23, v24, v25, v32, v33]
    all_goals omega
  have hc68 : ClauseSat (assignment c) [43,68] := by
    simp [ClauseSat, litVal, assignment_21, assignment_34, v21, v23, v24, v25, v26, v32, v33, v34]
    all_goals omega
  have hc69 : ClauseSat (assignment c) [45,70] := by
    simp [ClauseSat, litVal, assignment_22, assignment_35, v22, v23, v24, v25, v26, v27, v32, v33, v34, v35]
    all_goals omega
  have hc70 : ClauseSat (assignment c) [74,76,78,80,82,84] := by
    have hb := c.a2.isLt
    simp [ClauseSat, litVal, assignment_37, assignment_38, assignment_39, assignment_40, assignment_41, assignment_42, v37, v38, v39, v40, v41, v42]
    omega
  have hc71 : ClauseSat (assignment c) [75,77] := by
    simp [ClauseSat, litVal, assignment_37, assignment_38, v37, v38]
    all_goals omega
  have hc72 : ClauseSat (assignment c) [99,75] := by
    cases ha0 : v37 c <;> cases ha1 : v38 c <;> simp [ClauseSat, litVal, assignment_37, assignment_49, v49, ha0, ha1]
  have hc73 : ClauseSat (assignment c) [99,77] := by
    cases ha0 : v37 c <;> cases ha1 : v38 c <;> simp [ClauseSat, litVal, assignment_38, assignment_49, v49, ha0, ha1]
  have hc74 : ClauseSat (assignment c) [98,74,76] := by
    cases ha0 : v37 c <;> cases ha1 : v38 c <;> simp [ClauseSat, litVal, assignment_37, assignment_38, assignment_49, v49, ha0, ha1]
  have hc75 : ClauseSat (assignment c) [98,79] := by
    simp [ClauseSat, litVal, assignment_39, assignment_49, v37, v38, v39, v49]
    all_goals omega
  have hc76 : ClauseSat (assignment c) [101,98] := by
    cases ha0 : v39 c <;> cases ha1 : v49 c <;> simp [ClauseSat, litVal, assignment_49, assignment_50, v50, ha0, ha1]
  have hc77 : ClauseSat (assignment c) [101,79] := by
    cases ha0 : v39 c <;> cases ha1 : v49 c <;> simp [ClauseSat, litVal, assignment_39, assignment_50, v50, ha0, ha1]
  have hc78 : ClauseSat (assignment c) [100,99,78] := by
    cases ha0 : v39 c <;> cases ha1 : v49 c <;> simp [ClauseSat, litVal, assignment_39, assignment_49, assignment_50, v50, ha0, ha1]
  have hc79 : ClauseSat (assignment c) [100,81] := by
    simp [ClauseSat, litVal, assignment_40, assignment_50, v37, v38, v39, v40, v49, v50]
    all_goals omega
  have hc80 : ClauseSat (assignment c) [103,100] := by
    cases ha0 : v40 c <;> cases ha1 : v50 c <;> simp [ClauseSat, litVal, assignment_50, assignment_51, v51, ha0, ha1]
  have hc81 : ClauseSat (assignment c) [103,81] := by
    cases ha0 : v40 c <;> cases ha1 : v50 c <;> simp [ClauseSat, litVal, assignment_40, assignment_51, v51, ha0, ha1]
  have hc82 : ClauseSat (assignment c) [102,101,80] := by
    cases ha0 : v40 c <;> cases ha1 : v50 c <;> simp [ClauseSat, litVal, assignment_40, assignment_50, assignment_51, v51, ha0, ha1]
  have hc83 : ClauseSat (assignment c) [102,83] := by
    simp [ClauseSat, litVal, assignment_41, assignment_51, v37, v38, v39, v40, v41, v49, v50, v51]
    all_goals omega
  have hc84 : ClauseSat (assignment c) [105,102] := by
    cases ha0 : v41 c <;> cases ha1 : v51 c <;> simp [ClauseSat, litVal, assignment_51, assignment_52, v52, ha0, ha1]
  have hc85 : ClauseSat (assignment c) [105,83] := by
    cases ha0 : v41 c <;> cases ha1 : v51 c <;> simp [ClauseSat, litVal, assignment_41, assignment_52, v52, ha0, ha1]
  have hc86 : ClauseSat (assignment c) [104,103,82] := by
    cases ha0 : v41 c <;> cases ha1 : v51 c <;> simp [ClauseSat, litVal, assignment_41, assignment_51, assignment_52, v52, ha0, ha1]
  have hc87 : ClauseSat (assignment c) [104,85] := by
    simp [ClauseSat, litVal, assignment_42, assignment_52, v37, v38, v39, v40, v41, v42, v49, v50, v51, v52]
    all_goals omega
  have hc88 : ClauseSat (assignment c) [107,104] := by
    cases ha0 : v42 c <;> cases ha1 : v52 c <;> simp [ClauseSat, litVal, assignment_52, assignment_53, v53, ha0, ha1]
  have hc89 : ClauseSat (assignment c) [107,85] := by
    cases ha0 : v42 c <;> cases ha1 : v52 c <;> simp [ClauseSat, litVal, assignment_42, assignment_53, v53, ha0, ha1]
  have hc90 : ClauseSat (assignment c) [106,105,84] := by
    cases ha0 : v42 c <;> cases ha1 : v52 c <;> simp [ClauseSat, litVal, assignment_42, assignment_52, assignment_53, v53, ha0, ha1]
  have hc91 : ClauseSat (assignment c) [86,88,90,92,94,96] := by
    have hb := c.b2.isLt
    simp [ClauseSat, litVal, assignment_43, assignment_44, assignment_45, assignment_46, assignment_47, assignment_48, v43, v44, v45, v46, v47, v48]
    omega
  have hc92 : ClauseSat (assignment c) [87,89] := by
    simp [ClauseSat, litVal, assignment_43, assignment_44, v43, v44]
    all_goals omega
  have hc93 : ClauseSat (assignment c) [109,87] := by
    cases ha0 : v43 c <;> cases ha1 : v44 c <;> simp [ClauseSat, litVal, assignment_43, assignment_54, v54, ha0, ha1]
  have hc94 : ClauseSat (assignment c) [109,89] := by
    cases ha0 : v43 c <;> cases ha1 : v44 c <;> simp [ClauseSat, litVal, assignment_44, assignment_54, v54, ha0, ha1]
  have hc95 : ClauseSat (assignment c) [108,86,88] := by
    cases ha0 : v43 c <;> cases ha1 : v44 c <;> simp [ClauseSat, litVal, assignment_43, assignment_44, assignment_54, v54, ha0, ha1]
  have hc96 : ClauseSat (assignment c) [108,91] := by
    simp [ClauseSat, litVal, assignment_45, assignment_54, v43, v44, v45, v54]
    all_goals omega
  have hc97 : ClauseSat (assignment c) [111,108] := by
    cases ha0 : v45 c <;> cases ha1 : v54 c <;> simp [ClauseSat, litVal, assignment_54, assignment_55, v55, ha0, ha1]
  have hc98 : ClauseSat (assignment c) [111,91] := by
    cases ha0 : v45 c <;> cases ha1 : v54 c <;> simp [ClauseSat, litVal, assignment_45, assignment_55, v55, ha0, ha1]
  have hc99 : ClauseSat (assignment c) [110,109,90] := by
    cases ha0 : v45 c <;> cases ha1 : v54 c <;> simp [ClauseSat, litVal, assignment_45, assignment_54, assignment_55, v55, ha0, ha1]
  simp only [chunk0, List.forall_mem_cons]
  exact ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25, hc26, hc27, hc28, hc29, hc30, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38, hc39, hc40, hc41, hc42, hc43, hc44, hc45, hc46, hc47, hc48, hc49, hc50, hc51, hc52, hc53, hc54, hc55, hc56, hc57, hc58, hc59, hc60, hc61, hc62, hc63, hc64, hc65, hc66, hc67, hc68, hc69, hc70, hc71, hc72, hc73, hc74, hc75, hc76, hc77, hc78, hc79, hc80, hc81, hc82, hc83, hc84, hc85, hc86, hc87, hc88, hc89, hc90, hc91, hc92, hc93, hc94, hc95, hc96, hc97, hc98, hc99, by simp⟩
#check satChunk0

def chunk1 : List (List Nat) := [[110, 93], [113, 110], [113, 93], [112, 111, 92], [112, 95], [115, 112], [115, 95], [114, 113, 94], [114, 97], [117, 114], [117, 97], [116, 115, 96], [75, 87], [77, 108], [79, 110], [81, 112], [83, 114], [85, 116], [120, 122, 124, 126, 128, 130, 132], [121, 123], [149, 121], [149, 123], [148, 120, 122], [148, 125], [151, 148], [151, 125], [150, 149, 124], [150, 127], [153, 150], [153, 127], [152, 151, 126], [152, 129], [155, 152], [155, 129], [154, 153, 128], [154, 131], [157, 154], [157, 131], [156, 155, 130], [156, 133], [159, 156], [159, 133], [158, 157, 132], [134, 136, 138, 140, 142, 144, 146], [135, 137], [161, 135], [161, 137], [160, 134, 136], [160, 139], [163, 160], [163, 139], [162, 161, 138], [162, 141], [165, 162], [165, 141], [164, 163, 140], [164, 143], [167, 164], [167, 143], [166, 165, 142], [166, 145], [169, 166], [169, 145], [168, 167, 144], [168, 147], [171, 168], [171, 147], [170, 169, 146], [121, 135], [123, 160], [125, 162], [127, 164], [129, 166], [131, 168], [133, 170], [174, 176, 178, 180, 182, 184, 186, 188], [175, 177], [207, 175], [207, 177], [206, 174, 176], [206, 179], [209, 206], [209, 179], [208, 207, 178], [208, 181], [211, 208], [211, 181], [210, 209, 180], [210, 183], [213, 210], [213, 183], [212, 211, 182], [212, 185], [215, 212], [215, 185], [214, 213, 184], [214, 187], [217, 214], [217, 187], [216, 215, 186]]
theorem satChunk1 (c : Candidate) (hv : valid c)
    (hr : ∀ r : Fin 16, output c r = target r)
    (hl : derivativeLeft c = false) (hd : derivativeRight c = false) :
    ∀ cl ∈ chunk1, ClauseSat (assignment c) cl := by
  rcases hv with ⟨h0, h1, h2, h3, h4⟩
  have hc100 : ClauseSat (assignment c) [110,93] := by
    simp [ClauseSat, litVal, assignment_46, assignment_55, v43, v44, v45, v46, v54, v55]
    all_goals omega
  have hc101 : ClauseSat (assignment c) [113,110] := by
    cases ha0 : v46 c <;> cases ha1 : v55 c <;> simp [ClauseSat, litVal, assignment_55, assignment_56, v56, ha0, ha1]
  have hc102 : ClauseSat (assignment c) [113,93] := by
    cases ha0 : v46 c <;> cases ha1 : v55 c <;> simp [ClauseSat, litVal, assignment_46, assignment_56, v56, ha0, ha1]
  have hc103 : ClauseSat (assignment c) [112,111,92] := by
    cases ha0 : v46 c <;> cases ha1 : v55 c <;> simp [ClauseSat, litVal, assignment_46, assignment_55, assignment_56, v56, ha0, ha1]
  have hc104 : ClauseSat (assignment c) [112,95] := by
    simp [ClauseSat, litVal, assignment_47, assignment_56, v43, v44, v45, v46, v47, v54, v55, v56]
    all_goals omega
  have hc105 : ClauseSat (assignment c) [115,112] := by
    cases ha0 : v47 c <;> cases ha1 : v56 c <;> simp [ClauseSat, litVal, assignment_56, assignment_57, v57, ha0, ha1]
  have hc106 : ClauseSat (assignment c) [115,95] := by
    cases ha0 : v47 c <;> cases ha1 : v56 c <;> simp [ClauseSat, litVal, assignment_47, assignment_57, v57, ha0, ha1]
  have hc107 : ClauseSat (assignment c) [114,113,94] := by
    cases ha0 : v47 c <;> cases ha1 : v56 c <;> simp [ClauseSat, litVal, assignment_47, assignment_56, assignment_57, v57, ha0, ha1]
  have hc108 : ClauseSat (assignment c) [114,97] := by
    simp [ClauseSat, litVal, assignment_48, assignment_57, v43, v44, v45, v46, v47, v48, v54, v55, v56, v57]
    all_goals omega
  have hc109 : ClauseSat (assignment c) [117,114] := by
    cases ha0 : v48 c <;> cases ha1 : v57 c <;> simp [ClauseSat, litVal, assignment_57, assignment_58, v58, ha0, ha1]
  have hc110 : ClauseSat (assignment c) [117,97] := by
    cases ha0 : v48 c <;> cases ha1 : v57 c <;> simp [ClauseSat, litVal, assignment_48, assignment_58, v58, ha0, ha1]
  have hc111 : ClauseSat (assignment c) [116,115,96] := by
    cases ha0 : v48 c <;> cases ha1 : v57 c <;> simp [ClauseSat, litVal, assignment_48, assignment_57, assignment_58, v58, ha0, ha1]
  have hc112 : ClauseSat (assignment c) [75,87] := by
    simp [ClauseSat, litVal, assignment_37, assignment_43, v37, v43]
    all_goals omega
  have hc113 : ClauseSat (assignment c) [77,108] := by
    simp [ClauseSat, litVal, assignment_38, assignment_54, v38, v43, v44, v54]
    all_goals omega
  have hc114 : ClauseSat (assignment c) [79,110] := by
    simp [ClauseSat, litVal, assignment_39, assignment_55, v39, v43, v44, v45, v54, v55]
    all_goals omega
  have hc115 : ClauseSat (assignment c) [81,112] := by
    simp [ClauseSat, litVal, assignment_40, assignment_56, v40, v43, v44, v45, v46, v54, v55, v56]
    all_goals omega
  have hc116 : ClauseSat (assignment c) [83,114] := by
    simp [ClauseSat, litVal, assignment_41, assignment_57, v41, v43, v44, v45, v46, v47, v54, v55, v56, v57]
    all_goals omega
  have hc117 : ClauseSat (assignment c) [85,116] := by
    simp [ClauseSat, litVal, assignment_42, assignment_58, v42, v43, v44, v45, v46, v47, v48, v54, v55, v56, v57, v58]
    all_goals omega
  have hc118 : ClauseSat (assignment c) [120,122,124,126,128,130,132] := by
    have hb := c.a3.isLt
    simp [ClauseSat, litVal, assignment_60, assignment_61, assignment_62, assignment_63, assignment_64, assignment_65, assignment_66, v60, v61, v62, v63, v64, v65, v66]
    omega
  have hc119 : ClauseSat (assignment c) [121,123] := by
    simp [ClauseSat, litVal, assignment_60, assignment_61, v60, v61]
    all_goals omega
  have hc120 : ClauseSat (assignment c) [149,121] := by
    cases ha0 : v60 c <;> cases ha1 : v61 c <;> simp [ClauseSat, litVal, assignment_60, assignment_74, v74, ha0, ha1]
  have hc121 : ClauseSat (assignment c) [149,123] := by
    cases ha0 : v60 c <;> cases ha1 : v61 c <;> simp [ClauseSat, litVal, assignment_61, assignment_74, v74, ha0, ha1]
  have hc122 : ClauseSat (assignment c) [148,120,122] := by
    cases ha0 : v60 c <;> cases ha1 : v61 c <;> simp [ClauseSat, litVal, assignment_60, assignment_61, assignment_74, v74, ha0, ha1]
  have hc123 : ClauseSat (assignment c) [148,125] := by
    simp [ClauseSat, litVal, assignment_62, assignment_74, v60, v61, v62, v74]
    all_goals omega
  have hc124 : ClauseSat (assignment c) [151,148] := by
    cases ha0 : v62 c <;> cases ha1 : v74 c <;> simp [ClauseSat, litVal, assignment_74, assignment_75, v75, ha0, ha1]
  have hc125 : ClauseSat (assignment c) [151,125] := by
    cases ha0 : v62 c <;> cases ha1 : v74 c <;> simp [ClauseSat, litVal, assignment_62, assignment_75, v75, ha0, ha1]
  have hc126 : ClauseSat (assignment c) [150,149,124] := by
    cases ha0 : v62 c <;> cases ha1 : v74 c <;> simp [ClauseSat, litVal, assignment_62, assignment_74, assignment_75, v75, ha0, ha1]
  have hc127 : ClauseSat (assignment c) [150,127] := by
    simp [ClauseSat, litVal, assignment_63, assignment_75, v60, v61, v62, v63, v74, v75]
    all_goals omega
  have hc128 : ClauseSat (assignment c) [153,150] := by
    cases ha0 : v63 c <;> cases ha1 : v75 c <;> simp [ClauseSat, litVal, assignment_75, assignment_76, v76, ha0, ha1]
  have hc129 : ClauseSat (assignment c) [153,127] := by
    cases ha0 : v63 c <;> cases ha1 : v75 c <;> simp [ClauseSat, litVal, assignment_63, assignment_76, v76, ha0, ha1]
  have hc130 : ClauseSat (assignment c) [152,151,126] := by
    cases ha0 : v63 c <;> cases ha1 : v75 c <;> simp [ClauseSat, litVal, assignment_63, assignment_75, assignment_76, v76, ha0, ha1]
  have hc131 : ClauseSat (assignment c) [152,129] := by
    simp [ClauseSat, litVal, assignment_64, assignment_76, v60, v61, v62, v63, v64, v74, v75, v76]
    all_goals omega
  have hc132 : ClauseSat (assignment c) [155,152] := by
    cases ha0 : v64 c <;> cases ha1 : v76 c <;> simp [ClauseSat, litVal, assignment_76, assignment_77, v77, ha0, ha1]
  have hc133 : ClauseSat (assignment c) [155,129] := by
    cases ha0 : v64 c <;> cases ha1 : v76 c <;> simp [ClauseSat, litVal, assignment_64, assignment_77, v77, ha0, ha1]
  have hc134 : ClauseSat (assignment c) [154,153,128] := by
    cases ha0 : v64 c <;> cases ha1 : v76 c <;> simp [ClauseSat, litVal, assignment_64, assignment_76, assignment_77, v77, ha0, ha1]
  have hc135 : ClauseSat (assignment c) [154,131] := by
    simp [ClauseSat, litVal, assignment_65, assignment_77, v60, v61, v62, v63, v64, v65, v74, v75, v76, v77]
    all_goals omega
  have hc136 : ClauseSat (assignment c) [157,154] := by
    cases ha0 : v65 c <;> cases ha1 : v77 c <;> simp [ClauseSat, litVal, assignment_77, assignment_78, v78, ha0, ha1]
  have hc137 : ClauseSat (assignment c) [157,131] := by
    cases ha0 : v65 c <;> cases ha1 : v77 c <;> simp [ClauseSat, litVal, assignment_65, assignment_78, v78, ha0, ha1]
  have hc138 : ClauseSat (assignment c) [156,155,130] := by
    cases ha0 : v65 c <;> cases ha1 : v77 c <;> simp [ClauseSat, litVal, assignment_65, assignment_77, assignment_78, v78, ha0, ha1]
  have hc139 : ClauseSat (assignment c) [156,133] := by
    simp [ClauseSat, litVal, assignment_66, assignment_78, v60, v61, v62, v63, v64, v65, v66, v74, v75, v76, v77, v78]
    all_goals omega
  have hc140 : ClauseSat (assignment c) [159,156] := by
    cases ha0 : v66 c <;> cases ha1 : v78 c <;> simp [ClauseSat, litVal, assignment_78, assignment_79, v79, ha0, ha1]
  have hc141 : ClauseSat (assignment c) [159,133] := by
    cases ha0 : v66 c <;> cases ha1 : v78 c <;> simp [ClauseSat, litVal, assignment_66, assignment_79, v79, ha0, ha1]
  have hc142 : ClauseSat (assignment c) [158,157,132] := by
    cases ha0 : v66 c <;> cases ha1 : v78 c <;> simp [ClauseSat, litVal, assignment_66, assignment_78, assignment_79, v79, ha0, ha1]
  have hc143 : ClauseSat (assignment c) [134,136,138,140,142,144,146] := by
    have hb := c.b3.isLt
    simp [ClauseSat, litVal, assignment_67, assignment_68, assignment_69, assignment_70, assignment_71, assignment_72, assignment_73, v67, v68, v69, v70, v71, v72, v73]
    omega
  have hc144 : ClauseSat (assignment c) [135,137] := by
    simp [ClauseSat, litVal, assignment_67, assignment_68, v67, v68]
    all_goals omega
  have hc145 : ClauseSat (assignment c) [161,135] := by
    cases ha0 : v67 c <;> cases ha1 : v68 c <;> simp [ClauseSat, litVal, assignment_67, assignment_80, v80, ha0, ha1]
  have hc146 : ClauseSat (assignment c) [161,137] := by
    cases ha0 : v67 c <;> cases ha1 : v68 c <;> simp [ClauseSat, litVal, assignment_68, assignment_80, v80, ha0, ha1]
  have hc147 : ClauseSat (assignment c) [160,134,136] := by
    cases ha0 : v67 c <;> cases ha1 : v68 c <;> simp [ClauseSat, litVal, assignment_67, assignment_68, assignment_80, v80, ha0, ha1]
  have hc148 : ClauseSat (assignment c) [160,139] := by
    simp [ClauseSat, litVal, assignment_69, assignment_80, v67, v68, v69, v80]
    all_goals omega
  have hc149 : ClauseSat (assignment c) [163,160] := by
    cases ha0 : v69 c <;> cases ha1 : v80 c <;> simp [ClauseSat, litVal, assignment_80, assignment_81, v81, ha0, ha1]
  have hc150 : ClauseSat (assignment c) [163,139] := by
    cases ha0 : v69 c <;> cases ha1 : v80 c <;> simp [ClauseSat, litVal, assignment_69, assignment_81, v81, ha0, ha1]
  have hc151 : ClauseSat (assignment c) [162,161,138] := by
    cases ha0 : v69 c <;> cases ha1 : v80 c <;> simp [ClauseSat, litVal, assignment_69, assignment_80, assignment_81, v81, ha0, ha1]
  have hc152 : ClauseSat (assignment c) [162,141] := by
    simp [ClauseSat, litVal, assignment_70, assignment_81, v67, v68, v69, v70, v80, v81]
    all_goals omega
  have hc153 : ClauseSat (assignment c) [165,162] := by
    cases ha0 : v70 c <;> cases ha1 : v81 c <;> simp [ClauseSat, litVal, assignment_81, assignment_82, v82, ha0, ha1]
  have hc154 : ClauseSat (assignment c) [165,141] := by
    cases ha0 : v70 c <;> cases ha1 : v81 c <;> simp [ClauseSat, litVal, assignment_70, assignment_82, v82, ha0, ha1]
  have hc155 : ClauseSat (assignment c) [164,163,140] := by
    cases ha0 : v70 c <;> cases ha1 : v81 c <;> simp [ClauseSat, litVal, assignment_70, assignment_81, assignment_82, v82, ha0, ha1]
  have hc156 : ClauseSat (assignment c) [164,143] := by
    simp [ClauseSat, litVal, assignment_71, assignment_82, v67, v68, v69, v70, v71, v80, v81, v82]
    all_goals omega
  have hc157 : ClauseSat (assignment c) [167,164] := by
    cases ha0 : v71 c <;> cases ha1 : v82 c <;> simp [ClauseSat, litVal, assignment_82, assignment_83, v83, ha0, ha1]
  have hc158 : ClauseSat (assignment c) [167,143] := by
    cases ha0 : v71 c <;> cases ha1 : v82 c <;> simp [ClauseSat, litVal, assignment_71, assignment_83, v83, ha0, ha1]
  have hc159 : ClauseSat (assignment c) [166,165,142] := by
    cases ha0 : v71 c <;> cases ha1 : v82 c <;> simp [ClauseSat, litVal, assignment_71, assignment_82, assignment_83, v83, ha0, ha1]
  have hc160 : ClauseSat (assignment c) [166,145] := by
    simp [ClauseSat, litVal, assignment_72, assignment_83, v67, v68, v69, v70, v71, v72, v80, v81, v82, v83]
    all_goals omega
  have hc161 : ClauseSat (assignment c) [169,166] := by
    cases ha0 : v72 c <;> cases ha1 : v83 c <;> simp [ClauseSat, litVal, assignment_83, assignment_84, v84, ha0, ha1]
  have hc162 : ClauseSat (assignment c) [169,145] := by
    cases ha0 : v72 c <;> cases ha1 : v83 c <;> simp [ClauseSat, litVal, assignment_72, assignment_84, v84, ha0, ha1]
  have hc163 : ClauseSat (assignment c) [168,167,144] := by
    cases ha0 : v72 c <;> cases ha1 : v83 c <;> simp [ClauseSat, litVal, assignment_72, assignment_83, assignment_84, v84, ha0, ha1]
  have hc164 : ClauseSat (assignment c) [168,147] := by
    simp [ClauseSat, litVal, assignment_73, assignment_84, v67, v68, v69, v70, v71, v72, v73, v80, v81, v82, v83, v84]
    all_goals omega
  have hc165 : ClauseSat (assignment c) [171,168] := by
    cases ha0 : v73 c <;> cases ha1 : v84 c <;> simp [ClauseSat, litVal, assignment_84, assignment_85, v85, ha0, ha1]
  have hc166 : ClauseSat (assignment c) [171,147] := by
    cases ha0 : v73 c <;> cases ha1 : v84 c <;> simp [ClauseSat, litVal, assignment_73, assignment_85, v85, ha0, ha1]
  have hc167 : ClauseSat (assignment c) [170,169,146] := by
    cases ha0 : v73 c <;> cases ha1 : v84 c <;> simp [ClauseSat, litVal, assignment_73, assignment_84, assignment_85, v85, ha0, ha1]
  have hc168 : ClauseSat (assignment c) [121,135] := by
    simp [ClauseSat, litVal, assignment_60, assignment_67, v60, v67]
    all_goals omega
  have hc169 : ClauseSat (assignment c) [123,160] := by
    simp [ClauseSat, litVal, assignment_61, assignment_80, v61, v67, v68, v80]
    all_goals omega
  have hc170 : ClauseSat (assignment c) [125,162] := by
    simp [ClauseSat, litVal, assignment_62, assignment_81, v62, v67, v68, v69, v80, v81]
    all_goals omega
  have hc171 : ClauseSat (assignment c) [127,164] := by
    simp [ClauseSat, litVal, assignment_63, assignment_82, v63, v67, v68, v69, v70, v80, v81, v82]
    all_goals omega
  have hc172 : ClauseSat (assignment c) [129,166] := by
    simp [ClauseSat, litVal, assignment_64, assignment_83, v64, v67, v68, v69, v70, v71, v80, v81, v82, v83]
    all_goals omega
  have hc173 : ClauseSat (assignment c) [131,168] := by
    simp [ClauseSat, litVal, assignment_65, assignment_84, v65, v67, v68, v69, v70, v71, v72, v80, v81, v82, v83, v84]
    all_goals omega
  have hc174 : ClauseSat (assignment c) [133,170] := by
    simp [ClauseSat, litVal, assignment_66, assignment_85, v66, v67, v68, v69, v70, v71, v72, v73, v80, v81, v82, v83, v84, v85]
    all_goals omega
  have hc175 : ClauseSat (assignment c) [174,176,178,180,182,184,186,188] := by
    have hb := c.a4.isLt
    simp [ClauseSat, litVal, assignment_87, assignment_88, assignment_89, assignment_90, assignment_91, assignment_92, assignment_93, assignment_94, v87, v88, v89, v90, v91, v92, v93, v94]
    omega
  have hc176 : ClauseSat (assignment c) [175,177] := by
    simp [ClauseSat, litVal, assignment_87, assignment_88, v87, v88]
    all_goals omega
  have hc177 : ClauseSat (assignment c) [207,175] := by
    cases ha0 : v87 c <;> cases ha1 : v88 c <;> simp [ClauseSat, litVal, assignment_87, assignment_103, v103, ha0, ha1]
  have hc178 : ClauseSat (assignment c) [207,177] := by
    cases ha0 : v87 c <;> cases ha1 : v88 c <;> simp [ClauseSat, litVal, assignment_88, assignment_103, v103, ha0, ha1]
  have hc179 : ClauseSat (assignment c) [206,174,176] := by
    cases ha0 : v87 c <;> cases ha1 : v88 c <;> simp [ClauseSat, litVal, assignment_87, assignment_88, assignment_103, v103, ha0, ha1]
  have hc180 : ClauseSat (assignment c) [206,179] := by
    simp [ClauseSat, litVal, assignment_89, assignment_103, v87, v88, v89, v103]
    all_goals omega
  have hc181 : ClauseSat (assignment c) [209,206] := by
    cases ha0 : v89 c <;> cases ha1 : v103 c <;> simp [ClauseSat, litVal, assignment_103, assignment_104, v104, ha0, ha1]
  have hc182 : ClauseSat (assignment c) [209,179] := by
    cases ha0 : v89 c <;> cases ha1 : v103 c <;> simp [ClauseSat, litVal, assignment_89, assignment_104, v104, ha0, ha1]
  have hc183 : ClauseSat (assignment c) [208,207,178] := by
    cases ha0 : v89 c <;> cases ha1 : v103 c <;> simp [ClauseSat, litVal, assignment_89, assignment_103, assignment_104, v104, ha0, ha1]
  have hc184 : ClauseSat (assignment c) [208,181] := by
    simp [ClauseSat, litVal, assignment_90, assignment_104, v87, v88, v89, v90, v103, v104]
    all_goals omega
  have hc185 : ClauseSat (assignment c) [211,208] := by
    cases ha0 : v90 c <;> cases ha1 : v104 c <;> simp [ClauseSat, litVal, assignment_104, assignment_105, v105, ha0, ha1]
  have hc186 : ClauseSat (assignment c) [211,181] := by
    cases ha0 : v90 c <;> cases ha1 : v104 c <;> simp [ClauseSat, litVal, assignment_90, assignment_105, v105, ha0, ha1]
  have hc187 : ClauseSat (assignment c) [210,209,180] := by
    cases ha0 : v90 c <;> cases ha1 : v104 c <;> simp [ClauseSat, litVal, assignment_90, assignment_104, assignment_105, v105, ha0, ha1]
  have hc188 : ClauseSat (assignment c) [210,183] := by
    simp [ClauseSat, litVal, assignment_91, assignment_105, v87, v88, v89, v90, v91, v103, v104, v105]
    all_goals omega
  have hc189 : ClauseSat (assignment c) [213,210] := by
    cases ha0 : v91 c <;> cases ha1 : v105 c <;> simp [ClauseSat, litVal, assignment_105, assignment_106, v106, ha0, ha1]
  have hc190 : ClauseSat (assignment c) [213,183] := by
    cases ha0 : v91 c <;> cases ha1 : v105 c <;> simp [ClauseSat, litVal, assignment_91, assignment_106, v106, ha0, ha1]
  have hc191 : ClauseSat (assignment c) [212,211,182] := by
    cases ha0 : v91 c <;> cases ha1 : v105 c <;> simp [ClauseSat, litVal, assignment_91, assignment_105, assignment_106, v106, ha0, ha1]
  have hc192 : ClauseSat (assignment c) [212,185] := by
    simp [ClauseSat, litVal, assignment_92, assignment_106, v87, v88, v89, v90, v91, v92, v103, v104, v105, v106]
    all_goals omega
  have hc193 : ClauseSat (assignment c) [215,212] := by
    cases ha0 : v92 c <;> cases ha1 : v106 c <;> simp [ClauseSat, litVal, assignment_106, assignment_107, v107, ha0, ha1]
  have hc194 : ClauseSat (assignment c) [215,185] := by
    cases ha0 : v92 c <;> cases ha1 : v106 c <;> simp [ClauseSat, litVal, assignment_92, assignment_107, v107, ha0, ha1]
  have hc195 : ClauseSat (assignment c) [214,213,184] := by
    cases ha0 : v92 c <;> cases ha1 : v106 c <;> simp [ClauseSat, litVal, assignment_92, assignment_106, assignment_107, v107, ha0, ha1]
  have hc196 : ClauseSat (assignment c) [214,187] := by
    simp [ClauseSat, litVal, assignment_93, assignment_107, v87, v88, v89, v90, v91, v92, v93, v103, v104, v105, v106, v107]
    all_goals omega
  have hc197 : ClauseSat (assignment c) [217,214] := by
    cases ha0 : v93 c <;> cases ha1 : v107 c <;> simp [ClauseSat, litVal, assignment_107, assignment_108, v108, ha0, ha1]
  have hc198 : ClauseSat (assignment c) [217,187] := by
    cases ha0 : v93 c <;> cases ha1 : v107 c <;> simp [ClauseSat, litVal, assignment_93, assignment_108, v108, ha0, ha1]
  have hc199 : ClauseSat (assignment c) [216,215,186] := by
    cases ha0 : v93 c <;> cases ha1 : v107 c <;> simp [ClauseSat, litVal, assignment_93, assignment_107, assignment_108, v108, ha0, ha1]
  simp only [chunk1, List.forall_mem_cons]
  exact ⟨hc100, hc101, hc102, hc103, hc104, hc105, hc106, hc107, hc108, hc109, hc110, hc111, hc112, hc113, hc114, hc115, hc116, hc117, hc118, hc119, hc120, hc121, hc122, hc123, hc124, hc125, hc126, hc127, hc128, hc129, hc130, hc131, hc132, hc133, hc134, hc135, hc136, hc137, hc138, hc139, hc140, hc141, hc142, hc143, hc144, hc145, hc146, hc147, hc148, hc149, hc150, hc151, hc152, hc153, hc154, hc155, hc156, hc157, hc158, hc159, hc160, hc161, hc162, hc163, hc164, hc165, hc166, hc167, hc168, hc169, hc170, hc171, hc172, hc173, hc174, hc175, hc176, hc177, hc178, hc179, hc180, hc181, hc182, hc183, hc184, hc185, hc186, hc187, hc188, hc189, hc190, hc191, hc192, hc193, hc194, hc195, hc196, hc197, hc198, hc199, by simp⟩
#check satChunk1

def chunk2 : List (List Nat) := [[216, 189], [219, 216], [219, 189], [218, 217, 188], [190, 192, 194, 196, 198, 200, 202, 204], [191, 193], [221, 191], [221, 193], [220, 190, 192], [220, 195], [223, 220], [223, 195], [222, 221, 194], [222, 197], [225, 222], [225, 197], [224, 223, 196], [224, 199], [227, 224], [227, 199], [226, 225, 198], [226, 201], [229, 226], [229, 201], [228, 227, 200], [228, 203], [231, 228], [231, 203], [230, 229, 202], [230, 205], [233, 230], [233, 205], [232, 231, 204], [175, 191], [177, 220], [179, 222], [181, 224], [183, 226], [185, 228], [187, 230], [189, 232], [5, 235], [5, 235], [4, 235], [37, 237], [39, 237], [41, 237], [43, 237], [45, 237, 234], [45, 236, 235], [47, 239], [49, 239], [51, 239], [53, 239], [55, 239, 234], [55, 238, 235], [35, 241, 236], [35, 241, 238], [35, 240, 237, 239], [34, 240, 237], [34, 240, 239], [34, 241, 236, 238], [75, 243], [77, 243], [79, 243], [81, 243], [83, 243, 234], [83, 242, 235], [85, 243, 240], [85, 242, 241], [87, 245], [89, 245], [91, 245], [93, 245], [95, 245, 234], [95, 244, 235], [97, 245, 240], [97, 244, 241], [73, 247, 242], [73, 247, 244], [73, 246, 243, 245], [72, 246, 243], [72, 246, 245], [72, 247, 242, 244], [121, 249], [123, 249], [125, 249], [127, 249], [129, 249, 234], [129, 248, 235], [131, 249, 240], [131, 248, 241], [133, 249, 246], [133, 248, 247], [135, 251], [137, 251], [139, 251], [141, 251], [143, 251, 234], [143, 250, 235]]
theorem satChunk2 (c : Candidate) (hv : valid c)
    (hr : ∀ r : Fin 16, output c r = target r)
    (hl : derivativeLeft c = false) (hd : derivativeRight c = false) :
    ∀ cl ∈ chunk2, ClauseSat (assignment c) cl := by
  rcases hv with ⟨h0, h1, h2, h3, h4⟩
  have hc200 : ClauseSat (assignment c) [216,189] := by
    simp [ClauseSat, litVal, assignment_94, assignment_108, v87, v88, v89, v90, v91, v92, v93, v94, v103, v104, v105, v106, v107, v108]
    all_goals omega
  have hc201 : ClauseSat (assignment c) [219,216] := by
    cases ha0 : v94 c <;> cases ha1 : v108 c <;> simp [ClauseSat, litVal, assignment_108, assignment_109, v109, ha0, ha1]
  have hc202 : ClauseSat (assignment c) [219,189] := by
    cases ha0 : v94 c <;> cases ha1 : v108 c <;> simp [ClauseSat, litVal, assignment_94, assignment_109, v109, ha0, ha1]
  have hc203 : ClauseSat (assignment c) [218,217,188] := by
    cases ha0 : v94 c <;> cases ha1 : v108 c <;> simp [ClauseSat, litVal, assignment_94, assignment_108, assignment_109, v109, ha0, ha1]
  have hc204 : ClauseSat (assignment c) [190,192,194,196,198,200,202,204] := by
    have hb := c.b4.isLt
    simp [ClauseSat, litVal, assignment_95, assignment_96, assignment_97, assignment_98, assignment_99, assignment_100, assignment_101, assignment_102, v95, v96, v97, v98, v99, v100, v101, v102]
    omega
  have hc205 : ClauseSat (assignment c) [191,193] := by
    simp [ClauseSat, litVal, assignment_95, assignment_96, v95, v96]
    all_goals omega
  have hc206 : ClauseSat (assignment c) [221,191] := by
    cases ha0 : v95 c <;> cases ha1 : v96 c <;> simp [ClauseSat, litVal, assignment_95, assignment_110, v110, ha0, ha1]
  have hc207 : ClauseSat (assignment c) [221,193] := by
    cases ha0 : v95 c <;> cases ha1 : v96 c <;> simp [ClauseSat, litVal, assignment_96, assignment_110, v110, ha0, ha1]
  have hc208 : ClauseSat (assignment c) [220,190,192] := by
    cases ha0 : v95 c <;> cases ha1 : v96 c <;> simp [ClauseSat, litVal, assignment_95, assignment_96, assignment_110, v110, ha0, ha1]
  have hc209 : ClauseSat (assignment c) [220,195] := by
    simp [ClauseSat, litVal, assignment_97, assignment_110, v95, v96, v97, v110]
    all_goals omega
  have hc210 : ClauseSat (assignment c) [223,220] := by
    cases ha0 : v97 c <;> cases ha1 : v110 c <;> simp [ClauseSat, litVal, assignment_110, assignment_111, v111, ha0, ha1]
  have hc211 : ClauseSat (assignment c) [223,195] := by
    cases ha0 : v97 c <;> cases ha1 : v110 c <;> simp [ClauseSat, litVal, assignment_97, assignment_111, v111, ha0, ha1]
  have hc212 : ClauseSat (assignment c) [222,221,194] := by
    cases ha0 : v97 c <;> cases ha1 : v110 c <;> simp [ClauseSat, litVal, assignment_97, assignment_110, assignment_111, v111, ha0, ha1]
  have hc213 : ClauseSat (assignment c) [222,197] := by
    simp [ClauseSat, litVal, assignment_98, assignment_111, v95, v96, v97, v98, v110, v111]
    all_goals omega
  have hc214 : ClauseSat (assignment c) [225,222] := by
    cases ha0 : v98 c <;> cases ha1 : v111 c <;> simp [ClauseSat, litVal, assignment_111, assignment_112, v112, ha0, ha1]
  have hc215 : ClauseSat (assignment c) [225,197] := by
    cases ha0 : v98 c <;> cases ha1 : v111 c <;> simp [ClauseSat, litVal, assignment_98, assignment_112, v112, ha0, ha1]
  have hc216 : ClauseSat (assignment c) [224,223,196] := by
    cases ha0 : v98 c <;> cases ha1 : v111 c <;> simp [ClauseSat, litVal, assignment_98, assignment_111, assignment_112, v112, ha0, ha1]
  have hc217 : ClauseSat (assignment c) [224,199] := by
    simp [ClauseSat, litVal, assignment_99, assignment_112, v95, v96, v97, v98, v99, v110, v111, v112]
    all_goals omega
  have hc218 : ClauseSat (assignment c) [227,224] := by
    cases ha0 : v99 c <;> cases ha1 : v112 c <;> simp [ClauseSat, litVal, assignment_112, assignment_113, v113, ha0, ha1]
  have hc219 : ClauseSat (assignment c) [227,199] := by
    cases ha0 : v99 c <;> cases ha1 : v112 c <;> simp [ClauseSat, litVal, assignment_99, assignment_113, v113, ha0, ha1]
  have hc220 : ClauseSat (assignment c) [226,225,198] := by
    cases ha0 : v99 c <;> cases ha1 : v112 c <;> simp [ClauseSat, litVal, assignment_99, assignment_112, assignment_113, v113, ha0, ha1]
  have hc221 : ClauseSat (assignment c) [226,201] := by
    simp [ClauseSat, litVal, assignment_100, assignment_113, v95, v96, v97, v98, v99, v100, v110, v111, v112, v113]
    all_goals omega
  have hc222 : ClauseSat (assignment c) [229,226] := by
    cases ha0 : v100 c <;> cases ha1 : v113 c <;> simp [ClauseSat, litVal, assignment_113, assignment_114, v114, ha0, ha1]
  have hc223 : ClauseSat (assignment c) [229,201] := by
    cases ha0 : v100 c <;> cases ha1 : v113 c <;> simp [ClauseSat, litVal, assignment_100, assignment_114, v114, ha0, ha1]
  have hc224 : ClauseSat (assignment c) [228,227,200] := by
    cases ha0 : v100 c <;> cases ha1 : v113 c <;> simp [ClauseSat, litVal, assignment_100, assignment_113, assignment_114, v114, ha0, ha1]
  have hc225 : ClauseSat (assignment c) [228,203] := by
    simp [ClauseSat, litVal, assignment_101, assignment_114, v95, v96, v97, v98, v99, v100, v101, v110, v111, v112, v113, v114]
    all_goals omega
  have hc226 : ClauseSat (assignment c) [231,228] := by
    cases ha0 : v101 c <;> cases ha1 : v114 c <;> simp [ClauseSat, litVal, assignment_114, assignment_115, v115, ha0, ha1]
  have hc227 : ClauseSat (assignment c) [231,203] := by
    cases ha0 : v101 c <;> cases ha1 : v114 c <;> simp [ClauseSat, litVal, assignment_101, assignment_115, v115, ha0, ha1]
  have hc228 : ClauseSat (assignment c) [230,229,202] := by
    cases ha0 : v101 c <;> cases ha1 : v114 c <;> simp [ClauseSat, litVal, assignment_101, assignment_114, assignment_115, v115, ha0, ha1]
  have hc229 : ClauseSat (assignment c) [230,205] := by
    simp [ClauseSat, litVal, assignment_102, assignment_115, v95, v96, v97, v98, v99, v100, v101, v102, v110, v111, v112, v113, v114, v115]
    all_goals omega
  have hc230 : ClauseSat (assignment c) [233,230] := by
    cases ha0 : v102 c <;> cases ha1 : v115 c <;> simp [ClauseSat, litVal, assignment_115, assignment_116, v116, ha0, ha1]
  have hc231 : ClauseSat (assignment c) [233,205] := by
    cases ha0 : v102 c <;> cases ha1 : v115 c <;> simp [ClauseSat, litVal, assignment_102, assignment_116, v116, ha0, ha1]
  have hc232 : ClauseSat (assignment c) [232,231,204] := by
    cases ha0 : v102 c <;> cases ha1 : v115 c <;> simp [ClauseSat, litVal, assignment_102, assignment_115, assignment_116, v116, ha0, ha1]
  have hc233 : ClauseSat (assignment c) [175,191] := by
    simp [ClauseSat, litVal, assignment_87, assignment_95, v87, v95]
    all_goals omega
  have hc234 : ClauseSat (assignment c) [177,220] := by
    simp [ClauseSat, litVal, assignment_88, assignment_110, v88, v95, v96, v110]
    all_goals omega
  have hc235 : ClauseSat (assignment c) [179,222] := by
    simp [ClauseSat, litVal, assignment_89, assignment_111, v89, v95, v96, v97, v110, v111]
    all_goals omega
  have hc236 : ClauseSat (assignment c) [181,224] := by
    simp [ClauseSat, litVal, assignment_90, assignment_112, v90, v95, v96, v97, v98, v110, v111, v112]
    all_goals omega
  have hc237 : ClauseSat (assignment c) [183,226] := by
    simp [ClauseSat, litVal, assignment_91, assignment_113, v91, v95, v96, v97, v98, v99, v110, v111, v112, v113]
    all_goals omega
  have hc238 : ClauseSat (assignment c) [185,228] := by
    simp [ClauseSat, litVal, assignment_92, assignment_114, v92, v95, v96, v97, v98, v99, v100, v110, v111, v112, v113, v114]
    all_goals omega
  have hc239 : ClauseSat (assignment c) [187,230] := by
    simp [ClauseSat, litVal, assignment_93, assignment_115, v93, v95, v96, v97, v98, v99, v100, v101, v110, v111, v112, v113, v114, v115]
    all_goals omega
  have hc240 : ClauseSat (assignment c) [189,232] := by
    simp [ClauseSat, litVal, assignment_94, assignment_116, v94, v95, v96, v97, v98, v99, v100, v101, v102, v110, v111, v112, v113, v114, v115, v116]
    all_goals omega
  have hc241 : ClauseSat (assignment c) [5,235] := by
    cases ha0 : v2 c <;> simp [ClauseSat, litVal, assignment_2, assignment_117, v117, ha0]
  have hc242 : ClauseSat (assignment c) [5,235] := by
    cases ha0 : v2 c <;> simp [ClauseSat, litVal, assignment_2, assignment_117, v117, ha0]
  have hc243 : ClauseSat (assignment c) [4,235] := by
    cases ha0 : v2 c <;> simp [ClauseSat, litVal, assignment_2, assignment_117, v117, ha0]
  have hc244 : ClauseSat (assignment c) [37,237] := by
    by_cases hs : c.a1.val = 0
    · simp [ClauseSat, litVal, assignment_18, assignment_118, v118, v18, hs]
    · simp [ClauseSat, litVal, assignment_18, assignment_118, v18, hs]
  have hc245 : ClauseSat (assignment c) [39,237] := by
    by_cases hs : c.a1.val = 1
    · simp [ClauseSat, litVal, assignment_19, assignment_118, v118, v19, hs]
    · simp [ClauseSat, litVal, assignment_19, assignment_118, v19, hs]
  have hc246 : ClauseSat (assignment c) [41,237] := by
    by_cases hs : c.a1.val = 2
    · simp [ClauseSat, litVal, assignment_20, assignment_118, v118, v20, hs]
    · simp [ClauseSat, litVal, assignment_20, assignment_118, v20, hs]
  have hc247 : ClauseSat (assignment c) [43,237] := by
    by_cases hs : c.a1.val = 3
    · simp [ClauseSat, litVal, assignment_21, assignment_118, v118, v21, hs]
    · simp [ClauseSat, litVal, assignment_21, assignment_118, v21, hs]
  have hc248 : ClauseSat (assignment c) [45,237,234] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_117, assignment_118, v118, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_117, assignment_118, v22, hs]
  have hc249 : ClauseSat (assignment c) [45,236,235] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_117, assignment_118, v118, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_117, assignment_118, v22, hs]
  have hc250 : ClauseSat (assignment c) [47,239] := by
    by_cases hs : c.b1.val = 0
    · simp [ClauseSat, litVal, assignment_23, assignment_119, v119, v23, hs]
    · simp [ClauseSat, litVal, assignment_23, assignment_119, v23, hs]
  have hc251 : ClauseSat (assignment c) [49,239] := by
    by_cases hs : c.b1.val = 1
    · simp [ClauseSat, litVal, assignment_24, assignment_119, v119, v24, hs]
    · simp [ClauseSat, litVal, assignment_24, assignment_119, v24, hs]
  have hc252 : ClauseSat (assignment c) [51,239] := by
    by_cases hs : c.b1.val = 2
    · simp [ClauseSat, litVal, assignment_25, assignment_119, v119, v25, hs]
    · simp [ClauseSat, litVal, assignment_25, assignment_119, v25, hs]
  have hc253 : ClauseSat (assignment c) [53,239] := by
    by_cases hs : c.b1.val = 3
    · simp [ClauseSat, litVal, assignment_26, assignment_119, v119, v26, hs]
    · simp [ClauseSat, litVal, assignment_26, assignment_119, v26, hs]
  have hc254 : ClauseSat (assignment c) [55,239,234] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_117, assignment_119, v119, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_117, assignment_119, v27, hs]
  have hc255 : ClauseSat (assignment c) [55,238,235] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_117, assignment_119, v119, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_117, assignment_119, v27, hs]
  have hc256 : ClauseSat (assignment c) [35,241,236] := by
    cases ha0 : v17 c <;> cases ha1 : v118 c <;> cases ha2 : v119 c <;> simp [ClauseSat, litVal, assignment_17, assignment_118, assignment_120, v120, ha0, ha1, ha2]
  have hc257 : ClauseSat (assignment c) [35,241,238] := by
    cases ha0 : v17 c <;> cases ha1 : v118 c <;> cases ha2 : v119 c <;> simp [ClauseSat, litVal, assignment_17, assignment_119, assignment_120, v120, ha0, ha1, ha2]
  have hc258 : ClauseSat (assignment c) [35,240,237,239] := by
    cases ha0 : v17 c <;> cases ha1 : v118 c <;> cases ha2 : v119 c <;> simp [ClauseSat, litVal, assignment_17, assignment_118, assignment_119, assignment_120, v120, ha0, ha1, ha2]
  have hc259 : ClauseSat (assignment c) [34,240,237] := by
    cases ha0 : v17 c <;> cases ha1 : v118 c <;> cases ha2 : v119 c <;> simp [ClauseSat, litVal, assignment_17, assignment_118, assignment_120, v120, ha0, ha1, ha2]
  have hc260 : ClauseSat (assignment c) [34,240,239] := by
    cases ha0 : v17 c <;> cases ha1 : v118 c <;> cases ha2 : v119 c <;> simp [ClauseSat, litVal, assignment_17, assignment_119, assignment_120, v120, ha0, ha1, ha2]
  have hc261 : ClauseSat (assignment c) [34,241,236,238] := by
    cases ha0 : v17 c <;> cases ha1 : v118 c <;> cases ha2 : v119 c <;> simp [ClauseSat, litVal, assignment_17, assignment_118, assignment_119, assignment_120, v120, ha0, ha1, ha2]
  have hc262 : ClauseSat (assignment c) [75,243] := by
    by_cases hs : c.a2.val = 0
    · simp [ClauseSat, litVal, assignment_37, assignment_121, v121, v37, hs]
    · simp [ClauseSat, litVal, assignment_37, assignment_121, v37, hs]
  have hc263 : ClauseSat (assignment c) [77,243] := by
    by_cases hs : c.a2.val = 1
    · simp [ClauseSat, litVal, assignment_38, assignment_121, v121, v38, hs]
    · simp [ClauseSat, litVal, assignment_38, assignment_121, v38, hs]
  have hc264 : ClauseSat (assignment c) [79,243] := by
    by_cases hs : c.a2.val = 2
    · simp [ClauseSat, litVal, assignment_39, assignment_121, v121, v39, hs]
    · simp [ClauseSat, litVal, assignment_39, assignment_121, v39, hs]
  have hc265 : ClauseSat (assignment c) [81,243] := by
    by_cases hs : c.a2.val = 3
    · simp [ClauseSat, litVal, assignment_40, assignment_121, v121, v40, hs]
    · simp [ClauseSat, litVal, assignment_40, assignment_121, v40, hs]
  have hc266 : ClauseSat (assignment c) [83,243,234] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_117, assignment_121, v121, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_117, assignment_121, v41, hs]
  have hc267 : ClauseSat (assignment c) [83,242,235] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_117, assignment_121, v121, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_117, assignment_121, v41, hs]
  have hc268 : ClauseSat (assignment c) [85,243,240] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_120, assignment_121, v121, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_120, assignment_121, v42, hs]
  have hc269 : ClauseSat (assignment c) [85,242,241] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_120, assignment_121, v121, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_120, assignment_121, v42, hs]
  have hc270 : ClauseSat (assignment c) [87,245] := by
    by_cases hs : c.b2.val = 0
    · simp [ClauseSat, litVal, assignment_43, assignment_122, v122, v43, hs]
    · simp [ClauseSat, litVal, assignment_43, assignment_122, v43, hs]
  have hc271 : ClauseSat (assignment c) [89,245] := by
    by_cases hs : c.b2.val = 1
    · simp [ClauseSat, litVal, assignment_44, assignment_122, v122, v44, hs]
    · simp [ClauseSat, litVal, assignment_44, assignment_122, v44, hs]
  have hc272 : ClauseSat (assignment c) [91,245] := by
    by_cases hs : c.b2.val = 2
    · simp [ClauseSat, litVal, assignment_45, assignment_122, v122, v45, hs]
    · simp [ClauseSat, litVal, assignment_45, assignment_122, v45, hs]
  have hc273 : ClauseSat (assignment c) [93,245] := by
    by_cases hs : c.b2.val = 3
    · simp [ClauseSat, litVal, assignment_46, assignment_122, v122, v46, hs]
    · simp [ClauseSat, litVal, assignment_46, assignment_122, v46, hs]
  have hc274 : ClauseSat (assignment c) [95,245,234] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_117, assignment_122, v122, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_117, assignment_122, v47, hs]
  have hc275 : ClauseSat (assignment c) [95,244,235] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_117, assignment_122, v122, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_117, assignment_122, v47, hs]
  have hc276 : ClauseSat (assignment c) [97,245,240] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_120, assignment_122, v122, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_120, assignment_122, v48, hs]
  have hc277 : ClauseSat (assignment c) [97,244,241] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_120, assignment_122, v122, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_120, assignment_122, v48, hs]
  have hc278 : ClauseSat (assignment c) [73,247,242] := by
    cases ha0 : v36 c <;> cases ha1 : v121 c <;> cases ha2 : v122 c <;> simp [ClauseSat, litVal, assignment_36, assignment_121, assignment_123, v123, ha0, ha1, ha2]
  have hc279 : ClauseSat (assignment c) [73,247,244] := by
    cases ha0 : v36 c <;> cases ha1 : v121 c <;> cases ha2 : v122 c <;> simp [ClauseSat, litVal, assignment_36, assignment_122, assignment_123, v123, ha0, ha1, ha2]
  have hc280 : ClauseSat (assignment c) [73,246,243,245] := by
    cases ha0 : v36 c <;> cases ha1 : v121 c <;> cases ha2 : v122 c <;> simp [ClauseSat, litVal, assignment_36, assignment_121, assignment_122, assignment_123, v123, ha0, ha1, ha2]
  have hc281 : ClauseSat (assignment c) [72,246,243] := by
    cases ha0 : v36 c <;> cases ha1 : v121 c <;> cases ha2 : v122 c <;> simp [ClauseSat, litVal, assignment_36, assignment_121, assignment_123, v123, ha0, ha1, ha2]
  have hc282 : ClauseSat (assignment c) [72,246,245] := by
    cases ha0 : v36 c <;> cases ha1 : v121 c <;> cases ha2 : v122 c <;> simp [ClauseSat, litVal, assignment_36, assignment_122, assignment_123, v123, ha0, ha1, ha2]
  have hc283 : ClauseSat (assignment c) [72,247,242,244] := by
    cases ha0 : v36 c <;> cases ha1 : v121 c <;> cases ha2 : v122 c <;> simp [ClauseSat, litVal, assignment_36, assignment_121, assignment_122, assignment_123, v123, ha0, ha1, ha2]
  have hc284 : ClauseSat (assignment c) [121,249] := by
    by_cases hs : c.a3.val = 0
    · simp [ClauseSat, litVal, assignment_60, assignment_124, v124, v60, hs]
    · simp [ClauseSat, litVal, assignment_60, assignment_124, v60, hs]
  have hc285 : ClauseSat (assignment c) [123,249] := by
    by_cases hs : c.a3.val = 1
    · simp [ClauseSat, litVal, assignment_61, assignment_124, v124, v61, hs]
    · simp [ClauseSat, litVal, assignment_61, assignment_124, v61, hs]
  have hc286 : ClauseSat (assignment c) [125,249] := by
    by_cases hs : c.a3.val = 2
    · simp [ClauseSat, litVal, assignment_62, assignment_124, v124, v62, hs]
    · simp [ClauseSat, litVal, assignment_62, assignment_124, v62, hs]
  have hc287 : ClauseSat (assignment c) [127,249] := by
    by_cases hs : c.a3.val = 3
    · simp [ClauseSat, litVal, assignment_63, assignment_124, v124, v63, hs]
    · simp [ClauseSat, litVal, assignment_63, assignment_124, v63, hs]
  have hc288 : ClauseSat (assignment c) [129,249,234] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_117, assignment_124, v124, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_117, assignment_124, v64, hs]
  have hc289 : ClauseSat (assignment c) [129,248,235] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_117, assignment_124, v124, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_117, assignment_124, v64, hs]
  have hc290 : ClauseSat (assignment c) [131,249,240] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_120, assignment_124, v124, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_120, assignment_124, v65, hs]
  have hc291 : ClauseSat (assignment c) [131,248,241] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_120, assignment_124, v124, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_120, assignment_124, v65, hs]
  have hc292 : ClauseSat (assignment c) [133,249,246] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_123, assignment_124, v124, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_123, assignment_124, v66, hs]
  have hc293 : ClauseSat (assignment c) [133,248,247] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_123, assignment_124, v124, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_123, assignment_124, v66, hs]
  have hc294 : ClauseSat (assignment c) [135,251] := by
    by_cases hs : c.b3.val = 0
    · simp [ClauseSat, litVal, assignment_67, assignment_125, v125, v67, hs]
    · simp [ClauseSat, litVal, assignment_67, assignment_125, v67, hs]
  have hc295 : ClauseSat (assignment c) [137,251] := by
    by_cases hs : c.b3.val = 1
    · simp [ClauseSat, litVal, assignment_68, assignment_125, v125, v68, hs]
    · simp [ClauseSat, litVal, assignment_68, assignment_125, v68, hs]
  have hc296 : ClauseSat (assignment c) [139,251] := by
    by_cases hs : c.b3.val = 2
    · simp [ClauseSat, litVal, assignment_69, assignment_125, v125, v69, hs]
    · simp [ClauseSat, litVal, assignment_69, assignment_125, v69, hs]
  have hc297 : ClauseSat (assignment c) [141,251] := by
    by_cases hs : c.b3.val = 3
    · simp [ClauseSat, litVal, assignment_70, assignment_125, v125, v70, hs]
    · simp [ClauseSat, litVal, assignment_70, assignment_125, v70, hs]
  have hc298 : ClauseSat (assignment c) [143,251,234] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_117, assignment_125, v125, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_117, assignment_125, v71, hs]
  have hc299 : ClauseSat (assignment c) [143,250,235] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_117, assignment_125, v125, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_117, assignment_125, v71, hs]
  simp only [chunk2, List.forall_mem_cons]
  exact ⟨hc200, hc201, hc202, hc203, hc204, hc205, hc206, hc207, hc208, hc209, hc210, hc211, hc212, hc213, hc214, hc215, hc216, hc217, hc218, hc219, hc220, hc221, hc222, hc223, hc224, hc225, hc226, hc227, hc228, hc229, hc230, hc231, hc232, hc233, hc234, hc235, hc236, hc237, hc238, hc239, hc240, hc241, hc242, hc243, hc244, hc245, hc246, hc247, hc248, hc249, hc250, hc251, hc252, hc253, hc254, hc255, hc256, hc257, hc258, hc259, hc260, hc261, hc262, hc263, hc264, hc265, hc266, hc267, hc268, hc269, hc270, hc271, hc272, hc273, hc274, hc275, hc276, hc277, hc278, hc279, hc280, hc281, hc282, hc283, hc284, hc285, hc286, hc287, hc288, hc289, hc290, hc291, hc292, hc293, hc294, hc295, hc296, hc297, hc298, hc299, by simp⟩
#check satChunk2

def chunk3 : List (List Nat) := [[145, 251, 240], [145, 250, 241], [147, 251, 246], [147, 250, 247], [119, 253, 248], [119, 253, 250], [119, 252, 249, 251], [118, 252, 249], [118, 252, 251], [118, 253, 248, 250], [175, 255], [177, 255], [179, 255], [181, 255], [183, 255, 234], [183, 254, 235], [185, 255, 240], [185, 254, 241], [187, 255, 246], [187, 254, 247], [189, 255, 252], [189, 254, 253], [191, 257], [193, 257], [195, 257], [197, 257], [199, 257, 234], [199, 256, 235], [201, 257, 240], [201, 256, 241], [203, 257, 246], [203, 256, 247], [205, 257, 252], [205, 256, 253], [173, 259, 254], [173, 259, 256], [173, 258, 255, 257], [172, 258, 255], [172, 258, 257], [172, 259, 254, 256], [259], [7, 260], [9, 261], [11, 261], [13, 261], [15, 262], [17, 263], [19, 263], [21, 263], [5, 265, 260], [5, 265, 262], [5, 264, 261, 263], [4, 264, 261], [4, 264, 263], [4, 265, 260, 262], [37, 266], [39, 267], [41, 267], [43, 267], [45, 267, 264], [45, 266, 265], [47, 268], [49, 269], [51, 269], [53, 269], [55, 269, 264], [55, 268, 265], [35, 271, 266], [35, 271, 268], [35, 270, 267, 269], [34, 270, 267], [34, 270, 269], [34, 271, 266, 268], [75, 272], [77, 273], [79, 273], [81, 273], [83, 273, 264], [83, 272, 265], [85, 273, 270], [85, 272, 271], [87, 274], [89, 275], [91, 275], [93, 275], [95, 275, 264], [95, 274, 265], [97, 275, 270], [97, 274, 271], [73, 277, 272], [73, 277, 274], [73, 276, 273, 275], [72, 276, 273], [72, 276, 275], [72, 277, 272, 274], [121, 278], [123, 279], [125, 279], [127, 279], [129, 279, 264]]
theorem satChunk3 (c : Candidate) (hv : valid c)
    (hr : ∀ r : Fin 16, output c r = target r)
    (hl : derivativeLeft c = false) (hd : derivativeRight c = false) :
    ∀ cl ∈ chunk3, ClauseSat (assignment c) cl := by
  rcases hv with ⟨h0, h1, h2, h3, h4⟩
  have hc300 : ClauseSat (assignment c) [145,251,240] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_120, assignment_125, v125, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_120, assignment_125, v72, hs]
  have hc301 : ClauseSat (assignment c) [145,250,241] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_120, assignment_125, v125, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_120, assignment_125, v72, hs]
  have hc302 : ClauseSat (assignment c) [147,251,246] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_123, assignment_125, v125, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_123, assignment_125, v73, hs]
  have hc303 : ClauseSat (assignment c) [147,250,247] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_123, assignment_125, v125, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_123, assignment_125, v73, hs]
  have hc304 : ClauseSat (assignment c) [119,253,248] := by
    cases ha0 : v59 c <;> cases ha1 : v124 c <;> cases ha2 : v125 c <;> simp [ClauseSat, litVal, assignment_59, assignment_124, assignment_126, v126, ha0, ha1, ha2]
  have hc305 : ClauseSat (assignment c) [119,253,250] := by
    cases ha0 : v59 c <;> cases ha1 : v124 c <;> cases ha2 : v125 c <;> simp [ClauseSat, litVal, assignment_59, assignment_125, assignment_126, v126, ha0, ha1, ha2]
  have hc306 : ClauseSat (assignment c) [119,252,249,251] := by
    cases ha0 : v59 c <;> cases ha1 : v124 c <;> cases ha2 : v125 c <;> simp [ClauseSat, litVal, assignment_59, assignment_124, assignment_125, assignment_126, v126, ha0, ha1, ha2]
  have hc307 : ClauseSat (assignment c) [118,252,249] := by
    cases ha0 : v59 c <;> cases ha1 : v124 c <;> cases ha2 : v125 c <;> simp [ClauseSat, litVal, assignment_59, assignment_124, assignment_126, v126, ha0, ha1, ha2]
  have hc308 : ClauseSat (assignment c) [118,252,251] := by
    cases ha0 : v59 c <;> cases ha1 : v124 c <;> cases ha2 : v125 c <;> simp [ClauseSat, litVal, assignment_59, assignment_125, assignment_126, v126, ha0, ha1, ha2]
  have hc309 : ClauseSat (assignment c) [118,253,248,250] := by
    cases ha0 : v59 c <;> cases ha1 : v124 c <;> cases ha2 : v125 c <;> simp [ClauseSat, litVal, assignment_59, assignment_124, assignment_125, assignment_126, v126, ha0, ha1, ha2]
  have hc310 : ClauseSat (assignment c) [175,255] := by
    by_cases hs : c.a4.val = 0
    · simp [ClauseSat, litVal, assignment_87, assignment_127, v127, v87, hs]
    · simp [ClauseSat, litVal, assignment_87, assignment_127, v87, hs]
  have hc311 : ClauseSat (assignment c) [177,255] := by
    by_cases hs : c.a4.val = 1
    · simp [ClauseSat, litVal, assignment_88, assignment_127, v127, v88, hs]
    · simp [ClauseSat, litVal, assignment_88, assignment_127, v88, hs]
  have hc312 : ClauseSat (assignment c) [179,255] := by
    by_cases hs : c.a4.val = 2
    · simp [ClauseSat, litVal, assignment_89, assignment_127, v127, v89, hs]
    · simp [ClauseSat, litVal, assignment_89, assignment_127, v89, hs]
  have hc313 : ClauseSat (assignment c) [181,255] := by
    by_cases hs : c.a4.val = 3
    · simp [ClauseSat, litVal, assignment_90, assignment_127, v127, v90, hs]
    · simp [ClauseSat, litVal, assignment_90, assignment_127, v90, hs]
  have hc314 : ClauseSat (assignment c) [183,255,234] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_117, assignment_127, v127, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_117, assignment_127, v91, hs]
  have hc315 : ClauseSat (assignment c) [183,254,235] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_117, assignment_127, v127, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_117, assignment_127, v91, hs]
  have hc316 : ClauseSat (assignment c) [185,255,240] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_120, assignment_127, v127, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_120, assignment_127, v92, hs]
  have hc317 : ClauseSat (assignment c) [185,254,241] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_120, assignment_127, v127, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_120, assignment_127, v92, hs]
  have hc318 : ClauseSat (assignment c) [187,255,246] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_123, assignment_127, v127, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_123, assignment_127, v93, hs]
  have hc319 : ClauseSat (assignment c) [187,254,247] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_123, assignment_127, v127, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_123, assignment_127, v93, hs]
  have hc320 : ClauseSat (assignment c) [189,255,252] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_126, assignment_127, v127, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_126, assignment_127, v94, hs]
  have hc321 : ClauseSat (assignment c) [189,254,253] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_126, assignment_127, v127, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_126, assignment_127, v94, hs]
  have hc322 : ClauseSat (assignment c) [191,257] := by
    by_cases hs : c.b4.val = 0
    · simp [ClauseSat, litVal, assignment_95, assignment_128, v128, v95, hs]
    · simp [ClauseSat, litVal, assignment_95, assignment_128, v95, hs]
  have hc323 : ClauseSat (assignment c) [193,257] := by
    by_cases hs : c.b4.val = 1
    · simp [ClauseSat, litVal, assignment_96, assignment_128, v128, v96, hs]
    · simp [ClauseSat, litVal, assignment_96, assignment_128, v96, hs]
  have hc324 : ClauseSat (assignment c) [195,257] := by
    by_cases hs : c.b4.val = 2
    · simp [ClauseSat, litVal, assignment_97, assignment_128, v128, v97, hs]
    · simp [ClauseSat, litVal, assignment_97, assignment_128, v97, hs]
  have hc325 : ClauseSat (assignment c) [197,257] := by
    by_cases hs : c.b4.val = 3
    · simp [ClauseSat, litVal, assignment_98, assignment_128, v128, v98, hs]
    · simp [ClauseSat, litVal, assignment_98, assignment_128, v98, hs]
  have hc326 : ClauseSat (assignment c) [199,257,234] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_117, assignment_128, v128, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_117, assignment_128, v99, hs]
  have hc327 : ClauseSat (assignment c) [199,256,235] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_117, assignment_128, v128, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_117, assignment_128, v99, hs]
  have hc328 : ClauseSat (assignment c) [201,257,240] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_120, assignment_128, v128, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_120, assignment_128, v100, hs]
  have hc329 : ClauseSat (assignment c) [201,256,241] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_120, assignment_128, v128, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_120, assignment_128, v100, hs]
  have hc330 : ClauseSat (assignment c) [203,257,246] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_123, assignment_128, v128, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_123, assignment_128, v101, hs]
  have hc331 : ClauseSat (assignment c) [203,256,247] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_123, assignment_128, v128, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_123, assignment_128, v101, hs]
  have hc332 : ClauseSat (assignment c) [205,257,252] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_126, assignment_128, v128, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_126, assignment_128, v102, hs]
  have hc333 : ClauseSat (assignment c) [205,256,253] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_126, assignment_128, v128, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_126, assignment_128, v102, hs]
  have hc334 : ClauseSat (assignment c) [173,259,254] := by
    cases ha0 : v86 c <;> cases ha1 : v127 c <;> cases ha2 : v128 c <;> simp [ClauseSat, litVal, assignment_86, assignment_127, assignment_129, v129, ha0, ha1, ha2]
  have hc335 : ClauseSat (assignment c) [173,259,256] := by
    cases ha0 : v86 c <;> cases ha1 : v127 c <;> cases ha2 : v128 c <;> simp [ClauseSat, litVal, assignment_86, assignment_128, assignment_129, v129, ha0, ha1, ha2]
  have hc336 : ClauseSat (assignment c) [173,258,255,257] := by
    cases ha0 : v86 c <;> cases ha1 : v127 c <;> cases ha2 : v128 c <;> simp [ClauseSat, litVal, assignment_86, assignment_127, assignment_128, assignment_129, v129, ha0, ha1, ha2]
  have hc337 : ClauseSat (assignment c) [172,258,255] := by
    cases ha0 : v86 c <;> cases ha1 : v127 c <;> cases ha2 : v128 c <;> simp [ClauseSat, litVal, assignment_86, assignment_127, assignment_129, v129, ha0, ha1, ha2]
  have hc338 : ClauseSat (assignment c) [172,258,257] := by
    cases ha0 : v86 c <;> cases ha1 : v127 c <;> cases ha2 : v128 c <;> simp [ClauseSat, litVal, assignment_86, assignment_128, assignment_129, v129, ha0, ha1, ha2]
  have hc339 : ClauseSat (assignment c) [172,259,254,256] := by
    cases ha0 : v86 c <;> cases ha1 : v127 c <;> cases ha2 : v128 c <;> simp [ClauseSat, litVal, assignment_86, assignment_127, assignment_128, assignment_129, v129, ha0, ha1, ha2]
  have hc340 : ClauseSat (assignment c) [259] := by
    have hh := hr ⟨0, by decide⟩
    have ht : target ⟨0, by decide⟩ = false := by decide
    rw [ht] at hh
    simpa [ClauseSat, litVal, assignment_129, output] using hh
  have hc341 : ClauseSat (assignment c) [7,260] := by
    by_cases hs : c.a0.val = 0
    · simp [ClauseSat, litVal, assignment_3, assignment_130, v130, v3, hs]
    · simp [ClauseSat, litVal, assignment_3, assignment_130, v3, hs]
  have hc342 : ClauseSat (assignment c) [9,261] := by
    by_cases hs : c.a0.val = 1
    · simp [ClauseSat, litVal, assignment_4, assignment_130, v130, v4, hs]
    · simp [ClauseSat, litVal, assignment_4, assignment_130, v4, hs]
  have hc343 : ClauseSat (assignment c) [11,261] := by
    by_cases hs : c.a0.val = 2
    · simp [ClauseSat, litVal, assignment_5, assignment_130, v130, v5, hs]
    · simp [ClauseSat, litVal, assignment_5, assignment_130, v5, hs]
  have hc344 : ClauseSat (assignment c) [13,261] := by
    by_cases hs : c.a0.val = 3
    · simp [ClauseSat, litVal, assignment_6, assignment_130, v130, v6, hs]
    · simp [ClauseSat, litVal, assignment_6, assignment_130, v6, hs]
  have hc345 : ClauseSat (assignment c) [15,262] := by
    by_cases hs : c.b0.val = 0
    · simp [ClauseSat, litVal, assignment_7, assignment_131, v131, v7, hs]
    · simp [ClauseSat, litVal, assignment_7, assignment_131, v7, hs]
  have hc346 : ClauseSat (assignment c) [17,263] := by
    by_cases hs : c.b0.val = 1
    · simp [ClauseSat, litVal, assignment_8, assignment_131, v131, v8, hs]
    · simp [ClauseSat, litVal, assignment_8, assignment_131, v8, hs]
  have hc347 : ClauseSat (assignment c) [19,263] := by
    by_cases hs : c.b0.val = 2
    · simp [ClauseSat, litVal, assignment_9, assignment_131, v131, v9, hs]
    · simp [ClauseSat, litVal, assignment_9, assignment_131, v9, hs]
  have hc348 : ClauseSat (assignment c) [21,263] := by
    by_cases hs : c.b0.val = 3
    · simp [ClauseSat, litVal, assignment_10, assignment_131, v131, v10, hs]
    · simp [ClauseSat, litVal, assignment_10, assignment_131, v10, hs]
  have hc349 : ClauseSat (assignment c) [5,265,260] := by
    cases ha0 : v2 c <;> cases ha1 : v130 c <;> cases ha2 : v131 c <;> simp [ClauseSat, litVal, assignment_2, assignment_130, assignment_132, v132, ha0, ha1, ha2]
  have hc350 : ClauseSat (assignment c) [5,265,262] := by
    cases ha0 : v2 c <;> cases ha1 : v130 c <;> cases ha2 : v131 c <;> simp [ClauseSat, litVal, assignment_2, assignment_131, assignment_132, v132, ha0, ha1, ha2]
  have hc351 : ClauseSat (assignment c) [5,264,261,263] := by
    cases ha0 : v2 c <;> cases ha1 : v130 c <;> cases ha2 : v131 c <;> simp [ClauseSat, litVal, assignment_2, assignment_130, assignment_131, assignment_132, v132, ha0, ha1, ha2]
  have hc352 : ClauseSat (assignment c) [4,264,261] := by
    cases ha0 : v2 c <;> cases ha1 : v130 c <;> cases ha2 : v131 c <;> simp [ClauseSat, litVal, assignment_2, assignment_130, assignment_132, v132, ha0, ha1, ha2]
  have hc353 : ClauseSat (assignment c) [4,264,263] := by
    cases ha0 : v2 c <;> cases ha1 : v130 c <;> cases ha2 : v131 c <;> simp [ClauseSat, litVal, assignment_2, assignment_131, assignment_132, v132, ha0, ha1, ha2]
  have hc354 : ClauseSat (assignment c) [4,265,260,262] := by
    cases ha0 : v2 c <;> cases ha1 : v130 c <;> cases ha2 : v131 c <;> simp [ClauseSat, litVal, assignment_2, assignment_130, assignment_131, assignment_132, v132, ha0, ha1, ha2]
  have hc355 : ClauseSat (assignment c) [37,266] := by
    by_cases hs : c.a1.val = 0
    · simp [ClauseSat, litVal, assignment_18, assignment_133, v133, v18, hs]
    · simp [ClauseSat, litVal, assignment_18, assignment_133, v18, hs]
  have hc356 : ClauseSat (assignment c) [39,267] := by
    by_cases hs : c.a1.val = 1
    · simp [ClauseSat, litVal, assignment_19, assignment_133, v133, v19, hs]
    · simp [ClauseSat, litVal, assignment_19, assignment_133, v19, hs]
  have hc357 : ClauseSat (assignment c) [41,267] := by
    by_cases hs : c.a1.val = 2
    · simp [ClauseSat, litVal, assignment_20, assignment_133, v133, v20, hs]
    · simp [ClauseSat, litVal, assignment_20, assignment_133, v20, hs]
  have hc358 : ClauseSat (assignment c) [43,267] := by
    by_cases hs : c.a1.val = 3
    · simp [ClauseSat, litVal, assignment_21, assignment_133, v133, v21, hs]
    · simp [ClauseSat, litVal, assignment_21, assignment_133, v21, hs]
  have hc359 : ClauseSat (assignment c) [45,267,264] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_132, assignment_133, v133, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_132, assignment_133, v22, hs]
  have hc360 : ClauseSat (assignment c) [45,266,265] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_132, assignment_133, v133, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_132, assignment_133, v22, hs]
  have hc361 : ClauseSat (assignment c) [47,268] := by
    by_cases hs : c.b1.val = 0
    · simp [ClauseSat, litVal, assignment_23, assignment_134, v134, v23, hs]
    · simp [ClauseSat, litVal, assignment_23, assignment_134, v23, hs]
  have hc362 : ClauseSat (assignment c) [49,269] := by
    by_cases hs : c.b1.val = 1
    · simp [ClauseSat, litVal, assignment_24, assignment_134, v134, v24, hs]
    · simp [ClauseSat, litVal, assignment_24, assignment_134, v24, hs]
  have hc363 : ClauseSat (assignment c) [51,269] := by
    by_cases hs : c.b1.val = 2
    · simp [ClauseSat, litVal, assignment_25, assignment_134, v134, v25, hs]
    · simp [ClauseSat, litVal, assignment_25, assignment_134, v25, hs]
  have hc364 : ClauseSat (assignment c) [53,269] := by
    by_cases hs : c.b1.val = 3
    · simp [ClauseSat, litVal, assignment_26, assignment_134, v134, v26, hs]
    · simp [ClauseSat, litVal, assignment_26, assignment_134, v26, hs]
  have hc365 : ClauseSat (assignment c) [55,269,264] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_132, assignment_134, v134, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_132, assignment_134, v27, hs]
  have hc366 : ClauseSat (assignment c) [55,268,265] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_132, assignment_134, v134, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_132, assignment_134, v27, hs]
  have hc367 : ClauseSat (assignment c) [35,271,266] := by
    cases ha0 : v17 c <;> cases ha1 : v133 c <;> cases ha2 : v134 c <;> simp [ClauseSat, litVal, assignment_17, assignment_133, assignment_135, v135, ha0, ha1, ha2]
  have hc368 : ClauseSat (assignment c) [35,271,268] := by
    cases ha0 : v17 c <;> cases ha1 : v133 c <;> cases ha2 : v134 c <;> simp [ClauseSat, litVal, assignment_17, assignment_134, assignment_135, v135, ha0, ha1, ha2]
  have hc369 : ClauseSat (assignment c) [35,270,267,269] := by
    cases ha0 : v17 c <;> cases ha1 : v133 c <;> cases ha2 : v134 c <;> simp [ClauseSat, litVal, assignment_17, assignment_133, assignment_134, assignment_135, v135, ha0, ha1, ha2]
  have hc370 : ClauseSat (assignment c) [34,270,267] := by
    cases ha0 : v17 c <;> cases ha1 : v133 c <;> cases ha2 : v134 c <;> simp [ClauseSat, litVal, assignment_17, assignment_133, assignment_135, v135, ha0, ha1, ha2]
  have hc371 : ClauseSat (assignment c) [34,270,269] := by
    cases ha0 : v17 c <;> cases ha1 : v133 c <;> cases ha2 : v134 c <;> simp [ClauseSat, litVal, assignment_17, assignment_134, assignment_135, v135, ha0, ha1, ha2]
  have hc372 : ClauseSat (assignment c) [34,271,266,268] := by
    cases ha0 : v17 c <;> cases ha1 : v133 c <;> cases ha2 : v134 c <;> simp [ClauseSat, litVal, assignment_17, assignment_133, assignment_134, assignment_135, v135, ha0, ha1, ha2]
  have hc373 : ClauseSat (assignment c) [75,272] := by
    by_cases hs : c.a2.val = 0
    · simp [ClauseSat, litVal, assignment_37, assignment_136, v136, v37, hs]
    · simp [ClauseSat, litVal, assignment_37, assignment_136, v37, hs]
  have hc374 : ClauseSat (assignment c) [77,273] := by
    by_cases hs : c.a2.val = 1
    · simp [ClauseSat, litVal, assignment_38, assignment_136, v136, v38, hs]
    · simp [ClauseSat, litVal, assignment_38, assignment_136, v38, hs]
  have hc375 : ClauseSat (assignment c) [79,273] := by
    by_cases hs : c.a2.val = 2
    · simp [ClauseSat, litVal, assignment_39, assignment_136, v136, v39, hs]
    · simp [ClauseSat, litVal, assignment_39, assignment_136, v39, hs]
  have hc376 : ClauseSat (assignment c) [81,273] := by
    by_cases hs : c.a2.val = 3
    · simp [ClauseSat, litVal, assignment_40, assignment_136, v136, v40, hs]
    · simp [ClauseSat, litVal, assignment_40, assignment_136, v40, hs]
  have hc377 : ClauseSat (assignment c) [83,273,264] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_132, assignment_136, v136, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_132, assignment_136, v41, hs]
  have hc378 : ClauseSat (assignment c) [83,272,265] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_132, assignment_136, v136, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_132, assignment_136, v41, hs]
  have hc379 : ClauseSat (assignment c) [85,273,270] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_135, assignment_136, v136, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_135, assignment_136, v42, hs]
  have hc380 : ClauseSat (assignment c) [85,272,271] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_135, assignment_136, v136, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_135, assignment_136, v42, hs]
  have hc381 : ClauseSat (assignment c) [87,274] := by
    by_cases hs : c.b2.val = 0
    · simp [ClauseSat, litVal, assignment_43, assignment_137, v137, v43, hs]
    · simp [ClauseSat, litVal, assignment_43, assignment_137, v43, hs]
  have hc382 : ClauseSat (assignment c) [89,275] := by
    by_cases hs : c.b2.val = 1
    · simp [ClauseSat, litVal, assignment_44, assignment_137, v137, v44, hs]
    · simp [ClauseSat, litVal, assignment_44, assignment_137, v44, hs]
  have hc383 : ClauseSat (assignment c) [91,275] := by
    by_cases hs : c.b2.val = 2
    · simp [ClauseSat, litVal, assignment_45, assignment_137, v137, v45, hs]
    · simp [ClauseSat, litVal, assignment_45, assignment_137, v45, hs]
  have hc384 : ClauseSat (assignment c) [93,275] := by
    by_cases hs : c.b2.val = 3
    · simp [ClauseSat, litVal, assignment_46, assignment_137, v137, v46, hs]
    · simp [ClauseSat, litVal, assignment_46, assignment_137, v46, hs]
  have hc385 : ClauseSat (assignment c) [95,275,264] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_132, assignment_137, v137, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_132, assignment_137, v47, hs]
  have hc386 : ClauseSat (assignment c) [95,274,265] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_132, assignment_137, v137, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_132, assignment_137, v47, hs]
  have hc387 : ClauseSat (assignment c) [97,275,270] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_135, assignment_137, v137, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_135, assignment_137, v48, hs]
  have hc388 : ClauseSat (assignment c) [97,274,271] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_135, assignment_137, v137, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_135, assignment_137, v48, hs]
  have hc389 : ClauseSat (assignment c) [73,277,272] := by
    cases ha0 : v36 c <;> cases ha1 : v136 c <;> cases ha2 : v137 c <;> simp [ClauseSat, litVal, assignment_36, assignment_136, assignment_138, v138, ha0, ha1, ha2]
  have hc390 : ClauseSat (assignment c) [73,277,274] := by
    cases ha0 : v36 c <;> cases ha1 : v136 c <;> cases ha2 : v137 c <;> simp [ClauseSat, litVal, assignment_36, assignment_137, assignment_138, v138, ha0, ha1, ha2]
  have hc391 : ClauseSat (assignment c) [73,276,273,275] := by
    cases ha0 : v36 c <;> cases ha1 : v136 c <;> cases ha2 : v137 c <;> simp [ClauseSat, litVal, assignment_36, assignment_136, assignment_137, assignment_138, v138, ha0, ha1, ha2]
  have hc392 : ClauseSat (assignment c) [72,276,273] := by
    cases ha0 : v36 c <;> cases ha1 : v136 c <;> cases ha2 : v137 c <;> simp [ClauseSat, litVal, assignment_36, assignment_136, assignment_138, v138, ha0, ha1, ha2]
  have hc393 : ClauseSat (assignment c) [72,276,275] := by
    cases ha0 : v36 c <;> cases ha1 : v136 c <;> cases ha2 : v137 c <;> simp [ClauseSat, litVal, assignment_36, assignment_137, assignment_138, v138, ha0, ha1, ha2]
  have hc394 : ClauseSat (assignment c) [72,277,272,274] := by
    cases ha0 : v36 c <;> cases ha1 : v136 c <;> cases ha2 : v137 c <;> simp [ClauseSat, litVal, assignment_36, assignment_136, assignment_137, assignment_138, v138, ha0, ha1, ha2]
  have hc395 : ClauseSat (assignment c) [121,278] := by
    by_cases hs : c.a3.val = 0
    · simp [ClauseSat, litVal, assignment_60, assignment_139, v139, v60, hs]
    · simp [ClauseSat, litVal, assignment_60, assignment_139, v60, hs]
  have hc396 : ClauseSat (assignment c) [123,279] := by
    by_cases hs : c.a3.val = 1
    · simp [ClauseSat, litVal, assignment_61, assignment_139, v139, v61, hs]
    · simp [ClauseSat, litVal, assignment_61, assignment_139, v61, hs]
  have hc397 : ClauseSat (assignment c) [125,279] := by
    by_cases hs : c.a3.val = 2
    · simp [ClauseSat, litVal, assignment_62, assignment_139, v139, v62, hs]
    · simp [ClauseSat, litVal, assignment_62, assignment_139, v62, hs]
  have hc398 : ClauseSat (assignment c) [127,279] := by
    by_cases hs : c.a3.val = 3
    · simp [ClauseSat, litVal, assignment_63, assignment_139, v139, v63, hs]
    · simp [ClauseSat, litVal, assignment_63, assignment_139, v63, hs]
  have hc399 : ClauseSat (assignment c) [129,279,264] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_132, assignment_139, v139, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_132, assignment_139, v64, hs]
  simp only [chunk3, List.forall_mem_cons]
  exact ⟨hc300, hc301, hc302, hc303, hc304, hc305, hc306, hc307, hc308, hc309, hc310, hc311, hc312, hc313, hc314, hc315, hc316, hc317, hc318, hc319, hc320, hc321, hc322, hc323, hc324, hc325, hc326, hc327, hc328, hc329, hc330, hc331, hc332, hc333, hc334, hc335, hc336, hc337, hc338, hc339, hc340, hc341, hc342, hc343, hc344, hc345, hc346, hc347, hc348, hc349, hc350, hc351, hc352, hc353, hc354, hc355, hc356, hc357, hc358, hc359, hc360, hc361, hc362, hc363, hc364, hc365, hc366, hc367, hc368, hc369, hc370, hc371, hc372, hc373, hc374, hc375, hc376, hc377, hc378, hc379, hc380, hc381, hc382, hc383, hc384, hc385, hc386, hc387, hc388, hc389, hc390, hc391, hc392, hc393, hc394, hc395, hc396, hc397, hc398, hc399, by simp⟩
#check satChunk3

def chunk4 : List (List Nat) := [[129, 278, 265], [131, 279, 270], [131, 278, 271], [133, 279, 276], [133, 278, 277], [135, 280], [137, 281], [139, 281], [141, 281], [143, 281, 264], [143, 280, 265], [145, 281, 270], [145, 280, 271], [147, 281, 276], [147, 280, 277], [119, 283, 278], [119, 283, 280], [119, 282, 279, 281], [118, 282, 279], [118, 282, 281], [118, 283, 278, 280], [175, 284], [177, 285], [179, 285], [181, 285], [183, 285, 264], [183, 284, 265], [185, 285, 270], [185, 284, 271], [187, 285, 276], [187, 284, 277], [189, 285, 282], [189, 284, 283], [191, 286], [193, 287], [195, 287], [197, 287], [199, 287, 264], [199, 286, 265], [201, 287, 270], [201, 286, 271], [203, 287, 276], [203, 286, 277], [205, 287, 282], [205, 286, 283], [173, 289, 284], [173, 289, 286], [173, 288, 285, 287], [172, 288, 285], [172, 288, 287], [172, 289, 284, 286], [289], [7, 291], [9, 290], [11, 291], [13, 291], [15, 293], [17, 292], [19, 293], [21, 293], [5, 295, 290], [5, 295, 292], [5, 294, 291, 293], [4, 294, 291], [4, 294, 293], [4, 295, 290, 292], [37, 297], [39, 296], [41, 297], [43, 297], [45, 297, 294], [45, 296, 295], [47, 299], [49, 298], [51, 299], [53, 299], [55, 299, 294], [55, 298, 295], [35, 301, 296], [35, 301, 298], [35, 300, 297, 299], [34, 300, 297], [34, 300, 299], [34, 301, 296, 298], [75, 303], [77, 302], [79, 303], [81, 303], [83, 303, 294], [83, 302, 295], [85, 303, 300], [85, 302, 301], [87, 305], [89, 304], [91, 305], [93, 305], [95, 305, 294], [95, 304, 295], [97, 305, 300], [97, 304, 301]]
theorem satChunk4 (c : Candidate) (hv : valid c)
    (hr : ∀ r : Fin 16, output c r = target r)
    (hl : derivativeLeft c = false) (hd : derivativeRight c = false) :
    ∀ cl ∈ chunk4, ClauseSat (assignment c) cl := by
  rcases hv with ⟨h0, h1, h2, h3, h4⟩
  have hc400 : ClauseSat (assignment c) [129,278,265] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_132, assignment_139, v139, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_132, assignment_139, v64, hs]
  have hc401 : ClauseSat (assignment c) [131,279,270] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_135, assignment_139, v139, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_135, assignment_139, v65, hs]
  have hc402 : ClauseSat (assignment c) [131,278,271] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_135, assignment_139, v139, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_135, assignment_139, v65, hs]
  have hc403 : ClauseSat (assignment c) [133,279,276] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_138, assignment_139, v139, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_138, assignment_139, v66, hs]
  have hc404 : ClauseSat (assignment c) [133,278,277] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_138, assignment_139, v139, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_138, assignment_139, v66, hs]
  have hc405 : ClauseSat (assignment c) [135,280] := by
    by_cases hs : c.b3.val = 0
    · simp [ClauseSat, litVal, assignment_67, assignment_140, v140, v67, hs]
    · simp [ClauseSat, litVal, assignment_67, assignment_140, v67, hs]
  have hc406 : ClauseSat (assignment c) [137,281] := by
    by_cases hs : c.b3.val = 1
    · simp [ClauseSat, litVal, assignment_68, assignment_140, v140, v68, hs]
    · simp [ClauseSat, litVal, assignment_68, assignment_140, v68, hs]
  have hc407 : ClauseSat (assignment c) [139,281] := by
    by_cases hs : c.b3.val = 2
    · simp [ClauseSat, litVal, assignment_69, assignment_140, v140, v69, hs]
    · simp [ClauseSat, litVal, assignment_69, assignment_140, v69, hs]
  have hc408 : ClauseSat (assignment c) [141,281] := by
    by_cases hs : c.b3.val = 3
    · simp [ClauseSat, litVal, assignment_70, assignment_140, v140, v70, hs]
    · simp [ClauseSat, litVal, assignment_70, assignment_140, v70, hs]
  have hc409 : ClauseSat (assignment c) [143,281,264] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_132, assignment_140, v140, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_132, assignment_140, v71, hs]
  have hc410 : ClauseSat (assignment c) [143,280,265] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_132, assignment_140, v140, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_132, assignment_140, v71, hs]
  have hc411 : ClauseSat (assignment c) [145,281,270] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_135, assignment_140, v140, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_135, assignment_140, v72, hs]
  have hc412 : ClauseSat (assignment c) [145,280,271] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_135, assignment_140, v140, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_135, assignment_140, v72, hs]
  have hc413 : ClauseSat (assignment c) [147,281,276] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_138, assignment_140, v140, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_138, assignment_140, v73, hs]
  have hc414 : ClauseSat (assignment c) [147,280,277] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_138, assignment_140, v140, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_138, assignment_140, v73, hs]
  have hc415 : ClauseSat (assignment c) [119,283,278] := by
    cases ha0 : v59 c <;> cases ha1 : v139 c <;> cases ha2 : v140 c <;> simp [ClauseSat, litVal, assignment_59, assignment_139, assignment_141, v141, ha0, ha1, ha2]
  have hc416 : ClauseSat (assignment c) [119,283,280] := by
    cases ha0 : v59 c <;> cases ha1 : v139 c <;> cases ha2 : v140 c <;> simp [ClauseSat, litVal, assignment_59, assignment_140, assignment_141, v141, ha0, ha1, ha2]
  have hc417 : ClauseSat (assignment c) [119,282,279,281] := by
    cases ha0 : v59 c <;> cases ha1 : v139 c <;> cases ha2 : v140 c <;> simp [ClauseSat, litVal, assignment_59, assignment_139, assignment_140, assignment_141, v141, ha0, ha1, ha2]
  have hc418 : ClauseSat (assignment c) [118,282,279] := by
    cases ha0 : v59 c <;> cases ha1 : v139 c <;> cases ha2 : v140 c <;> simp [ClauseSat, litVal, assignment_59, assignment_139, assignment_141, v141, ha0, ha1, ha2]
  have hc419 : ClauseSat (assignment c) [118,282,281] := by
    cases ha0 : v59 c <;> cases ha1 : v139 c <;> cases ha2 : v140 c <;> simp [ClauseSat, litVal, assignment_59, assignment_140, assignment_141, v141, ha0, ha1, ha2]
  have hc420 : ClauseSat (assignment c) [118,283,278,280] := by
    cases ha0 : v59 c <;> cases ha1 : v139 c <;> cases ha2 : v140 c <;> simp [ClauseSat, litVal, assignment_59, assignment_139, assignment_140, assignment_141, v141, ha0, ha1, ha2]
  have hc421 : ClauseSat (assignment c) [175,284] := by
    by_cases hs : c.a4.val = 0
    · simp [ClauseSat, litVal, assignment_87, assignment_142, v142, v87, hs]
    · simp [ClauseSat, litVal, assignment_87, assignment_142, v87, hs]
  have hc422 : ClauseSat (assignment c) [177,285] := by
    by_cases hs : c.a4.val = 1
    · simp [ClauseSat, litVal, assignment_88, assignment_142, v142, v88, hs]
    · simp [ClauseSat, litVal, assignment_88, assignment_142, v88, hs]
  have hc423 : ClauseSat (assignment c) [179,285] := by
    by_cases hs : c.a4.val = 2
    · simp [ClauseSat, litVal, assignment_89, assignment_142, v142, v89, hs]
    · simp [ClauseSat, litVal, assignment_89, assignment_142, v89, hs]
  have hc424 : ClauseSat (assignment c) [181,285] := by
    by_cases hs : c.a4.val = 3
    · simp [ClauseSat, litVal, assignment_90, assignment_142, v142, v90, hs]
    · simp [ClauseSat, litVal, assignment_90, assignment_142, v90, hs]
  have hc425 : ClauseSat (assignment c) [183,285,264] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_132, assignment_142, v142, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_132, assignment_142, v91, hs]
  have hc426 : ClauseSat (assignment c) [183,284,265] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_132, assignment_142, v142, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_132, assignment_142, v91, hs]
  have hc427 : ClauseSat (assignment c) [185,285,270] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_135, assignment_142, v142, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_135, assignment_142, v92, hs]
  have hc428 : ClauseSat (assignment c) [185,284,271] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_135, assignment_142, v142, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_135, assignment_142, v92, hs]
  have hc429 : ClauseSat (assignment c) [187,285,276] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_138, assignment_142, v142, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_138, assignment_142, v93, hs]
  have hc430 : ClauseSat (assignment c) [187,284,277] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_138, assignment_142, v142, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_138, assignment_142, v93, hs]
  have hc431 : ClauseSat (assignment c) [189,285,282] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_141, assignment_142, v142, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_141, assignment_142, v94, hs]
  have hc432 : ClauseSat (assignment c) [189,284,283] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_141, assignment_142, v142, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_141, assignment_142, v94, hs]
  have hc433 : ClauseSat (assignment c) [191,286] := by
    by_cases hs : c.b4.val = 0
    · simp [ClauseSat, litVal, assignment_95, assignment_143, v143, v95, hs]
    · simp [ClauseSat, litVal, assignment_95, assignment_143, v95, hs]
  have hc434 : ClauseSat (assignment c) [193,287] := by
    by_cases hs : c.b4.val = 1
    · simp [ClauseSat, litVal, assignment_96, assignment_143, v143, v96, hs]
    · simp [ClauseSat, litVal, assignment_96, assignment_143, v96, hs]
  have hc435 : ClauseSat (assignment c) [195,287] := by
    by_cases hs : c.b4.val = 2
    · simp [ClauseSat, litVal, assignment_97, assignment_143, v143, v97, hs]
    · simp [ClauseSat, litVal, assignment_97, assignment_143, v97, hs]
  have hc436 : ClauseSat (assignment c) [197,287] := by
    by_cases hs : c.b4.val = 3
    · simp [ClauseSat, litVal, assignment_98, assignment_143, v143, v98, hs]
    · simp [ClauseSat, litVal, assignment_98, assignment_143, v98, hs]
  have hc437 : ClauseSat (assignment c) [199,287,264] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_132, assignment_143, v143, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_132, assignment_143, v99, hs]
  have hc438 : ClauseSat (assignment c) [199,286,265] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_132, assignment_143, v143, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_132, assignment_143, v99, hs]
  have hc439 : ClauseSat (assignment c) [201,287,270] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_135, assignment_143, v143, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_135, assignment_143, v100, hs]
  have hc440 : ClauseSat (assignment c) [201,286,271] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_135, assignment_143, v143, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_135, assignment_143, v100, hs]
  have hc441 : ClauseSat (assignment c) [203,287,276] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_138, assignment_143, v143, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_138, assignment_143, v101, hs]
  have hc442 : ClauseSat (assignment c) [203,286,277] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_138, assignment_143, v143, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_138, assignment_143, v101, hs]
  have hc443 : ClauseSat (assignment c) [205,287,282] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_141, assignment_143, v143, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_141, assignment_143, v102, hs]
  have hc444 : ClauseSat (assignment c) [205,286,283] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_141, assignment_143, v143, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_141, assignment_143, v102, hs]
  have hc445 : ClauseSat (assignment c) [173,289,284] := by
    cases ha0 : v86 c <;> cases ha1 : v142 c <;> cases ha2 : v143 c <;> simp [ClauseSat, litVal, assignment_86, assignment_142, assignment_144, v144, ha0, ha1, ha2]
  have hc446 : ClauseSat (assignment c) [173,289,286] := by
    cases ha0 : v86 c <;> cases ha1 : v142 c <;> cases ha2 : v143 c <;> simp [ClauseSat, litVal, assignment_86, assignment_143, assignment_144, v144, ha0, ha1, ha2]
  have hc447 : ClauseSat (assignment c) [173,288,285,287] := by
    cases ha0 : v86 c <;> cases ha1 : v142 c <;> cases ha2 : v143 c <;> simp [ClauseSat, litVal, assignment_86, assignment_142, assignment_143, assignment_144, v144, ha0, ha1, ha2]
  have hc448 : ClauseSat (assignment c) [172,288,285] := by
    cases ha0 : v86 c <;> cases ha1 : v142 c <;> cases ha2 : v143 c <;> simp [ClauseSat, litVal, assignment_86, assignment_142, assignment_144, v144, ha0, ha1, ha2]
  have hc449 : ClauseSat (assignment c) [172,288,287] := by
    cases ha0 : v86 c <;> cases ha1 : v142 c <;> cases ha2 : v143 c <;> simp [ClauseSat, litVal, assignment_86, assignment_143, assignment_144, v144, ha0, ha1, ha2]
  have hc450 : ClauseSat (assignment c) [172,289,284,286] := by
    cases ha0 : v86 c <;> cases ha1 : v142 c <;> cases ha2 : v143 c <;> simp [ClauseSat, litVal, assignment_86, assignment_142, assignment_143, assignment_144, v144, ha0, ha1, ha2]
  have hc451 : ClauseSat (assignment c) [289] := by
    have hh := hr ⟨1, by decide⟩
    have ht : target ⟨1, by decide⟩ = false := by decide
    rw [ht] at hh
    simpa [ClauseSat, litVal, assignment_144, output] using hh
  have hc452 : ClauseSat (assignment c) [7,291] := by
    by_cases hs : c.a0.val = 0
    · simp [ClauseSat, litVal, assignment_3, assignment_145, v145, v3, hs]
    · simp [ClauseSat, litVal, assignment_3, assignment_145, v3, hs]
  have hc453 : ClauseSat (assignment c) [9,290] := by
    by_cases hs : c.a0.val = 1
    · simp [ClauseSat, litVal, assignment_4, assignment_145, v145, v4, hs]
    · simp [ClauseSat, litVal, assignment_4, assignment_145, v4, hs]
  have hc454 : ClauseSat (assignment c) [11,291] := by
    by_cases hs : c.a0.val = 2
    · simp [ClauseSat, litVal, assignment_5, assignment_145, v145, v5, hs]
    · simp [ClauseSat, litVal, assignment_5, assignment_145, v5, hs]
  have hc455 : ClauseSat (assignment c) [13,291] := by
    by_cases hs : c.a0.val = 3
    · simp [ClauseSat, litVal, assignment_6, assignment_145, v145, v6, hs]
    · simp [ClauseSat, litVal, assignment_6, assignment_145, v6, hs]
  have hc456 : ClauseSat (assignment c) [15,293] := by
    by_cases hs : c.b0.val = 0
    · simp [ClauseSat, litVal, assignment_7, assignment_146, v146, v7, hs]
    · simp [ClauseSat, litVal, assignment_7, assignment_146, v7, hs]
  have hc457 : ClauseSat (assignment c) [17,292] := by
    by_cases hs : c.b0.val = 1
    · simp [ClauseSat, litVal, assignment_8, assignment_146, v146, v8, hs]
    · simp [ClauseSat, litVal, assignment_8, assignment_146, v8, hs]
  have hc458 : ClauseSat (assignment c) [19,293] := by
    by_cases hs : c.b0.val = 2
    · simp [ClauseSat, litVal, assignment_9, assignment_146, v146, v9, hs]
    · simp [ClauseSat, litVal, assignment_9, assignment_146, v9, hs]
  have hc459 : ClauseSat (assignment c) [21,293] := by
    by_cases hs : c.b0.val = 3
    · simp [ClauseSat, litVal, assignment_10, assignment_146, v146, v10, hs]
    · simp [ClauseSat, litVal, assignment_10, assignment_146, v10, hs]
  have hc460 : ClauseSat (assignment c) [5,295,290] := by
    cases ha0 : v2 c <;> cases ha1 : v145 c <;> cases ha2 : v146 c <;> simp [ClauseSat, litVal, assignment_2, assignment_145, assignment_147, v147, ha0, ha1, ha2]
  have hc461 : ClauseSat (assignment c) [5,295,292] := by
    cases ha0 : v2 c <;> cases ha1 : v145 c <;> cases ha2 : v146 c <;> simp [ClauseSat, litVal, assignment_2, assignment_146, assignment_147, v147, ha0, ha1, ha2]
  have hc462 : ClauseSat (assignment c) [5,294,291,293] := by
    cases ha0 : v2 c <;> cases ha1 : v145 c <;> cases ha2 : v146 c <;> simp [ClauseSat, litVal, assignment_2, assignment_145, assignment_146, assignment_147, v147, ha0, ha1, ha2]
  have hc463 : ClauseSat (assignment c) [4,294,291] := by
    cases ha0 : v2 c <;> cases ha1 : v145 c <;> cases ha2 : v146 c <;> simp [ClauseSat, litVal, assignment_2, assignment_145, assignment_147, v147, ha0, ha1, ha2]
  have hc464 : ClauseSat (assignment c) [4,294,293] := by
    cases ha0 : v2 c <;> cases ha1 : v145 c <;> cases ha2 : v146 c <;> simp [ClauseSat, litVal, assignment_2, assignment_146, assignment_147, v147, ha0, ha1, ha2]
  have hc465 : ClauseSat (assignment c) [4,295,290,292] := by
    cases ha0 : v2 c <;> cases ha1 : v145 c <;> cases ha2 : v146 c <;> simp [ClauseSat, litVal, assignment_2, assignment_145, assignment_146, assignment_147, v147, ha0, ha1, ha2]
  have hc466 : ClauseSat (assignment c) [37,297] := by
    by_cases hs : c.a1.val = 0
    · simp [ClauseSat, litVal, assignment_18, assignment_148, v148, v18, hs]
    · simp [ClauseSat, litVal, assignment_18, assignment_148, v18, hs]
  have hc467 : ClauseSat (assignment c) [39,296] := by
    by_cases hs : c.a1.val = 1
    · simp [ClauseSat, litVal, assignment_19, assignment_148, v148, v19, hs]
    · simp [ClauseSat, litVal, assignment_19, assignment_148, v19, hs]
  have hc468 : ClauseSat (assignment c) [41,297] := by
    by_cases hs : c.a1.val = 2
    · simp [ClauseSat, litVal, assignment_20, assignment_148, v148, v20, hs]
    · simp [ClauseSat, litVal, assignment_20, assignment_148, v20, hs]
  have hc469 : ClauseSat (assignment c) [43,297] := by
    by_cases hs : c.a1.val = 3
    · simp [ClauseSat, litVal, assignment_21, assignment_148, v148, v21, hs]
    · simp [ClauseSat, litVal, assignment_21, assignment_148, v21, hs]
  have hc470 : ClauseSat (assignment c) [45,297,294] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_147, assignment_148, v148, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_147, assignment_148, v22, hs]
  have hc471 : ClauseSat (assignment c) [45,296,295] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_147, assignment_148, v148, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_147, assignment_148, v22, hs]
  have hc472 : ClauseSat (assignment c) [47,299] := by
    by_cases hs : c.b1.val = 0
    · simp [ClauseSat, litVal, assignment_23, assignment_149, v149, v23, hs]
    · simp [ClauseSat, litVal, assignment_23, assignment_149, v23, hs]
  have hc473 : ClauseSat (assignment c) [49,298] := by
    by_cases hs : c.b1.val = 1
    · simp [ClauseSat, litVal, assignment_24, assignment_149, v149, v24, hs]
    · simp [ClauseSat, litVal, assignment_24, assignment_149, v24, hs]
  have hc474 : ClauseSat (assignment c) [51,299] := by
    by_cases hs : c.b1.val = 2
    · simp [ClauseSat, litVal, assignment_25, assignment_149, v149, v25, hs]
    · simp [ClauseSat, litVal, assignment_25, assignment_149, v25, hs]
  have hc475 : ClauseSat (assignment c) [53,299] := by
    by_cases hs : c.b1.val = 3
    · simp [ClauseSat, litVal, assignment_26, assignment_149, v149, v26, hs]
    · simp [ClauseSat, litVal, assignment_26, assignment_149, v26, hs]
  have hc476 : ClauseSat (assignment c) [55,299,294] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_147, assignment_149, v149, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_147, assignment_149, v27, hs]
  have hc477 : ClauseSat (assignment c) [55,298,295] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_147, assignment_149, v149, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_147, assignment_149, v27, hs]
  have hc478 : ClauseSat (assignment c) [35,301,296] := by
    cases ha0 : v17 c <;> cases ha1 : v148 c <;> cases ha2 : v149 c <;> simp [ClauseSat, litVal, assignment_17, assignment_148, assignment_150, v150, ha0, ha1, ha2]
  have hc479 : ClauseSat (assignment c) [35,301,298] := by
    cases ha0 : v17 c <;> cases ha1 : v148 c <;> cases ha2 : v149 c <;> simp [ClauseSat, litVal, assignment_17, assignment_149, assignment_150, v150, ha0, ha1, ha2]
  have hc480 : ClauseSat (assignment c) [35,300,297,299] := by
    cases ha0 : v17 c <;> cases ha1 : v148 c <;> cases ha2 : v149 c <;> simp [ClauseSat, litVal, assignment_17, assignment_148, assignment_149, assignment_150, v150, ha0, ha1, ha2]
  have hc481 : ClauseSat (assignment c) [34,300,297] := by
    cases ha0 : v17 c <;> cases ha1 : v148 c <;> cases ha2 : v149 c <;> simp [ClauseSat, litVal, assignment_17, assignment_148, assignment_150, v150, ha0, ha1, ha2]
  have hc482 : ClauseSat (assignment c) [34,300,299] := by
    cases ha0 : v17 c <;> cases ha1 : v148 c <;> cases ha2 : v149 c <;> simp [ClauseSat, litVal, assignment_17, assignment_149, assignment_150, v150, ha0, ha1, ha2]
  have hc483 : ClauseSat (assignment c) [34,301,296,298] := by
    cases ha0 : v17 c <;> cases ha1 : v148 c <;> cases ha2 : v149 c <;> simp [ClauseSat, litVal, assignment_17, assignment_148, assignment_149, assignment_150, v150, ha0, ha1, ha2]
  have hc484 : ClauseSat (assignment c) [75,303] := by
    by_cases hs : c.a2.val = 0
    · simp [ClauseSat, litVal, assignment_37, assignment_151, v151, v37, hs]
    · simp [ClauseSat, litVal, assignment_37, assignment_151, v37, hs]
  have hc485 : ClauseSat (assignment c) [77,302] := by
    by_cases hs : c.a2.val = 1
    · simp [ClauseSat, litVal, assignment_38, assignment_151, v151, v38, hs]
    · simp [ClauseSat, litVal, assignment_38, assignment_151, v38, hs]
  have hc486 : ClauseSat (assignment c) [79,303] := by
    by_cases hs : c.a2.val = 2
    · simp [ClauseSat, litVal, assignment_39, assignment_151, v151, v39, hs]
    · simp [ClauseSat, litVal, assignment_39, assignment_151, v39, hs]
  have hc487 : ClauseSat (assignment c) [81,303] := by
    by_cases hs : c.a2.val = 3
    · simp [ClauseSat, litVal, assignment_40, assignment_151, v151, v40, hs]
    · simp [ClauseSat, litVal, assignment_40, assignment_151, v40, hs]
  have hc488 : ClauseSat (assignment c) [83,303,294] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_147, assignment_151, v151, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_147, assignment_151, v41, hs]
  have hc489 : ClauseSat (assignment c) [83,302,295] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_147, assignment_151, v151, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_147, assignment_151, v41, hs]
  have hc490 : ClauseSat (assignment c) [85,303,300] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_150, assignment_151, v151, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_150, assignment_151, v42, hs]
  have hc491 : ClauseSat (assignment c) [85,302,301] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_150, assignment_151, v151, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_150, assignment_151, v42, hs]
  have hc492 : ClauseSat (assignment c) [87,305] := by
    by_cases hs : c.b2.val = 0
    · simp [ClauseSat, litVal, assignment_43, assignment_152, v152, v43, hs]
    · simp [ClauseSat, litVal, assignment_43, assignment_152, v43, hs]
  have hc493 : ClauseSat (assignment c) [89,304] := by
    by_cases hs : c.b2.val = 1
    · simp [ClauseSat, litVal, assignment_44, assignment_152, v152, v44, hs]
    · simp [ClauseSat, litVal, assignment_44, assignment_152, v44, hs]
  have hc494 : ClauseSat (assignment c) [91,305] := by
    by_cases hs : c.b2.val = 2
    · simp [ClauseSat, litVal, assignment_45, assignment_152, v152, v45, hs]
    · simp [ClauseSat, litVal, assignment_45, assignment_152, v45, hs]
  have hc495 : ClauseSat (assignment c) [93,305] := by
    by_cases hs : c.b2.val = 3
    · simp [ClauseSat, litVal, assignment_46, assignment_152, v152, v46, hs]
    · simp [ClauseSat, litVal, assignment_46, assignment_152, v46, hs]
  have hc496 : ClauseSat (assignment c) [95,305,294] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_147, assignment_152, v152, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_147, assignment_152, v47, hs]
  have hc497 : ClauseSat (assignment c) [95,304,295] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_147, assignment_152, v152, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_147, assignment_152, v47, hs]
  have hc498 : ClauseSat (assignment c) [97,305,300] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_150, assignment_152, v152, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_150, assignment_152, v48, hs]
  have hc499 : ClauseSat (assignment c) [97,304,301] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_150, assignment_152, v152, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_150, assignment_152, v48, hs]
  simp only [chunk4, List.forall_mem_cons]
  exact ⟨hc400, hc401, hc402, hc403, hc404, hc405, hc406, hc407, hc408, hc409, hc410, hc411, hc412, hc413, hc414, hc415, hc416, hc417, hc418, hc419, hc420, hc421, hc422, hc423, hc424, hc425, hc426, hc427, hc428, hc429, hc430, hc431, hc432, hc433, hc434, hc435, hc436, hc437, hc438, hc439, hc440, hc441, hc442, hc443, hc444, hc445, hc446, hc447, hc448, hc449, hc450, hc451, hc452, hc453, hc454, hc455, hc456, hc457, hc458, hc459, hc460, hc461, hc462, hc463, hc464, hc465, hc466, hc467, hc468, hc469, hc470, hc471, hc472, hc473, hc474, hc475, hc476, hc477, hc478, hc479, hc480, hc481, hc482, hc483, hc484, hc485, hc486, hc487, hc488, hc489, hc490, hc491, hc492, hc493, hc494, hc495, hc496, hc497, hc498, hc499, by simp⟩
#check satChunk4

def chunk5 : List (List Nat) := [[73, 307, 302], [73, 307, 304], [73, 306, 303, 305], [72, 306, 303], [72, 306, 305], [72, 307, 302, 304], [121, 309], [123, 308], [125, 309], [127, 309], [129, 309, 294], [129, 308, 295], [131, 309, 300], [131, 308, 301], [133, 309, 306], [133, 308, 307], [135, 311], [137, 310], [139, 311], [141, 311], [143, 311, 294], [143, 310, 295], [145, 311, 300], [145, 310, 301], [147, 311, 306], [147, 310, 307], [119, 313, 308], [119, 313, 310], [119, 312, 309, 311], [118, 312, 309], [118, 312, 311], [118, 313, 308, 310], [175, 315], [177, 314], [179, 315], [181, 315], [183, 315, 294], [183, 314, 295], [185, 315, 300], [185, 314, 301], [187, 315, 306], [187, 314, 307], [189, 315, 312], [189, 314, 313], [191, 317], [193, 316], [195, 317], [197, 317], [199, 317, 294], [199, 316, 295], [201, 317, 300], [201, 316, 301], [203, 317, 306], [203, 316, 307], [205, 317, 312], [205, 316, 313], [173, 319, 314], [173, 319, 316], [173, 318, 315, 317], [172, 318, 315], [172, 318, 317], [172, 319, 314, 316], [319], [7, 320], [9, 320], [11, 321], [13, 321], [15, 322], [17, 322], [19, 323], [21, 323], [5, 325, 320], [5, 325, 322], [5, 324, 321, 323], [4, 324, 321], [4, 324, 323], [4, 325, 320, 322], [37, 326], [39, 326], [41, 327], [43, 327], [45, 327, 324], [45, 326, 325], [47, 328], [49, 328], [51, 329], [53, 329], [55, 329, 324], [55, 328, 325], [35, 331, 326], [35, 331, 328], [35, 330, 327, 329], [34, 330, 327], [34, 330, 329], [34, 331, 326, 328], [75, 332], [77, 332], [79, 333], [81, 333], [83, 333, 324]]
theorem satChunk5 (c : Candidate) (hv : valid c)
    (hr : ∀ r : Fin 16, output c r = target r)
    (hl : derivativeLeft c = false) (hd : derivativeRight c = false) :
    ∀ cl ∈ chunk5, ClauseSat (assignment c) cl := by
  rcases hv with ⟨h0, h1, h2, h3, h4⟩
  have hc500 : ClauseSat (assignment c) [73,307,302] := by
    cases ha0 : v36 c <;> cases ha1 : v151 c <;> cases ha2 : v152 c <;> simp [ClauseSat, litVal, assignment_36, assignment_151, assignment_153, v153, ha0, ha1, ha2]
  have hc501 : ClauseSat (assignment c) [73,307,304] := by
    cases ha0 : v36 c <;> cases ha1 : v151 c <;> cases ha2 : v152 c <;> simp [ClauseSat, litVal, assignment_36, assignment_152, assignment_153, v153, ha0, ha1, ha2]
  have hc502 : ClauseSat (assignment c) [73,306,303,305] := by
    cases ha0 : v36 c <;> cases ha1 : v151 c <;> cases ha2 : v152 c <;> simp [ClauseSat, litVal, assignment_36, assignment_151, assignment_152, assignment_153, v153, ha0, ha1, ha2]
  have hc503 : ClauseSat (assignment c) [72,306,303] := by
    cases ha0 : v36 c <;> cases ha1 : v151 c <;> cases ha2 : v152 c <;> simp [ClauseSat, litVal, assignment_36, assignment_151, assignment_153, v153, ha0, ha1, ha2]
  have hc504 : ClauseSat (assignment c) [72,306,305] := by
    cases ha0 : v36 c <;> cases ha1 : v151 c <;> cases ha2 : v152 c <;> simp [ClauseSat, litVal, assignment_36, assignment_152, assignment_153, v153, ha0, ha1, ha2]
  have hc505 : ClauseSat (assignment c) [72,307,302,304] := by
    cases ha0 : v36 c <;> cases ha1 : v151 c <;> cases ha2 : v152 c <;> simp [ClauseSat, litVal, assignment_36, assignment_151, assignment_152, assignment_153, v153, ha0, ha1, ha2]
  have hc506 : ClauseSat (assignment c) [121,309] := by
    by_cases hs : c.a3.val = 0
    · simp [ClauseSat, litVal, assignment_60, assignment_154, v154, v60, hs]
    · simp [ClauseSat, litVal, assignment_60, assignment_154, v60, hs]
  have hc507 : ClauseSat (assignment c) [123,308] := by
    by_cases hs : c.a3.val = 1
    · simp [ClauseSat, litVal, assignment_61, assignment_154, v154, v61, hs]
    · simp [ClauseSat, litVal, assignment_61, assignment_154, v61, hs]
  have hc508 : ClauseSat (assignment c) [125,309] := by
    by_cases hs : c.a3.val = 2
    · simp [ClauseSat, litVal, assignment_62, assignment_154, v154, v62, hs]
    · simp [ClauseSat, litVal, assignment_62, assignment_154, v62, hs]
  have hc509 : ClauseSat (assignment c) [127,309] := by
    by_cases hs : c.a3.val = 3
    · simp [ClauseSat, litVal, assignment_63, assignment_154, v154, v63, hs]
    · simp [ClauseSat, litVal, assignment_63, assignment_154, v63, hs]
  have hc510 : ClauseSat (assignment c) [129,309,294] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_147, assignment_154, v154, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_147, assignment_154, v64, hs]
  have hc511 : ClauseSat (assignment c) [129,308,295] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_147, assignment_154, v154, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_147, assignment_154, v64, hs]
  have hc512 : ClauseSat (assignment c) [131,309,300] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_150, assignment_154, v154, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_150, assignment_154, v65, hs]
  have hc513 : ClauseSat (assignment c) [131,308,301] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_150, assignment_154, v154, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_150, assignment_154, v65, hs]
  have hc514 : ClauseSat (assignment c) [133,309,306] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_153, assignment_154, v154, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_153, assignment_154, v66, hs]
  have hc515 : ClauseSat (assignment c) [133,308,307] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_153, assignment_154, v154, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_153, assignment_154, v66, hs]
  have hc516 : ClauseSat (assignment c) [135,311] := by
    by_cases hs : c.b3.val = 0
    · simp [ClauseSat, litVal, assignment_67, assignment_155, v155, v67, hs]
    · simp [ClauseSat, litVal, assignment_67, assignment_155, v67, hs]
  have hc517 : ClauseSat (assignment c) [137,310] := by
    by_cases hs : c.b3.val = 1
    · simp [ClauseSat, litVal, assignment_68, assignment_155, v155, v68, hs]
    · simp [ClauseSat, litVal, assignment_68, assignment_155, v68, hs]
  have hc518 : ClauseSat (assignment c) [139,311] := by
    by_cases hs : c.b3.val = 2
    · simp [ClauseSat, litVal, assignment_69, assignment_155, v155, v69, hs]
    · simp [ClauseSat, litVal, assignment_69, assignment_155, v69, hs]
  have hc519 : ClauseSat (assignment c) [141,311] := by
    by_cases hs : c.b3.val = 3
    · simp [ClauseSat, litVal, assignment_70, assignment_155, v155, v70, hs]
    · simp [ClauseSat, litVal, assignment_70, assignment_155, v70, hs]
  have hc520 : ClauseSat (assignment c) [143,311,294] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_147, assignment_155, v155, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_147, assignment_155, v71, hs]
  have hc521 : ClauseSat (assignment c) [143,310,295] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_147, assignment_155, v155, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_147, assignment_155, v71, hs]
  have hc522 : ClauseSat (assignment c) [145,311,300] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_150, assignment_155, v155, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_150, assignment_155, v72, hs]
  have hc523 : ClauseSat (assignment c) [145,310,301] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_150, assignment_155, v155, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_150, assignment_155, v72, hs]
  have hc524 : ClauseSat (assignment c) [147,311,306] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_153, assignment_155, v155, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_153, assignment_155, v73, hs]
  have hc525 : ClauseSat (assignment c) [147,310,307] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_153, assignment_155, v155, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_153, assignment_155, v73, hs]
  have hc526 : ClauseSat (assignment c) [119,313,308] := by
    cases ha0 : v59 c <;> cases ha1 : v154 c <;> cases ha2 : v155 c <;> simp [ClauseSat, litVal, assignment_59, assignment_154, assignment_156, v156, ha0, ha1, ha2]
  have hc527 : ClauseSat (assignment c) [119,313,310] := by
    cases ha0 : v59 c <;> cases ha1 : v154 c <;> cases ha2 : v155 c <;> simp [ClauseSat, litVal, assignment_59, assignment_155, assignment_156, v156, ha0, ha1, ha2]
  have hc528 : ClauseSat (assignment c) [119,312,309,311] := by
    cases ha0 : v59 c <;> cases ha1 : v154 c <;> cases ha2 : v155 c <;> simp [ClauseSat, litVal, assignment_59, assignment_154, assignment_155, assignment_156, v156, ha0, ha1, ha2]
  have hc529 : ClauseSat (assignment c) [118,312,309] := by
    cases ha0 : v59 c <;> cases ha1 : v154 c <;> cases ha2 : v155 c <;> simp [ClauseSat, litVal, assignment_59, assignment_154, assignment_156, v156, ha0, ha1, ha2]
  have hc530 : ClauseSat (assignment c) [118,312,311] := by
    cases ha0 : v59 c <;> cases ha1 : v154 c <;> cases ha2 : v155 c <;> simp [ClauseSat, litVal, assignment_59, assignment_155, assignment_156, v156, ha0, ha1, ha2]
  have hc531 : ClauseSat (assignment c) [118,313,308,310] := by
    cases ha0 : v59 c <;> cases ha1 : v154 c <;> cases ha2 : v155 c <;> simp [ClauseSat, litVal, assignment_59, assignment_154, assignment_155, assignment_156, v156, ha0, ha1, ha2]
  have hc532 : ClauseSat (assignment c) [175,315] := by
    by_cases hs : c.a4.val = 0
    · simp [ClauseSat, litVal, assignment_87, assignment_157, v157, v87, hs]
    · simp [ClauseSat, litVal, assignment_87, assignment_157, v87, hs]
  have hc533 : ClauseSat (assignment c) [177,314] := by
    by_cases hs : c.a4.val = 1
    · simp [ClauseSat, litVal, assignment_88, assignment_157, v157, v88, hs]
    · simp [ClauseSat, litVal, assignment_88, assignment_157, v88, hs]
  have hc534 : ClauseSat (assignment c) [179,315] := by
    by_cases hs : c.a4.val = 2
    · simp [ClauseSat, litVal, assignment_89, assignment_157, v157, v89, hs]
    · simp [ClauseSat, litVal, assignment_89, assignment_157, v89, hs]
  have hc535 : ClauseSat (assignment c) [181,315] := by
    by_cases hs : c.a4.val = 3
    · simp [ClauseSat, litVal, assignment_90, assignment_157, v157, v90, hs]
    · simp [ClauseSat, litVal, assignment_90, assignment_157, v90, hs]
  have hc536 : ClauseSat (assignment c) [183,315,294] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_147, assignment_157, v157, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_147, assignment_157, v91, hs]
  have hc537 : ClauseSat (assignment c) [183,314,295] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_147, assignment_157, v157, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_147, assignment_157, v91, hs]
  have hc538 : ClauseSat (assignment c) [185,315,300] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_150, assignment_157, v157, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_150, assignment_157, v92, hs]
  have hc539 : ClauseSat (assignment c) [185,314,301] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_150, assignment_157, v157, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_150, assignment_157, v92, hs]
  have hc540 : ClauseSat (assignment c) [187,315,306] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_153, assignment_157, v157, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_153, assignment_157, v93, hs]
  have hc541 : ClauseSat (assignment c) [187,314,307] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_153, assignment_157, v157, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_153, assignment_157, v93, hs]
  have hc542 : ClauseSat (assignment c) [189,315,312] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_156, assignment_157, v157, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_156, assignment_157, v94, hs]
  have hc543 : ClauseSat (assignment c) [189,314,313] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_156, assignment_157, v157, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_156, assignment_157, v94, hs]
  have hc544 : ClauseSat (assignment c) [191,317] := by
    by_cases hs : c.b4.val = 0
    · simp [ClauseSat, litVal, assignment_95, assignment_158, v158, v95, hs]
    · simp [ClauseSat, litVal, assignment_95, assignment_158, v95, hs]
  have hc545 : ClauseSat (assignment c) [193,316] := by
    by_cases hs : c.b4.val = 1
    · simp [ClauseSat, litVal, assignment_96, assignment_158, v158, v96, hs]
    · simp [ClauseSat, litVal, assignment_96, assignment_158, v96, hs]
  have hc546 : ClauseSat (assignment c) [195,317] := by
    by_cases hs : c.b4.val = 2
    · simp [ClauseSat, litVal, assignment_97, assignment_158, v158, v97, hs]
    · simp [ClauseSat, litVal, assignment_97, assignment_158, v97, hs]
  have hc547 : ClauseSat (assignment c) [197,317] := by
    by_cases hs : c.b4.val = 3
    · simp [ClauseSat, litVal, assignment_98, assignment_158, v158, v98, hs]
    · simp [ClauseSat, litVal, assignment_98, assignment_158, v98, hs]
  have hc548 : ClauseSat (assignment c) [199,317,294] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_147, assignment_158, v158, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_147, assignment_158, v99, hs]
  have hc549 : ClauseSat (assignment c) [199,316,295] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_147, assignment_158, v158, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_147, assignment_158, v99, hs]
  have hc550 : ClauseSat (assignment c) [201,317,300] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_150, assignment_158, v158, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_150, assignment_158, v100, hs]
  have hc551 : ClauseSat (assignment c) [201,316,301] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_150, assignment_158, v158, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_150, assignment_158, v100, hs]
  have hc552 : ClauseSat (assignment c) [203,317,306] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_153, assignment_158, v158, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_153, assignment_158, v101, hs]
  have hc553 : ClauseSat (assignment c) [203,316,307] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_153, assignment_158, v158, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_153, assignment_158, v101, hs]
  have hc554 : ClauseSat (assignment c) [205,317,312] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_156, assignment_158, v158, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_156, assignment_158, v102, hs]
  have hc555 : ClauseSat (assignment c) [205,316,313] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_156, assignment_158, v158, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_156, assignment_158, v102, hs]
  have hc556 : ClauseSat (assignment c) [173,319,314] := by
    cases ha0 : v86 c <;> cases ha1 : v157 c <;> cases ha2 : v158 c <;> simp [ClauseSat, litVal, assignment_86, assignment_157, assignment_159, v159, ha0, ha1, ha2]
  have hc557 : ClauseSat (assignment c) [173,319,316] := by
    cases ha0 : v86 c <;> cases ha1 : v157 c <;> cases ha2 : v158 c <;> simp [ClauseSat, litVal, assignment_86, assignment_158, assignment_159, v159, ha0, ha1, ha2]
  have hc558 : ClauseSat (assignment c) [173,318,315,317] := by
    cases ha0 : v86 c <;> cases ha1 : v157 c <;> cases ha2 : v158 c <;> simp [ClauseSat, litVal, assignment_86, assignment_157, assignment_158, assignment_159, v159, ha0, ha1, ha2]
  have hc559 : ClauseSat (assignment c) [172,318,315] := by
    cases ha0 : v86 c <;> cases ha1 : v157 c <;> cases ha2 : v158 c <;> simp [ClauseSat, litVal, assignment_86, assignment_157, assignment_159, v159, ha0, ha1, ha2]
  have hc560 : ClauseSat (assignment c) [172,318,317] := by
    cases ha0 : v86 c <;> cases ha1 : v157 c <;> cases ha2 : v158 c <;> simp [ClauseSat, litVal, assignment_86, assignment_158, assignment_159, v159, ha0, ha1, ha2]
  have hc561 : ClauseSat (assignment c) [172,319,314,316] := by
    cases ha0 : v86 c <;> cases ha1 : v157 c <;> cases ha2 : v158 c <;> simp [ClauseSat, litVal, assignment_86, assignment_157, assignment_158, assignment_159, v159, ha0, ha1, ha2]
  have hc562 : ClauseSat (assignment c) [319] := by
    have hh := hr ⟨2, by decide⟩
    have ht : target ⟨2, by decide⟩ = false := by decide
    rw [ht] at hh
    simpa [ClauseSat, litVal, assignment_159, output] using hh
  have hc563 : ClauseSat (assignment c) [7,320] := by
    by_cases hs : c.a0.val = 0
    · simp [ClauseSat, litVal, assignment_3, assignment_160, v160, v3, hs]
    · simp [ClauseSat, litVal, assignment_3, assignment_160, v3, hs]
  have hc564 : ClauseSat (assignment c) [9,320] := by
    by_cases hs : c.a0.val = 1
    · simp [ClauseSat, litVal, assignment_4, assignment_160, v160, v4, hs]
    · simp [ClauseSat, litVal, assignment_4, assignment_160, v4, hs]
  have hc565 : ClauseSat (assignment c) [11,321] := by
    by_cases hs : c.a0.val = 2
    · simp [ClauseSat, litVal, assignment_5, assignment_160, v160, v5, hs]
    · simp [ClauseSat, litVal, assignment_5, assignment_160, v5, hs]
  have hc566 : ClauseSat (assignment c) [13,321] := by
    by_cases hs : c.a0.val = 3
    · simp [ClauseSat, litVal, assignment_6, assignment_160, v160, v6, hs]
    · simp [ClauseSat, litVal, assignment_6, assignment_160, v6, hs]
  have hc567 : ClauseSat (assignment c) [15,322] := by
    by_cases hs : c.b0.val = 0
    · simp [ClauseSat, litVal, assignment_7, assignment_161, v161, v7, hs]
    · simp [ClauseSat, litVal, assignment_7, assignment_161, v7, hs]
  have hc568 : ClauseSat (assignment c) [17,322] := by
    by_cases hs : c.b0.val = 1
    · simp [ClauseSat, litVal, assignment_8, assignment_161, v161, v8, hs]
    · simp [ClauseSat, litVal, assignment_8, assignment_161, v8, hs]
  have hc569 : ClauseSat (assignment c) [19,323] := by
    by_cases hs : c.b0.val = 2
    · simp [ClauseSat, litVal, assignment_9, assignment_161, v161, v9, hs]
    · simp [ClauseSat, litVal, assignment_9, assignment_161, v9, hs]
  have hc570 : ClauseSat (assignment c) [21,323] := by
    by_cases hs : c.b0.val = 3
    · simp [ClauseSat, litVal, assignment_10, assignment_161, v161, v10, hs]
    · simp [ClauseSat, litVal, assignment_10, assignment_161, v10, hs]
  have hc571 : ClauseSat (assignment c) [5,325,320] := by
    cases ha0 : v2 c <;> cases ha1 : v160 c <;> cases ha2 : v161 c <;> simp [ClauseSat, litVal, assignment_2, assignment_160, assignment_162, v162, ha0, ha1, ha2]
  have hc572 : ClauseSat (assignment c) [5,325,322] := by
    cases ha0 : v2 c <;> cases ha1 : v160 c <;> cases ha2 : v161 c <;> simp [ClauseSat, litVal, assignment_2, assignment_161, assignment_162, v162, ha0, ha1, ha2]
  have hc573 : ClauseSat (assignment c) [5,324,321,323] := by
    cases ha0 : v2 c <;> cases ha1 : v160 c <;> cases ha2 : v161 c <;> simp [ClauseSat, litVal, assignment_2, assignment_160, assignment_161, assignment_162, v162, ha0, ha1, ha2]
  have hc574 : ClauseSat (assignment c) [4,324,321] := by
    cases ha0 : v2 c <;> cases ha1 : v160 c <;> cases ha2 : v161 c <;> simp [ClauseSat, litVal, assignment_2, assignment_160, assignment_162, v162, ha0, ha1, ha2]
  have hc575 : ClauseSat (assignment c) [4,324,323] := by
    cases ha0 : v2 c <;> cases ha1 : v160 c <;> cases ha2 : v161 c <;> simp [ClauseSat, litVal, assignment_2, assignment_161, assignment_162, v162, ha0, ha1, ha2]
  have hc576 : ClauseSat (assignment c) [4,325,320,322] := by
    cases ha0 : v2 c <;> cases ha1 : v160 c <;> cases ha2 : v161 c <;> simp [ClauseSat, litVal, assignment_2, assignment_160, assignment_161, assignment_162, v162, ha0, ha1, ha2]
  have hc577 : ClauseSat (assignment c) [37,326] := by
    by_cases hs : c.a1.val = 0
    · simp [ClauseSat, litVal, assignment_18, assignment_163, v163, v18, hs]
    · simp [ClauseSat, litVal, assignment_18, assignment_163, v18, hs]
  have hc578 : ClauseSat (assignment c) [39,326] := by
    by_cases hs : c.a1.val = 1
    · simp [ClauseSat, litVal, assignment_19, assignment_163, v163, v19, hs]
    · simp [ClauseSat, litVal, assignment_19, assignment_163, v19, hs]
  have hc579 : ClauseSat (assignment c) [41,327] := by
    by_cases hs : c.a1.val = 2
    · simp [ClauseSat, litVal, assignment_20, assignment_163, v163, v20, hs]
    · simp [ClauseSat, litVal, assignment_20, assignment_163, v20, hs]
  have hc580 : ClauseSat (assignment c) [43,327] := by
    by_cases hs : c.a1.val = 3
    · simp [ClauseSat, litVal, assignment_21, assignment_163, v163, v21, hs]
    · simp [ClauseSat, litVal, assignment_21, assignment_163, v21, hs]
  have hc581 : ClauseSat (assignment c) [45,327,324] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_162, assignment_163, v163, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_162, assignment_163, v22, hs]
  have hc582 : ClauseSat (assignment c) [45,326,325] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_162, assignment_163, v163, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_162, assignment_163, v22, hs]
  have hc583 : ClauseSat (assignment c) [47,328] := by
    by_cases hs : c.b1.val = 0
    · simp [ClauseSat, litVal, assignment_23, assignment_164, v164, v23, hs]
    · simp [ClauseSat, litVal, assignment_23, assignment_164, v23, hs]
  have hc584 : ClauseSat (assignment c) [49,328] := by
    by_cases hs : c.b1.val = 1
    · simp [ClauseSat, litVal, assignment_24, assignment_164, v164, v24, hs]
    · simp [ClauseSat, litVal, assignment_24, assignment_164, v24, hs]
  have hc585 : ClauseSat (assignment c) [51,329] := by
    by_cases hs : c.b1.val = 2
    · simp [ClauseSat, litVal, assignment_25, assignment_164, v164, v25, hs]
    · simp [ClauseSat, litVal, assignment_25, assignment_164, v25, hs]
  have hc586 : ClauseSat (assignment c) [53,329] := by
    by_cases hs : c.b1.val = 3
    · simp [ClauseSat, litVal, assignment_26, assignment_164, v164, v26, hs]
    · simp [ClauseSat, litVal, assignment_26, assignment_164, v26, hs]
  have hc587 : ClauseSat (assignment c) [55,329,324] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_162, assignment_164, v164, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_162, assignment_164, v27, hs]
  have hc588 : ClauseSat (assignment c) [55,328,325] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_162, assignment_164, v164, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_162, assignment_164, v27, hs]
  have hc589 : ClauseSat (assignment c) [35,331,326] := by
    cases ha0 : v17 c <;> cases ha1 : v163 c <;> cases ha2 : v164 c <;> simp [ClauseSat, litVal, assignment_17, assignment_163, assignment_165, v165, ha0, ha1, ha2]
  have hc590 : ClauseSat (assignment c) [35,331,328] := by
    cases ha0 : v17 c <;> cases ha1 : v163 c <;> cases ha2 : v164 c <;> simp [ClauseSat, litVal, assignment_17, assignment_164, assignment_165, v165, ha0, ha1, ha2]
  have hc591 : ClauseSat (assignment c) [35,330,327,329] := by
    cases ha0 : v17 c <;> cases ha1 : v163 c <;> cases ha2 : v164 c <;> simp [ClauseSat, litVal, assignment_17, assignment_163, assignment_164, assignment_165, v165, ha0, ha1, ha2]
  have hc592 : ClauseSat (assignment c) [34,330,327] := by
    cases ha0 : v17 c <;> cases ha1 : v163 c <;> cases ha2 : v164 c <;> simp [ClauseSat, litVal, assignment_17, assignment_163, assignment_165, v165, ha0, ha1, ha2]
  have hc593 : ClauseSat (assignment c) [34,330,329] := by
    cases ha0 : v17 c <;> cases ha1 : v163 c <;> cases ha2 : v164 c <;> simp [ClauseSat, litVal, assignment_17, assignment_164, assignment_165, v165, ha0, ha1, ha2]
  have hc594 : ClauseSat (assignment c) [34,331,326,328] := by
    cases ha0 : v17 c <;> cases ha1 : v163 c <;> cases ha2 : v164 c <;> simp [ClauseSat, litVal, assignment_17, assignment_163, assignment_164, assignment_165, v165, ha0, ha1, ha2]
  have hc595 : ClauseSat (assignment c) [75,332] := by
    by_cases hs : c.a2.val = 0
    · simp [ClauseSat, litVal, assignment_37, assignment_166, v166, v37, hs]
    · simp [ClauseSat, litVal, assignment_37, assignment_166, v37, hs]
  have hc596 : ClauseSat (assignment c) [77,332] := by
    by_cases hs : c.a2.val = 1
    · simp [ClauseSat, litVal, assignment_38, assignment_166, v166, v38, hs]
    · simp [ClauseSat, litVal, assignment_38, assignment_166, v38, hs]
  have hc597 : ClauseSat (assignment c) [79,333] := by
    by_cases hs : c.a2.val = 2
    · simp [ClauseSat, litVal, assignment_39, assignment_166, v166, v39, hs]
    · simp [ClauseSat, litVal, assignment_39, assignment_166, v39, hs]
  have hc598 : ClauseSat (assignment c) [81,333] := by
    by_cases hs : c.a2.val = 3
    · simp [ClauseSat, litVal, assignment_40, assignment_166, v166, v40, hs]
    · simp [ClauseSat, litVal, assignment_40, assignment_166, v40, hs]
  have hc599 : ClauseSat (assignment c) [83,333,324] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_162, assignment_166, v166, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_162, assignment_166, v41, hs]
  simp only [chunk5, List.forall_mem_cons]
  exact ⟨hc500, hc501, hc502, hc503, hc504, hc505, hc506, hc507, hc508, hc509, hc510, hc511, hc512, hc513, hc514, hc515, hc516, hc517, hc518, hc519, hc520, hc521, hc522, hc523, hc524, hc525, hc526, hc527, hc528, hc529, hc530, hc531, hc532, hc533, hc534, hc535, hc536, hc537, hc538, hc539, hc540, hc541, hc542, hc543, hc544, hc545, hc546, hc547, hc548, hc549, hc550, hc551, hc552, hc553, hc554, hc555, hc556, hc557, hc558, hc559, hc560, hc561, hc562, hc563, hc564, hc565, hc566, hc567, hc568, hc569, hc570, hc571, hc572, hc573, hc574, hc575, hc576, hc577, hc578, hc579, hc580, hc581, hc582, hc583, hc584, hc585, hc586, hc587, hc588, hc589, hc590, hc591, hc592, hc593, hc594, hc595, hc596, hc597, hc598, hc599, by simp⟩
#check satChunk5

def chunk6 : List (List Nat) := [[83, 332, 325], [85, 333, 330], [85, 332, 331], [87, 334], [89, 334], [91, 335], [93, 335], [95, 335, 324], [95, 334, 325], [97, 335, 330], [97, 334, 331], [73, 337, 332], [73, 337, 334], [73, 336, 333, 335], [72, 336, 333], [72, 336, 335], [72, 337, 332, 334], [121, 338], [123, 338], [125, 339], [127, 339], [129, 339, 324], [129, 338, 325], [131, 339, 330], [131, 338, 331], [133, 339, 336], [133, 338, 337], [135, 340], [137, 340], [139, 341], [141, 341], [143, 341, 324], [143, 340, 325], [145, 341, 330], [145, 340, 331], [147, 341, 336], [147, 340, 337], [119, 343, 338], [119, 343, 340], [119, 342, 339, 341], [118, 342, 339], [118, 342, 341], [118, 343, 338, 340], [175, 344], [177, 344], [179, 345], [181, 345], [183, 345, 324], [183, 344, 325], [185, 345, 330], [185, 344, 331], [187, 345, 336], [187, 344, 337], [189, 345, 342], [189, 344, 343], [191, 346], [193, 346], [195, 347], [197, 347], [199, 347, 324], [199, 346, 325], [201, 347, 330], [201, 346, 331], [203, 347, 336], [203, 346, 337], [205, 347, 342], [205, 346, 343], [173, 349, 344], [173, 349, 346], [173, 348, 345, 347], [172, 348, 345], [172, 348, 347], [172, 349, 344, 346], [348], [7, 351], [9, 351], [11, 350], [13, 351], [15, 353], [17, 353], [19, 352], [21, 353], [5, 355, 350], [5, 355, 352], [5, 354, 351, 353], [4, 354, 351], [4, 354, 353], [4, 355, 350, 352], [37, 357], [39, 357], [41, 356], [43, 357], [45, 357, 354], [45, 356, 355], [47, 359], [49, 359], [51, 358], [53, 359], [55, 359, 354], [55, 358, 355]]
theorem satChunk6 (c : Candidate) (hv : valid c)
    (hr : ∀ r : Fin 16, output c r = target r)
    (hl : derivativeLeft c = false) (hd : derivativeRight c = false) :
    ∀ cl ∈ chunk6, ClauseSat (assignment c) cl := by
  rcases hv with ⟨h0, h1, h2, h3, h4⟩
  have hc600 : ClauseSat (assignment c) [83,332,325] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_162, assignment_166, v166, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_162, assignment_166, v41, hs]
  have hc601 : ClauseSat (assignment c) [85,333,330] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_165, assignment_166, v166, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_165, assignment_166, v42, hs]
  have hc602 : ClauseSat (assignment c) [85,332,331] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_165, assignment_166, v166, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_165, assignment_166, v42, hs]
  have hc603 : ClauseSat (assignment c) [87,334] := by
    by_cases hs : c.b2.val = 0
    · simp [ClauseSat, litVal, assignment_43, assignment_167, v167, v43, hs]
    · simp [ClauseSat, litVal, assignment_43, assignment_167, v43, hs]
  have hc604 : ClauseSat (assignment c) [89,334] := by
    by_cases hs : c.b2.val = 1
    · simp [ClauseSat, litVal, assignment_44, assignment_167, v167, v44, hs]
    · simp [ClauseSat, litVal, assignment_44, assignment_167, v44, hs]
  have hc605 : ClauseSat (assignment c) [91,335] := by
    by_cases hs : c.b2.val = 2
    · simp [ClauseSat, litVal, assignment_45, assignment_167, v167, v45, hs]
    · simp [ClauseSat, litVal, assignment_45, assignment_167, v45, hs]
  have hc606 : ClauseSat (assignment c) [93,335] := by
    by_cases hs : c.b2.val = 3
    · simp [ClauseSat, litVal, assignment_46, assignment_167, v167, v46, hs]
    · simp [ClauseSat, litVal, assignment_46, assignment_167, v46, hs]
  have hc607 : ClauseSat (assignment c) [95,335,324] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_162, assignment_167, v167, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_162, assignment_167, v47, hs]
  have hc608 : ClauseSat (assignment c) [95,334,325] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_162, assignment_167, v167, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_162, assignment_167, v47, hs]
  have hc609 : ClauseSat (assignment c) [97,335,330] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_165, assignment_167, v167, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_165, assignment_167, v48, hs]
  have hc610 : ClauseSat (assignment c) [97,334,331] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_165, assignment_167, v167, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_165, assignment_167, v48, hs]
  have hc611 : ClauseSat (assignment c) [73,337,332] := by
    cases ha0 : v36 c <;> cases ha1 : v166 c <;> cases ha2 : v167 c <;> simp [ClauseSat, litVal, assignment_36, assignment_166, assignment_168, v168, ha0, ha1, ha2]
  have hc612 : ClauseSat (assignment c) [73,337,334] := by
    cases ha0 : v36 c <;> cases ha1 : v166 c <;> cases ha2 : v167 c <;> simp [ClauseSat, litVal, assignment_36, assignment_167, assignment_168, v168, ha0, ha1, ha2]
  have hc613 : ClauseSat (assignment c) [73,336,333,335] := by
    cases ha0 : v36 c <;> cases ha1 : v166 c <;> cases ha2 : v167 c <;> simp [ClauseSat, litVal, assignment_36, assignment_166, assignment_167, assignment_168, v168, ha0, ha1, ha2]
  have hc614 : ClauseSat (assignment c) [72,336,333] := by
    cases ha0 : v36 c <;> cases ha1 : v166 c <;> cases ha2 : v167 c <;> simp [ClauseSat, litVal, assignment_36, assignment_166, assignment_168, v168, ha0, ha1, ha2]
  have hc615 : ClauseSat (assignment c) [72,336,335] := by
    cases ha0 : v36 c <;> cases ha1 : v166 c <;> cases ha2 : v167 c <;> simp [ClauseSat, litVal, assignment_36, assignment_167, assignment_168, v168, ha0, ha1, ha2]
  have hc616 : ClauseSat (assignment c) [72,337,332,334] := by
    cases ha0 : v36 c <;> cases ha1 : v166 c <;> cases ha2 : v167 c <;> simp [ClauseSat, litVal, assignment_36, assignment_166, assignment_167, assignment_168, v168, ha0, ha1, ha2]
  have hc617 : ClauseSat (assignment c) [121,338] := by
    by_cases hs : c.a3.val = 0
    · simp [ClauseSat, litVal, assignment_60, assignment_169, v169, v60, hs]
    · simp [ClauseSat, litVal, assignment_60, assignment_169, v60, hs]
  have hc618 : ClauseSat (assignment c) [123,338] := by
    by_cases hs : c.a3.val = 1
    · simp [ClauseSat, litVal, assignment_61, assignment_169, v169, v61, hs]
    · simp [ClauseSat, litVal, assignment_61, assignment_169, v61, hs]
  have hc619 : ClauseSat (assignment c) [125,339] := by
    by_cases hs : c.a3.val = 2
    · simp [ClauseSat, litVal, assignment_62, assignment_169, v169, v62, hs]
    · simp [ClauseSat, litVal, assignment_62, assignment_169, v62, hs]
  have hc620 : ClauseSat (assignment c) [127,339] := by
    by_cases hs : c.a3.val = 3
    · simp [ClauseSat, litVal, assignment_63, assignment_169, v169, v63, hs]
    · simp [ClauseSat, litVal, assignment_63, assignment_169, v63, hs]
  have hc621 : ClauseSat (assignment c) [129,339,324] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_162, assignment_169, v169, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_162, assignment_169, v64, hs]
  have hc622 : ClauseSat (assignment c) [129,338,325] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_162, assignment_169, v169, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_162, assignment_169, v64, hs]
  have hc623 : ClauseSat (assignment c) [131,339,330] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_165, assignment_169, v169, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_165, assignment_169, v65, hs]
  have hc624 : ClauseSat (assignment c) [131,338,331] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_165, assignment_169, v169, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_165, assignment_169, v65, hs]
  have hc625 : ClauseSat (assignment c) [133,339,336] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_168, assignment_169, v169, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_168, assignment_169, v66, hs]
  have hc626 : ClauseSat (assignment c) [133,338,337] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_168, assignment_169, v169, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_168, assignment_169, v66, hs]
  have hc627 : ClauseSat (assignment c) [135,340] := by
    by_cases hs : c.b3.val = 0
    · simp [ClauseSat, litVal, assignment_67, assignment_170, v170, v67, hs]
    · simp [ClauseSat, litVal, assignment_67, assignment_170, v67, hs]
  have hc628 : ClauseSat (assignment c) [137,340] := by
    by_cases hs : c.b3.val = 1
    · simp [ClauseSat, litVal, assignment_68, assignment_170, v170, v68, hs]
    · simp [ClauseSat, litVal, assignment_68, assignment_170, v68, hs]
  have hc629 : ClauseSat (assignment c) [139,341] := by
    by_cases hs : c.b3.val = 2
    · simp [ClauseSat, litVal, assignment_69, assignment_170, v170, v69, hs]
    · simp [ClauseSat, litVal, assignment_69, assignment_170, v69, hs]
  have hc630 : ClauseSat (assignment c) [141,341] := by
    by_cases hs : c.b3.val = 3
    · simp [ClauseSat, litVal, assignment_70, assignment_170, v170, v70, hs]
    · simp [ClauseSat, litVal, assignment_70, assignment_170, v70, hs]
  have hc631 : ClauseSat (assignment c) [143,341,324] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_162, assignment_170, v170, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_162, assignment_170, v71, hs]
  have hc632 : ClauseSat (assignment c) [143,340,325] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_162, assignment_170, v170, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_162, assignment_170, v71, hs]
  have hc633 : ClauseSat (assignment c) [145,341,330] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_165, assignment_170, v170, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_165, assignment_170, v72, hs]
  have hc634 : ClauseSat (assignment c) [145,340,331] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_165, assignment_170, v170, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_165, assignment_170, v72, hs]
  have hc635 : ClauseSat (assignment c) [147,341,336] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_168, assignment_170, v170, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_168, assignment_170, v73, hs]
  have hc636 : ClauseSat (assignment c) [147,340,337] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_168, assignment_170, v170, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_168, assignment_170, v73, hs]
  have hc637 : ClauseSat (assignment c) [119,343,338] := by
    cases ha0 : v59 c <;> cases ha1 : v169 c <;> cases ha2 : v170 c <;> simp [ClauseSat, litVal, assignment_59, assignment_169, assignment_171, v171, ha0, ha1, ha2]
  have hc638 : ClauseSat (assignment c) [119,343,340] := by
    cases ha0 : v59 c <;> cases ha1 : v169 c <;> cases ha2 : v170 c <;> simp [ClauseSat, litVal, assignment_59, assignment_170, assignment_171, v171, ha0, ha1, ha2]
  have hc639 : ClauseSat (assignment c) [119,342,339,341] := by
    cases ha0 : v59 c <;> cases ha1 : v169 c <;> cases ha2 : v170 c <;> simp [ClauseSat, litVal, assignment_59, assignment_169, assignment_170, assignment_171, v171, ha0, ha1, ha2]
  have hc640 : ClauseSat (assignment c) [118,342,339] := by
    cases ha0 : v59 c <;> cases ha1 : v169 c <;> cases ha2 : v170 c <;> simp [ClauseSat, litVal, assignment_59, assignment_169, assignment_171, v171, ha0, ha1, ha2]
  have hc641 : ClauseSat (assignment c) [118,342,341] := by
    cases ha0 : v59 c <;> cases ha1 : v169 c <;> cases ha2 : v170 c <;> simp [ClauseSat, litVal, assignment_59, assignment_170, assignment_171, v171, ha0, ha1, ha2]
  have hc642 : ClauseSat (assignment c) [118,343,338,340] := by
    cases ha0 : v59 c <;> cases ha1 : v169 c <;> cases ha2 : v170 c <;> simp [ClauseSat, litVal, assignment_59, assignment_169, assignment_170, assignment_171, v171, ha0, ha1, ha2]
  have hc643 : ClauseSat (assignment c) [175,344] := by
    by_cases hs : c.a4.val = 0
    · simp [ClauseSat, litVal, assignment_87, assignment_172, v172, v87, hs]
    · simp [ClauseSat, litVal, assignment_87, assignment_172, v87, hs]
  have hc644 : ClauseSat (assignment c) [177,344] := by
    by_cases hs : c.a4.val = 1
    · simp [ClauseSat, litVal, assignment_88, assignment_172, v172, v88, hs]
    · simp [ClauseSat, litVal, assignment_88, assignment_172, v88, hs]
  have hc645 : ClauseSat (assignment c) [179,345] := by
    by_cases hs : c.a4.val = 2
    · simp [ClauseSat, litVal, assignment_89, assignment_172, v172, v89, hs]
    · simp [ClauseSat, litVal, assignment_89, assignment_172, v89, hs]
  have hc646 : ClauseSat (assignment c) [181,345] := by
    by_cases hs : c.a4.val = 3
    · simp [ClauseSat, litVal, assignment_90, assignment_172, v172, v90, hs]
    · simp [ClauseSat, litVal, assignment_90, assignment_172, v90, hs]
  have hc647 : ClauseSat (assignment c) [183,345,324] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_162, assignment_172, v172, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_162, assignment_172, v91, hs]
  have hc648 : ClauseSat (assignment c) [183,344,325] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_162, assignment_172, v172, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_162, assignment_172, v91, hs]
  have hc649 : ClauseSat (assignment c) [185,345,330] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_165, assignment_172, v172, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_165, assignment_172, v92, hs]
  have hc650 : ClauseSat (assignment c) [185,344,331] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_165, assignment_172, v172, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_165, assignment_172, v92, hs]
  have hc651 : ClauseSat (assignment c) [187,345,336] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_168, assignment_172, v172, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_168, assignment_172, v93, hs]
  have hc652 : ClauseSat (assignment c) [187,344,337] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_168, assignment_172, v172, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_168, assignment_172, v93, hs]
  have hc653 : ClauseSat (assignment c) [189,345,342] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_171, assignment_172, v172, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_171, assignment_172, v94, hs]
  have hc654 : ClauseSat (assignment c) [189,344,343] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_171, assignment_172, v172, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_171, assignment_172, v94, hs]
  have hc655 : ClauseSat (assignment c) [191,346] := by
    by_cases hs : c.b4.val = 0
    · simp [ClauseSat, litVal, assignment_95, assignment_173, v173, v95, hs]
    · simp [ClauseSat, litVal, assignment_95, assignment_173, v95, hs]
  have hc656 : ClauseSat (assignment c) [193,346] := by
    by_cases hs : c.b4.val = 1
    · simp [ClauseSat, litVal, assignment_96, assignment_173, v173, v96, hs]
    · simp [ClauseSat, litVal, assignment_96, assignment_173, v96, hs]
  have hc657 : ClauseSat (assignment c) [195,347] := by
    by_cases hs : c.b4.val = 2
    · simp [ClauseSat, litVal, assignment_97, assignment_173, v173, v97, hs]
    · simp [ClauseSat, litVal, assignment_97, assignment_173, v97, hs]
  have hc658 : ClauseSat (assignment c) [197,347] := by
    by_cases hs : c.b4.val = 3
    · simp [ClauseSat, litVal, assignment_98, assignment_173, v173, v98, hs]
    · simp [ClauseSat, litVal, assignment_98, assignment_173, v98, hs]
  have hc659 : ClauseSat (assignment c) [199,347,324] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_162, assignment_173, v173, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_162, assignment_173, v99, hs]
  have hc660 : ClauseSat (assignment c) [199,346,325] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_162, assignment_173, v173, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_162, assignment_173, v99, hs]
  have hc661 : ClauseSat (assignment c) [201,347,330] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_165, assignment_173, v173, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_165, assignment_173, v100, hs]
  have hc662 : ClauseSat (assignment c) [201,346,331] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_165, assignment_173, v173, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_165, assignment_173, v100, hs]
  have hc663 : ClauseSat (assignment c) [203,347,336] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_168, assignment_173, v173, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_168, assignment_173, v101, hs]
  have hc664 : ClauseSat (assignment c) [203,346,337] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_168, assignment_173, v173, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_168, assignment_173, v101, hs]
  have hc665 : ClauseSat (assignment c) [205,347,342] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_171, assignment_173, v173, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_171, assignment_173, v102, hs]
  have hc666 : ClauseSat (assignment c) [205,346,343] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_171, assignment_173, v173, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_171, assignment_173, v102, hs]
  have hc667 : ClauseSat (assignment c) [173,349,344] := by
    cases ha0 : v86 c <;> cases ha1 : v172 c <;> cases ha2 : v173 c <;> simp [ClauseSat, litVal, assignment_86, assignment_172, assignment_174, v174, ha0, ha1, ha2]
  have hc668 : ClauseSat (assignment c) [173,349,346] := by
    cases ha0 : v86 c <;> cases ha1 : v172 c <;> cases ha2 : v173 c <;> simp [ClauseSat, litVal, assignment_86, assignment_173, assignment_174, v174, ha0, ha1, ha2]
  have hc669 : ClauseSat (assignment c) [173,348,345,347] := by
    cases ha0 : v86 c <;> cases ha1 : v172 c <;> cases ha2 : v173 c <;> simp [ClauseSat, litVal, assignment_86, assignment_172, assignment_173, assignment_174, v174, ha0, ha1, ha2]
  have hc670 : ClauseSat (assignment c) [172,348,345] := by
    cases ha0 : v86 c <;> cases ha1 : v172 c <;> cases ha2 : v173 c <;> simp [ClauseSat, litVal, assignment_86, assignment_172, assignment_174, v174, ha0, ha1, ha2]
  have hc671 : ClauseSat (assignment c) [172,348,347] := by
    cases ha0 : v86 c <;> cases ha1 : v172 c <;> cases ha2 : v173 c <;> simp [ClauseSat, litVal, assignment_86, assignment_173, assignment_174, v174, ha0, ha1, ha2]
  have hc672 : ClauseSat (assignment c) [172,349,344,346] := by
    cases ha0 : v86 c <;> cases ha1 : v172 c <;> cases ha2 : v173 c <;> simp [ClauseSat, litVal, assignment_86, assignment_172, assignment_173, assignment_174, v174, ha0, ha1, ha2]
  have hc673 : ClauseSat (assignment c) [348] := by
    have hh := hr ⟨3, by decide⟩
    have ht : target ⟨3, by decide⟩ = true := by decide
    rw [ht] at hh
    simpa [ClauseSat, litVal, assignment_174, output] using hh
  have hc674 : ClauseSat (assignment c) [7,351] := by
    by_cases hs : c.a0.val = 0
    · simp [ClauseSat, litVal, assignment_3, assignment_175, v175, v3, hs]
    · simp [ClauseSat, litVal, assignment_3, assignment_175, v3, hs]
  have hc675 : ClauseSat (assignment c) [9,351] := by
    by_cases hs : c.a0.val = 1
    · simp [ClauseSat, litVal, assignment_4, assignment_175, v175, v4, hs]
    · simp [ClauseSat, litVal, assignment_4, assignment_175, v4, hs]
  have hc676 : ClauseSat (assignment c) [11,350] := by
    by_cases hs : c.a0.val = 2
    · simp [ClauseSat, litVal, assignment_5, assignment_175, v175, v5, hs]
    · simp [ClauseSat, litVal, assignment_5, assignment_175, v5, hs]
  have hc677 : ClauseSat (assignment c) [13,351] := by
    by_cases hs : c.a0.val = 3
    · simp [ClauseSat, litVal, assignment_6, assignment_175, v175, v6, hs]
    · simp [ClauseSat, litVal, assignment_6, assignment_175, v6, hs]
  have hc678 : ClauseSat (assignment c) [15,353] := by
    by_cases hs : c.b0.val = 0
    · simp [ClauseSat, litVal, assignment_7, assignment_176, v176, v7, hs]
    · simp [ClauseSat, litVal, assignment_7, assignment_176, v7, hs]
  have hc679 : ClauseSat (assignment c) [17,353] := by
    by_cases hs : c.b0.val = 1
    · simp [ClauseSat, litVal, assignment_8, assignment_176, v176, v8, hs]
    · simp [ClauseSat, litVal, assignment_8, assignment_176, v8, hs]
  have hc680 : ClauseSat (assignment c) [19,352] := by
    by_cases hs : c.b0.val = 2
    · simp [ClauseSat, litVal, assignment_9, assignment_176, v176, v9, hs]
    · simp [ClauseSat, litVal, assignment_9, assignment_176, v9, hs]
  have hc681 : ClauseSat (assignment c) [21,353] := by
    by_cases hs : c.b0.val = 3
    · simp [ClauseSat, litVal, assignment_10, assignment_176, v176, v10, hs]
    · simp [ClauseSat, litVal, assignment_10, assignment_176, v10, hs]
  have hc682 : ClauseSat (assignment c) [5,355,350] := by
    cases ha0 : v2 c <;> cases ha1 : v175 c <;> cases ha2 : v176 c <;> simp [ClauseSat, litVal, assignment_2, assignment_175, assignment_177, v177, ha0, ha1, ha2]
  have hc683 : ClauseSat (assignment c) [5,355,352] := by
    cases ha0 : v2 c <;> cases ha1 : v175 c <;> cases ha2 : v176 c <;> simp [ClauseSat, litVal, assignment_2, assignment_176, assignment_177, v177, ha0, ha1, ha2]
  have hc684 : ClauseSat (assignment c) [5,354,351,353] := by
    cases ha0 : v2 c <;> cases ha1 : v175 c <;> cases ha2 : v176 c <;> simp [ClauseSat, litVal, assignment_2, assignment_175, assignment_176, assignment_177, v177, ha0, ha1, ha2]
  have hc685 : ClauseSat (assignment c) [4,354,351] := by
    cases ha0 : v2 c <;> cases ha1 : v175 c <;> cases ha2 : v176 c <;> simp [ClauseSat, litVal, assignment_2, assignment_175, assignment_177, v177, ha0, ha1, ha2]
  have hc686 : ClauseSat (assignment c) [4,354,353] := by
    cases ha0 : v2 c <;> cases ha1 : v175 c <;> cases ha2 : v176 c <;> simp [ClauseSat, litVal, assignment_2, assignment_176, assignment_177, v177, ha0, ha1, ha2]
  have hc687 : ClauseSat (assignment c) [4,355,350,352] := by
    cases ha0 : v2 c <;> cases ha1 : v175 c <;> cases ha2 : v176 c <;> simp [ClauseSat, litVal, assignment_2, assignment_175, assignment_176, assignment_177, v177, ha0, ha1, ha2]
  have hc688 : ClauseSat (assignment c) [37,357] := by
    by_cases hs : c.a1.val = 0
    · simp [ClauseSat, litVal, assignment_18, assignment_178, v178, v18, hs]
    · simp [ClauseSat, litVal, assignment_18, assignment_178, v18, hs]
  have hc689 : ClauseSat (assignment c) [39,357] := by
    by_cases hs : c.a1.val = 1
    · simp [ClauseSat, litVal, assignment_19, assignment_178, v178, v19, hs]
    · simp [ClauseSat, litVal, assignment_19, assignment_178, v19, hs]
  have hc690 : ClauseSat (assignment c) [41,356] := by
    by_cases hs : c.a1.val = 2
    · simp [ClauseSat, litVal, assignment_20, assignment_178, v178, v20, hs]
    · simp [ClauseSat, litVal, assignment_20, assignment_178, v20, hs]
  have hc691 : ClauseSat (assignment c) [43,357] := by
    by_cases hs : c.a1.val = 3
    · simp [ClauseSat, litVal, assignment_21, assignment_178, v178, v21, hs]
    · simp [ClauseSat, litVal, assignment_21, assignment_178, v21, hs]
  have hc692 : ClauseSat (assignment c) [45,357,354] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_177, assignment_178, v178, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_177, assignment_178, v22, hs]
  have hc693 : ClauseSat (assignment c) [45,356,355] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_177, assignment_178, v178, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_177, assignment_178, v22, hs]
  have hc694 : ClauseSat (assignment c) [47,359] := by
    by_cases hs : c.b1.val = 0
    · simp [ClauseSat, litVal, assignment_23, assignment_179, v179, v23, hs]
    · simp [ClauseSat, litVal, assignment_23, assignment_179, v23, hs]
  have hc695 : ClauseSat (assignment c) [49,359] := by
    by_cases hs : c.b1.val = 1
    · simp [ClauseSat, litVal, assignment_24, assignment_179, v179, v24, hs]
    · simp [ClauseSat, litVal, assignment_24, assignment_179, v24, hs]
  have hc696 : ClauseSat (assignment c) [51,358] := by
    by_cases hs : c.b1.val = 2
    · simp [ClauseSat, litVal, assignment_25, assignment_179, v179, v25, hs]
    · simp [ClauseSat, litVal, assignment_25, assignment_179, v25, hs]
  have hc697 : ClauseSat (assignment c) [53,359] := by
    by_cases hs : c.b1.val = 3
    · simp [ClauseSat, litVal, assignment_26, assignment_179, v179, v26, hs]
    · simp [ClauseSat, litVal, assignment_26, assignment_179, v26, hs]
  have hc698 : ClauseSat (assignment c) [55,359,354] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_177, assignment_179, v179, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_177, assignment_179, v27, hs]
  have hc699 : ClauseSat (assignment c) [55,358,355] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_177, assignment_179, v179, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_177, assignment_179, v27, hs]
  simp only [chunk6, List.forall_mem_cons]
  exact ⟨hc600, hc601, hc602, hc603, hc604, hc605, hc606, hc607, hc608, hc609, hc610, hc611, hc612, hc613, hc614, hc615, hc616, hc617, hc618, hc619, hc620, hc621, hc622, hc623, hc624, hc625, hc626, hc627, hc628, hc629, hc630, hc631, hc632, hc633, hc634, hc635, hc636, hc637, hc638, hc639, hc640, hc641, hc642, hc643, hc644, hc645, hc646, hc647, hc648, hc649, hc650, hc651, hc652, hc653, hc654, hc655, hc656, hc657, hc658, hc659, hc660, hc661, hc662, hc663, hc664, hc665, hc666, hc667, hc668, hc669, hc670, hc671, hc672, hc673, hc674, hc675, hc676, hc677, hc678, hc679, hc680, hc681, hc682, hc683, hc684, hc685, hc686, hc687, hc688, hc689, hc690, hc691, hc692, hc693, hc694, hc695, hc696, hc697, hc698, hc699, by simp⟩
#check satChunk6

def chunk7 : List (List Nat) := [[35, 361, 356], [35, 361, 358], [35, 360, 357, 359], [34, 360, 357], [34, 360, 359], [34, 361, 356, 358], [75, 363], [77, 363], [79, 362], [81, 363], [83, 363, 354], [83, 362, 355], [85, 363, 360], [85, 362, 361], [87, 365], [89, 365], [91, 364], [93, 365], [95, 365, 354], [95, 364, 355], [97, 365, 360], [97, 364, 361], [73, 367, 362], [73, 367, 364], [73, 366, 363, 365], [72, 366, 363], [72, 366, 365], [72, 367, 362, 364], [121, 369], [123, 369], [125, 368], [127, 369], [129, 369, 354], [129, 368, 355], [131, 369, 360], [131, 368, 361], [133, 369, 366], [133, 368, 367], [135, 371], [137, 371], [139, 370], [141, 371], [143, 371, 354], [143, 370, 355], [145, 371, 360], [145, 370, 361], [147, 371, 366], [147, 370, 367], [119, 373, 368], [119, 373, 370], [119, 372, 369, 371], [118, 372, 369], [118, 372, 371], [118, 373, 368, 370], [175, 375], [177, 375], [179, 374], [181, 375], [183, 375, 354], [183, 374, 355], [185, 375, 360], [185, 374, 361], [187, 375, 366], [187, 374, 367], [189, 375, 372], [189, 374, 373], [191, 377], [193, 377], [195, 376], [197, 377], [199, 377, 354], [199, 376, 355], [201, 377, 360], [201, 376, 361], [203, 377, 366], [203, 376, 367], [205, 377, 372], [205, 376, 373], [173, 379, 374], [173, 379, 376], [173, 378, 375, 377], [172, 378, 375], [172, 378, 377], [172, 379, 374, 376], [379], [7, 380], [9, 381], [11, 380], [13, 381], [15, 382], [17, 383], [19, 382], [21, 383], [5, 385, 380], [5, 385, 382], [5, 384, 381, 383], [4, 384, 381], [4, 384, 383], [4, 385, 380, 382], [37, 386]]
theorem satChunk7 (c : Candidate) (hv : valid c)
    (hr : ∀ r : Fin 16, output c r = target r)
    (hl : derivativeLeft c = false) (hd : derivativeRight c = false) :
    ∀ cl ∈ chunk7, ClauseSat (assignment c) cl := by
  rcases hv with ⟨h0, h1, h2, h3, h4⟩
  have hc700 : ClauseSat (assignment c) [35,361,356] := by
    cases ha0 : v17 c <;> cases ha1 : v178 c <;> cases ha2 : v179 c <;> simp [ClauseSat, litVal, assignment_17, assignment_178, assignment_180, v180, ha0, ha1, ha2]
  have hc701 : ClauseSat (assignment c) [35,361,358] := by
    cases ha0 : v17 c <;> cases ha1 : v178 c <;> cases ha2 : v179 c <;> simp [ClauseSat, litVal, assignment_17, assignment_179, assignment_180, v180, ha0, ha1, ha2]
  have hc702 : ClauseSat (assignment c) [35,360,357,359] := by
    cases ha0 : v17 c <;> cases ha1 : v178 c <;> cases ha2 : v179 c <;> simp [ClauseSat, litVal, assignment_17, assignment_178, assignment_179, assignment_180, v180, ha0, ha1, ha2]
  have hc703 : ClauseSat (assignment c) [34,360,357] := by
    cases ha0 : v17 c <;> cases ha1 : v178 c <;> cases ha2 : v179 c <;> simp [ClauseSat, litVal, assignment_17, assignment_178, assignment_180, v180, ha0, ha1, ha2]
  have hc704 : ClauseSat (assignment c) [34,360,359] := by
    cases ha0 : v17 c <;> cases ha1 : v178 c <;> cases ha2 : v179 c <;> simp [ClauseSat, litVal, assignment_17, assignment_179, assignment_180, v180, ha0, ha1, ha2]
  have hc705 : ClauseSat (assignment c) [34,361,356,358] := by
    cases ha0 : v17 c <;> cases ha1 : v178 c <;> cases ha2 : v179 c <;> simp [ClauseSat, litVal, assignment_17, assignment_178, assignment_179, assignment_180, v180, ha0, ha1, ha2]
  have hc706 : ClauseSat (assignment c) [75,363] := by
    by_cases hs : c.a2.val = 0
    · simp [ClauseSat, litVal, assignment_37, assignment_181, v181, v37, hs]
    · simp [ClauseSat, litVal, assignment_37, assignment_181, v37, hs]
  have hc707 : ClauseSat (assignment c) [77,363] := by
    by_cases hs : c.a2.val = 1
    · simp [ClauseSat, litVal, assignment_38, assignment_181, v181, v38, hs]
    · simp [ClauseSat, litVal, assignment_38, assignment_181, v38, hs]
  have hc708 : ClauseSat (assignment c) [79,362] := by
    by_cases hs : c.a2.val = 2
    · simp [ClauseSat, litVal, assignment_39, assignment_181, v181, v39, hs]
    · simp [ClauseSat, litVal, assignment_39, assignment_181, v39, hs]
  have hc709 : ClauseSat (assignment c) [81,363] := by
    by_cases hs : c.a2.val = 3
    · simp [ClauseSat, litVal, assignment_40, assignment_181, v181, v40, hs]
    · simp [ClauseSat, litVal, assignment_40, assignment_181, v40, hs]
  have hc710 : ClauseSat (assignment c) [83,363,354] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_177, assignment_181, v181, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_177, assignment_181, v41, hs]
  have hc711 : ClauseSat (assignment c) [83,362,355] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_177, assignment_181, v181, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_177, assignment_181, v41, hs]
  have hc712 : ClauseSat (assignment c) [85,363,360] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_180, assignment_181, v181, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_180, assignment_181, v42, hs]
  have hc713 : ClauseSat (assignment c) [85,362,361] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_180, assignment_181, v181, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_180, assignment_181, v42, hs]
  have hc714 : ClauseSat (assignment c) [87,365] := by
    by_cases hs : c.b2.val = 0
    · simp [ClauseSat, litVal, assignment_43, assignment_182, v182, v43, hs]
    · simp [ClauseSat, litVal, assignment_43, assignment_182, v43, hs]
  have hc715 : ClauseSat (assignment c) [89,365] := by
    by_cases hs : c.b2.val = 1
    · simp [ClauseSat, litVal, assignment_44, assignment_182, v182, v44, hs]
    · simp [ClauseSat, litVal, assignment_44, assignment_182, v44, hs]
  have hc716 : ClauseSat (assignment c) [91,364] := by
    by_cases hs : c.b2.val = 2
    · simp [ClauseSat, litVal, assignment_45, assignment_182, v182, v45, hs]
    · simp [ClauseSat, litVal, assignment_45, assignment_182, v45, hs]
  have hc717 : ClauseSat (assignment c) [93,365] := by
    by_cases hs : c.b2.val = 3
    · simp [ClauseSat, litVal, assignment_46, assignment_182, v182, v46, hs]
    · simp [ClauseSat, litVal, assignment_46, assignment_182, v46, hs]
  have hc718 : ClauseSat (assignment c) [95,365,354] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_177, assignment_182, v182, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_177, assignment_182, v47, hs]
  have hc719 : ClauseSat (assignment c) [95,364,355] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_177, assignment_182, v182, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_177, assignment_182, v47, hs]
  have hc720 : ClauseSat (assignment c) [97,365,360] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_180, assignment_182, v182, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_180, assignment_182, v48, hs]
  have hc721 : ClauseSat (assignment c) [97,364,361] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_180, assignment_182, v182, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_180, assignment_182, v48, hs]
  have hc722 : ClauseSat (assignment c) [73,367,362] := by
    cases ha0 : v36 c <;> cases ha1 : v181 c <;> cases ha2 : v182 c <;> simp [ClauseSat, litVal, assignment_36, assignment_181, assignment_183, v183, ha0, ha1, ha2]
  have hc723 : ClauseSat (assignment c) [73,367,364] := by
    cases ha0 : v36 c <;> cases ha1 : v181 c <;> cases ha2 : v182 c <;> simp [ClauseSat, litVal, assignment_36, assignment_182, assignment_183, v183, ha0, ha1, ha2]
  have hc724 : ClauseSat (assignment c) [73,366,363,365] := by
    cases ha0 : v36 c <;> cases ha1 : v181 c <;> cases ha2 : v182 c <;> simp [ClauseSat, litVal, assignment_36, assignment_181, assignment_182, assignment_183, v183, ha0, ha1, ha2]
  have hc725 : ClauseSat (assignment c) [72,366,363] := by
    cases ha0 : v36 c <;> cases ha1 : v181 c <;> cases ha2 : v182 c <;> simp [ClauseSat, litVal, assignment_36, assignment_181, assignment_183, v183, ha0, ha1, ha2]
  have hc726 : ClauseSat (assignment c) [72,366,365] := by
    cases ha0 : v36 c <;> cases ha1 : v181 c <;> cases ha2 : v182 c <;> simp [ClauseSat, litVal, assignment_36, assignment_182, assignment_183, v183, ha0, ha1, ha2]
  have hc727 : ClauseSat (assignment c) [72,367,362,364] := by
    cases ha0 : v36 c <;> cases ha1 : v181 c <;> cases ha2 : v182 c <;> simp [ClauseSat, litVal, assignment_36, assignment_181, assignment_182, assignment_183, v183, ha0, ha1, ha2]
  have hc728 : ClauseSat (assignment c) [121,369] := by
    by_cases hs : c.a3.val = 0
    · simp [ClauseSat, litVal, assignment_60, assignment_184, v184, v60, hs]
    · simp [ClauseSat, litVal, assignment_60, assignment_184, v60, hs]
  have hc729 : ClauseSat (assignment c) [123,369] := by
    by_cases hs : c.a3.val = 1
    · simp [ClauseSat, litVal, assignment_61, assignment_184, v184, v61, hs]
    · simp [ClauseSat, litVal, assignment_61, assignment_184, v61, hs]
  have hc730 : ClauseSat (assignment c) [125,368] := by
    by_cases hs : c.a3.val = 2
    · simp [ClauseSat, litVal, assignment_62, assignment_184, v184, v62, hs]
    · simp [ClauseSat, litVal, assignment_62, assignment_184, v62, hs]
  have hc731 : ClauseSat (assignment c) [127,369] := by
    by_cases hs : c.a3.val = 3
    · simp [ClauseSat, litVal, assignment_63, assignment_184, v184, v63, hs]
    · simp [ClauseSat, litVal, assignment_63, assignment_184, v63, hs]
  have hc732 : ClauseSat (assignment c) [129,369,354] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_177, assignment_184, v184, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_177, assignment_184, v64, hs]
  have hc733 : ClauseSat (assignment c) [129,368,355] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_177, assignment_184, v184, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_177, assignment_184, v64, hs]
  have hc734 : ClauseSat (assignment c) [131,369,360] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_180, assignment_184, v184, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_180, assignment_184, v65, hs]
  have hc735 : ClauseSat (assignment c) [131,368,361] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_180, assignment_184, v184, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_180, assignment_184, v65, hs]
  have hc736 : ClauseSat (assignment c) [133,369,366] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_183, assignment_184, v184, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_183, assignment_184, v66, hs]
  have hc737 : ClauseSat (assignment c) [133,368,367] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_183, assignment_184, v184, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_183, assignment_184, v66, hs]
  have hc738 : ClauseSat (assignment c) [135,371] := by
    by_cases hs : c.b3.val = 0
    · simp [ClauseSat, litVal, assignment_67, assignment_185, v185, v67, hs]
    · simp [ClauseSat, litVal, assignment_67, assignment_185, v67, hs]
  have hc739 : ClauseSat (assignment c) [137,371] := by
    by_cases hs : c.b3.val = 1
    · simp [ClauseSat, litVal, assignment_68, assignment_185, v185, v68, hs]
    · simp [ClauseSat, litVal, assignment_68, assignment_185, v68, hs]
  have hc740 : ClauseSat (assignment c) [139,370] := by
    by_cases hs : c.b3.val = 2
    · simp [ClauseSat, litVal, assignment_69, assignment_185, v185, v69, hs]
    · simp [ClauseSat, litVal, assignment_69, assignment_185, v69, hs]
  have hc741 : ClauseSat (assignment c) [141,371] := by
    by_cases hs : c.b3.val = 3
    · simp [ClauseSat, litVal, assignment_70, assignment_185, v185, v70, hs]
    · simp [ClauseSat, litVal, assignment_70, assignment_185, v70, hs]
  have hc742 : ClauseSat (assignment c) [143,371,354] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_177, assignment_185, v185, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_177, assignment_185, v71, hs]
  have hc743 : ClauseSat (assignment c) [143,370,355] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_177, assignment_185, v185, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_177, assignment_185, v71, hs]
  have hc744 : ClauseSat (assignment c) [145,371,360] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_180, assignment_185, v185, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_180, assignment_185, v72, hs]
  have hc745 : ClauseSat (assignment c) [145,370,361] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_180, assignment_185, v185, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_180, assignment_185, v72, hs]
  have hc746 : ClauseSat (assignment c) [147,371,366] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_183, assignment_185, v185, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_183, assignment_185, v73, hs]
  have hc747 : ClauseSat (assignment c) [147,370,367] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_183, assignment_185, v185, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_183, assignment_185, v73, hs]
  have hc748 : ClauseSat (assignment c) [119,373,368] := by
    cases ha0 : v59 c <;> cases ha1 : v184 c <;> cases ha2 : v185 c <;> simp [ClauseSat, litVal, assignment_59, assignment_184, assignment_186, v186, ha0, ha1, ha2]
  have hc749 : ClauseSat (assignment c) [119,373,370] := by
    cases ha0 : v59 c <;> cases ha1 : v184 c <;> cases ha2 : v185 c <;> simp [ClauseSat, litVal, assignment_59, assignment_185, assignment_186, v186, ha0, ha1, ha2]
  have hc750 : ClauseSat (assignment c) [119,372,369,371] := by
    cases ha0 : v59 c <;> cases ha1 : v184 c <;> cases ha2 : v185 c <;> simp [ClauseSat, litVal, assignment_59, assignment_184, assignment_185, assignment_186, v186, ha0, ha1, ha2]
  have hc751 : ClauseSat (assignment c) [118,372,369] := by
    cases ha0 : v59 c <;> cases ha1 : v184 c <;> cases ha2 : v185 c <;> simp [ClauseSat, litVal, assignment_59, assignment_184, assignment_186, v186, ha0, ha1, ha2]
  have hc752 : ClauseSat (assignment c) [118,372,371] := by
    cases ha0 : v59 c <;> cases ha1 : v184 c <;> cases ha2 : v185 c <;> simp [ClauseSat, litVal, assignment_59, assignment_185, assignment_186, v186, ha0, ha1, ha2]
  have hc753 : ClauseSat (assignment c) [118,373,368,370] := by
    cases ha0 : v59 c <;> cases ha1 : v184 c <;> cases ha2 : v185 c <;> simp [ClauseSat, litVal, assignment_59, assignment_184, assignment_185, assignment_186, v186, ha0, ha1, ha2]
  have hc754 : ClauseSat (assignment c) [175,375] := by
    by_cases hs : c.a4.val = 0
    · simp [ClauseSat, litVal, assignment_87, assignment_187, v187, v87, hs]
    · simp [ClauseSat, litVal, assignment_87, assignment_187, v87, hs]
  have hc755 : ClauseSat (assignment c) [177,375] := by
    by_cases hs : c.a4.val = 1
    · simp [ClauseSat, litVal, assignment_88, assignment_187, v187, v88, hs]
    · simp [ClauseSat, litVal, assignment_88, assignment_187, v88, hs]
  have hc756 : ClauseSat (assignment c) [179,374] := by
    by_cases hs : c.a4.val = 2
    · simp [ClauseSat, litVal, assignment_89, assignment_187, v187, v89, hs]
    · simp [ClauseSat, litVal, assignment_89, assignment_187, v89, hs]
  have hc757 : ClauseSat (assignment c) [181,375] := by
    by_cases hs : c.a4.val = 3
    · simp [ClauseSat, litVal, assignment_90, assignment_187, v187, v90, hs]
    · simp [ClauseSat, litVal, assignment_90, assignment_187, v90, hs]
  have hc758 : ClauseSat (assignment c) [183,375,354] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_177, assignment_187, v187, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_177, assignment_187, v91, hs]
  have hc759 : ClauseSat (assignment c) [183,374,355] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_177, assignment_187, v187, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_177, assignment_187, v91, hs]
  have hc760 : ClauseSat (assignment c) [185,375,360] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_180, assignment_187, v187, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_180, assignment_187, v92, hs]
  have hc761 : ClauseSat (assignment c) [185,374,361] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_180, assignment_187, v187, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_180, assignment_187, v92, hs]
  have hc762 : ClauseSat (assignment c) [187,375,366] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_183, assignment_187, v187, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_183, assignment_187, v93, hs]
  have hc763 : ClauseSat (assignment c) [187,374,367] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_183, assignment_187, v187, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_183, assignment_187, v93, hs]
  have hc764 : ClauseSat (assignment c) [189,375,372] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_186, assignment_187, v187, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_186, assignment_187, v94, hs]
  have hc765 : ClauseSat (assignment c) [189,374,373] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_186, assignment_187, v187, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_186, assignment_187, v94, hs]
  have hc766 : ClauseSat (assignment c) [191,377] := by
    by_cases hs : c.b4.val = 0
    · simp [ClauseSat, litVal, assignment_95, assignment_188, v188, v95, hs]
    · simp [ClauseSat, litVal, assignment_95, assignment_188, v95, hs]
  have hc767 : ClauseSat (assignment c) [193,377] := by
    by_cases hs : c.b4.val = 1
    · simp [ClauseSat, litVal, assignment_96, assignment_188, v188, v96, hs]
    · simp [ClauseSat, litVal, assignment_96, assignment_188, v96, hs]
  have hc768 : ClauseSat (assignment c) [195,376] := by
    by_cases hs : c.b4.val = 2
    · simp [ClauseSat, litVal, assignment_97, assignment_188, v188, v97, hs]
    · simp [ClauseSat, litVal, assignment_97, assignment_188, v97, hs]
  have hc769 : ClauseSat (assignment c) [197,377] := by
    by_cases hs : c.b4.val = 3
    · simp [ClauseSat, litVal, assignment_98, assignment_188, v188, v98, hs]
    · simp [ClauseSat, litVal, assignment_98, assignment_188, v98, hs]
  have hc770 : ClauseSat (assignment c) [199,377,354] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_177, assignment_188, v188, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_177, assignment_188, v99, hs]
  have hc771 : ClauseSat (assignment c) [199,376,355] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_177, assignment_188, v188, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_177, assignment_188, v99, hs]
  have hc772 : ClauseSat (assignment c) [201,377,360] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_180, assignment_188, v188, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_180, assignment_188, v100, hs]
  have hc773 : ClauseSat (assignment c) [201,376,361] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_180, assignment_188, v188, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_180, assignment_188, v100, hs]
  have hc774 : ClauseSat (assignment c) [203,377,366] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_183, assignment_188, v188, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_183, assignment_188, v101, hs]
  have hc775 : ClauseSat (assignment c) [203,376,367] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_183, assignment_188, v188, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_183, assignment_188, v101, hs]
  have hc776 : ClauseSat (assignment c) [205,377,372] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_186, assignment_188, v188, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_186, assignment_188, v102, hs]
  have hc777 : ClauseSat (assignment c) [205,376,373] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_186, assignment_188, v188, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_186, assignment_188, v102, hs]
  have hc778 : ClauseSat (assignment c) [173,379,374] := by
    cases ha0 : v86 c <;> cases ha1 : v187 c <;> cases ha2 : v188 c <;> simp [ClauseSat, litVal, assignment_86, assignment_187, assignment_189, v189, ha0, ha1, ha2]
  have hc779 : ClauseSat (assignment c) [173,379,376] := by
    cases ha0 : v86 c <;> cases ha1 : v187 c <;> cases ha2 : v188 c <;> simp [ClauseSat, litVal, assignment_86, assignment_188, assignment_189, v189, ha0, ha1, ha2]
  have hc780 : ClauseSat (assignment c) [173,378,375,377] := by
    cases ha0 : v86 c <;> cases ha1 : v187 c <;> cases ha2 : v188 c <;> simp [ClauseSat, litVal, assignment_86, assignment_187, assignment_188, assignment_189, v189, ha0, ha1, ha2]
  have hc781 : ClauseSat (assignment c) [172,378,375] := by
    cases ha0 : v86 c <;> cases ha1 : v187 c <;> cases ha2 : v188 c <;> simp [ClauseSat, litVal, assignment_86, assignment_187, assignment_189, v189, ha0, ha1, ha2]
  have hc782 : ClauseSat (assignment c) [172,378,377] := by
    cases ha0 : v86 c <;> cases ha1 : v187 c <;> cases ha2 : v188 c <;> simp [ClauseSat, litVal, assignment_86, assignment_188, assignment_189, v189, ha0, ha1, ha2]
  have hc783 : ClauseSat (assignment c) [172,379,374,376] := by
    cases ha0 : v86 c <;> cases ha1 : v187 c <;> cases ha2 : v188 c <;> simp [ClauseSat, litVal, assignment_86, assignment_187, assignment_188, assignment_189, v189, ha0, ha1, ha2]
  have hc784 : ClauseSat (assignment c) [379] := by
    have hh := hr ⟨4, by decide⟩
    have ht : target ⟨4, by decide⟩ = false := by decide
    rw [ht] at hh
    simpa [ClauseSat, litVal, assignment_189, output] using hh
  have hc785 : ClauseSat (assignment c) [7,380] := by
    by_cases hs : c.a0.val = 0
    · simp [ClauseSat, litVal, assignment_3, assignment_190, v190, v3, hs]
    · simp [ClauseSat, litVal, assignment_3, assignment_190, v3, hs]
  have hc786 : ClauseSat (assignment c) [9,381] := by
    by_cases hs : c.a0.val = 1
    · simp [ClauseSat, litVal, assignment_4, assignment_190, v190, v4, hs]
    · simp [ClauseSat, litVal, assignment_4, assignment_190, v4, hs]
  have hc787 : ClauseSat (assignment c) [11,380] := by
    by_cases hs : c.a0.val = 2
    · simp [ClauseSat, litVal, assignment_5, assignment_190, v190, v5, hs]
    · simp [ClauseSat, litVal, assignment_5, assignment_190, v5, hs]
  have hc788 : ClauseSat (assignment c) [13,381] := by
    by_cases hs : c.a0.val = 3
    · simp [ClauseSat, litVal, assignment_6, assignment_190, v190, v6, hs]
    · simp [ClauseSat, litVal, assignment_6, assignment_190, v6, hs]
  have hc789 : ClauseSat (assignment c) [15,382] := by
    by_cases hs : c.b0.val = 0
    · simp [ClauseSat, litVal, assignment_7, assignment_191, v191, v7, hs]
    · simp [ClauseSat, litVal, assignment_7, assignment_191, v7, hs]
  have hc790 : ClauseSat (assignment c) [17,383] := by
    by_cases hs : c.b0.val = 1
    · simp [ClauseSat, litVal, assignment_8, assignment_191, v191, v8, hs]
    · simp [ClauseSat, litVal, assignment_8, assignment_191, v8, hs]
  have hc791 : ClauseSat (assignment c) [19,382] := by
    by_cases hs : c.b0.val = 2
    · simp [ClauseSat, litVal, assignment_9, assignment_191, v191, v9, hs]
    · simp [ClauseSat, litVal, assignment_9, assignment_191, v9, hs]
  have hc792 : ClauseSat (assignment c) [21,383] := by
    by_cases hs : c.b0.val = 3
    · simp [ClauseSat, litVal, assignment_10, assignment_191, v191, v10, hs]
    · simp [ClauseSat, litVal, assignment_10, assignment_191, v10, hs]
  have hc793 : ClauseSat (assignment c) [5,385,380] := by
    cases ha0 : v2 c <;> cases ha1 : v190 c <;> cases ha2 : v191 c <;> simp [ClauseSat, litVal, assignment_2, assignment_190, assignment_192, v192, ha0, ha1, ha2]
  have hc794 : ClauseSat (assignment c) [5,385,382] := by
    cases ha0 : v2 c <;> cases ha1 : v190 c <;> cases ha2 : v191 c <;> simp [ClauseSat, litVal, assignment_2, assignment_191, assignment_192, v192, ha0, ha1, ha2]
  have hc795 : ClauseSat (assignment c) [5,384,381,383] := by
    cases ha0 : v2 c <;> cases ha1 : v190 c <;> cases ha2 : v191 c <;> simp [ClauseSat, litVal, assignment_2, assignment_190, assignment_191, assignment_192, v192, ha0, ha1, ha2]
  have hc796 : ClauseSat (assignment c) [4,384,381] := by
    cases ha0 : v2 c <;> cases ha1 : v190 c <;> cases ha2 : v191 c <;> simp [ClauseSat, litVal, assignment_2, assignment_190, assignment_192, v192, ha0, ha1, ha2]
  have hc797 : ClauseSat (assignment c) [4,384,383] := by
    cases ha0 : v2 c <;> cases ha1 : v190 c <;> cases ha2 : v191 c <;> simp [ClauseSat, litVal, assignment_2, assignment_191, assignment_192, v192, ha0, ha1, ha2]
  have hc798 : ClauseSat (assignment c) [4,385,380,382] := by
    cases ha0 : v2 c <;> cases ha1 : v190 c <;> cases ha2 : v191 c <;> simp [ClauseSat, litVal, assignment_2, assignment_190, assignment_191, assignment_192, v192, ha0, ha1, ha2]
  have hc799 : ClauseSat (assignment c) [37,386] := by
    by_cases hs : c.a1.val = 0
    · simp [ClauseSat, litVal, assignment_18, assignment_193, v193, v18, hs]
    · simp [ClauseSat, litVal, assignment_18, assignment_193, v18, hs]
  simp only [chunk7, List.forall_mem_cons]
  exact ⟨hc700, hc701, hc702, hc703, hc704, hc705, hc706, hc707, hc708, hc709, hc710, hc711, hc712, hc713, hc714, hc715, hc716, hc717, hc718, hc719, hc720, hc721, hc722, hc723, hc724, hc725, hc726, hc727, hc728, hc729, hc730, hc731, hc732, hc733, hc734, hc735, hc736, hc737, hc738, hc739, hc740, hc741, hc742, hc743, hc744, hc745, hc746, hc747, hc748, hc749, hc750, hc751, hc752, hc753, hc754, hc755, hc756, hc757, hc758, hc759, hc760, hc761, hc762, hc763, hc764, hc765, hc766, hc767, hc768, hc769, hc770, hc771, hc772, hc773, hc774, hc775, hc776, hc777, hc778, hc779, hc780, hc781, hc782, hc783, hc784, hc785, hc786, hc787, hc788, hc789, hc790, hc791, hc792, hc793, hc794, hc795, hc796, hc797, hc798, hc799, by simp⟩
#check satChunk7

def chunk8 : List (List Nat) := [[39, 387], [41, 386], [43, 387], [45, 387, 384], [45, 386, 385], [47, 388], [49, 389], [51, 388], [53, 389], [55, 389, 384], [55, 388, 385], [35, 391, 386], [35, 391, 388], [35, 390, 387, 389], [34, 390, 387], [34, 390, 389], [34, 391, 386, 388], [75, 392], [77, 393], [79, 392], [81, 393], [83, 393, 384], [83, 392, 385], [85, 393, 390], [85, 392, 391], [87, 394], [89, 395], [91, 394], [93, 395], [95, 395, 384], [95, 394, 385], [97, 395, 390], [97, 394, 391], [73, 397, 392], [73, 397, 394], [73, 396, 393, 395], [72, 396, 393], [72, 396, 395], [72, 397, 392, 394], [121, 398], [123, 399], [125, 398], [127, 399], [129, 399, 384], [129, 398, 385], [131, 399, 390], [131, 398, 391], [133, 399, 396], [133, 398, 397], [135, 400], [137, 401], [139, 400], [141, 401], [143, 401, 384], [143, 400, 385], [145, 401, 390], [145, 400, 391], [147, 401, 396], [147, 400, 397], [119, 403, 398], [119, 403, 400], [119, 402, 399, 401], [118, 402, 399], [118, 402, 401], [118, 403, 398, 400], [175, 404], [177, 405], [179, 404], [181, 405], [183, 405, 384], [183, 404, 385], [185, 405, 390], [185, 404, 391], [187, 405, 396], [187, 404, 397], [189, 405, 402], [189, 404, 403], [191, 406], [193, 407], [195, 406], [197, 407], [199, 407, 384], [199, 406, 385], [201, 407, 390], [201, 406, 391], [203, 407, 396], [203, 406, 397], [205, 407, 402], [205, 406, 403], [173, 409, 404], [173, 409, 406], [173, 408, 405, 407], [172, 408, 405], [172, 408, 407], [172, 409, 404, 406], [408], [7, 411], [9, 410], [11, 410], [13, 411]]
theorem satChunk8 (c : Candidate) (hv : valid c)
    (hr : ∀ r : Fin 16, output c r = target r)
    (hl : derivativeLeft c = false) (hd : derivativeRight c = false) :
    ∀ cl ∈ chunk8, ClauseSat (assignment c) cl := by
  rcases hv with ⟨h0, h1, h2, h3, h4⟩
  have hc800 : ClauseSat (assignment c) [39,387] := by
    by_cases hs : c.a1.val = 1
    · simp [ClauseSat, litVal, assignment_19, assignment_193, v193, v19, hs]
    · simp [ClauseSat, litVal, assignment_19, assignment_193, v19, hs]
  have hc801 : ClauseSat (assignment c) [41,386] := by
    by_cases hs : c.a1.val = 2
    · simp [ClauseSat, litVal, assignment_20, assignment_193, v193, v20, hs]
    · simp [ClauseSat, litVal, assignment_20, assignment_193, v20, hs]
  have hc802 : ClauseSat (assignment c) [43,387] := by
    by_cases hs : c.a1.val = 3
    · simp [ClauseSat, litVal, assignment_21, assignment_193, v193, v21, hs]
    · simp [ClauseSat, litVal, assignment_21, assignment_193, v21, hs]
  have hc803 : ClauseSat (assignment c) [45,387,384] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_192, assignment_193, v193, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_192, assignment_193, v22, hs]
  have hc804 : ClauseSat (assignment c) [45,386,385] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_192, assignment_193, v193, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_192, assignment_193, v22, hs]
  have hc805 : ClauseSat (assignment c) [47,388] := by
    by_cases hs : c.b1.val = 0
    · simp [ClauseSat, litVal, assignment_23, assignment_194, v194, v23, hs]
    · simp [ClauseSat, litVal, assignment_23, assignment_194, v23, hs]
  have hc806 : ClauseSat (assignment c) [49,389] := by
    by_cases hs : c.b1.val = 1
    · simp [ClauseSat, litVal, assignment_24, assignment_194, v194, v24, hs]
    · simp [ClauseSat, litVal, assignment_24, assignment_194, v24, hs]
  have hc807 : ClauseSat (assignment c) [51,388] := by
    by_cases hs : c.b1.val = 2
    · simp [ClauseSat, litVal, assignment_25, assignment_194, v194, v25, hs]
    · simp [ClauseSat, litVal, assignment_25, assignment_194, v25, hs]
  have hc808 : ClauseSat (assignment c) [53,389] := by
    by_cases hs : c.b1.val = 3
    · simp [ClauseSat, litVal, assignment_26, assignment_194, v194, v26, hs]
    · simp [ClauseSat, litVal, assignment_26, assignment_194, v26, hs]
  have hc809 : ClauseSat (assignment c) [55,389,384] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_192, assignment_194, v194, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_192, assignment_194, v27, hs]
  have hc810 : ClauseSat (assignment c) [55,388,385] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_192, assignment_194, v194, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_192, assignment_194, v27, hs]
  have hc811 : ClauseSat (assignment c) [35,391,386] := by
    cases ha0 : v17 c <;> cases ha1 : v193 c <;> cases ha2 : v194 c <;> simp [ClauseSat, litVal, assignment_17, assignment_193, assignment_195, v195, ha0, ha1, ha2]
  have hc812 : ClauseSat (assignment c) [35,391,388] := by
    cases ha0 : v17 c <;> cases ha1 : v193 c <;> cases ha2 : v194 c <;> simp [ClauseSat, litVal, assignment_17, assignment_194, assignment_195, v195, ha0, ha1, ha2]
  have hc813 : ClauseSat (assignment c) [35,390,387,389] := by
    cases ha0 : v17 c <;> cases ha1 : v193 c <;> cases ha2 : v194 c <;> simp [ClauseSat, litVal, assignment_17, assignment_193, assignment_194, assignment_195, v195, ha0, ha1, ha2]
  have hc814 : ClauseSat (assignment c) [34,390,387] := by
    cases ha0 : v17 c <;> cases ha1 : v193 c <;> cases ha2 : v194 c <;> simp [ClauseSat, litVal, assignment_17, assignment_193, assignment_195, v195, ha0, ha1, ha2]
  have hc815 : ClauseSat (assignment c) [34,390,389] := by
    cases ha0 : v17 c <;> cases ha1 : v193 c <;> cases ha2 : v194 c <;> simp [ClauseSat, litVal, assignment_17, assignment_194, assignment_195, v195, ha0, ha1, ha2]
  have hc816 : ClauseSat (assignment c) [34,391,386,388] := by
    cases ha0 : v17 c <;> cases ha1 : v193 c <;> cases ha2 : v194 c <;> simp [ClauseSat, litVal, assignment_17, assignment_193, assignment_194, assignment_195, v195, ha0, ha1, ha2]
  have hc817 : ClauseSat (assignment c) [75,392] := by
    by_cases hs : c.a2.val = 0
    · simp [ClauseSat, litVal, assignment_37, assignment_196, v196, v37, hs]
    · simp [ClauseSat, litVal, assignment_37, assignment_196, v37, hs]
  have hc818 : ClauseSat (assignment c) [77,393] := by
    by_cases hs : c.a2.val = 1
    · simp [ClauseSat, litVal, assignment_38, assignment_196, v196, v38, hs]
    · simp [ClauseSat, litVal, assignment_38, assignment_196, v38, hs]
  have hc819 : ClauseSat (assignment c) [79,392] := by
    by_cases hs : c.a2.val = 2
    · simp [ClauseSat, litVal, assignment_39, assignment_196, v196, v39, hs]
    · simp [ClauseSat, litVal, assignment_39, assignment_196, v39, hs]
  have hc820 : ClauseSat (assignment c) [81,393] := by
    by_cases hs : c.a2.val = 3
    · simp [ClauseSat, litVal, assignment_40, assignment_196, v196, v40, hs]
    · simp [ClauseSat, litVal, assignment_40, assignment_196, v40, hs]
  have hc821 : ClauseSat (assignment c) [83,393,384] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_192, assignment_196, v196, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_192, assignment_196, v41, hs]
  have hc822 : ClauseSat (assignment c) [83,392,385] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_192, assignment_196, v196, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_192, assignment_196, v41, hs]
  have hc823 : ClauseSat (assignment c) [85,393,390] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_195, assignment_196, v196, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_195, assignment_196, v42, hs]
  have hc824 : ClauseSat (assignment c) [85,392,391] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_195, assignment_196, v196, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_195, assignment_196, v42, hs]
  have hc825 : ClauseSat (assignment c) [87,394] := by
    by_cases hs : c.b2.val = 0
    · simp [ClauseSat, litVal, assignment_43, assignment_197, v197, v43, hs]
    · simp [ClauseSat, litVal, assignment_43, assignment_197, v43, hs]
  have hc826 : ClauseSat (assignment c) [89,395] := by
    by_cases hs : c.b2.val = 1
    · simp [ClauseSat, litVal, assignment_44, assignment_197, v197, v44, hs]
    · simp [ClauseSat, litVal, assignment_44, assignment_197, v44, hs]
  have hc827 : ClauseSat (assignment c) [91,394] := by
    by_cases hs : c.b2.val = 2
    · simp [ClauseSat, litVal, assignment_45, assignment_197, v197, v45, hs]
    · simp [ClauseSat, litVal, assignment_45, assignment_197, v45, hs]
  have hc828 : ClauseSat (assignment c) [93,395] := by
    by_cases hs : c.b2.val = 3
    · simp [ClauseSat, litVal, assignment_46, assignment_197, v197, v46, hs]
    · simp [ClauseSat, litVal, assignment_46, assignment_197, v46, hs]
  have hc829 : ClauseSat (assignment c) [95,395,384] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_192, assignment_197, v197, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_192, assignment_197, v47, hs]
  have hc830 : ClauseSat (assignment c) [95,394,385] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_192, assignment_197, v197, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_192, assignment_197, v47, hs]
  have hc831 : ClauseSat (assignment c) [97,395,390] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_195, assignment_197, v197, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_195, assignment_197, v48, hs]
  have hc832 : ClauseSat (assignment c) [97,394,391] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_195, assignment_197, v197, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_195, assignment_197, v48, hs]
  have hc833 : ClauseSat (assignment c) [73,397,392] := by
    cases ha0 : v36 c <;> cases ha1 : v196 c <;> cases ha2 : v197 c <;> simp [ClauseSat, litVal, assignment_36, assignment_196, assignment_198, v198, ha0, ha1, ha2]
  have hc834 : ClauseSat (assignment c) [73,397,394] := by
    cases ha0 : v36 c <;> cases ha1 : v196 c <;> cases ha2 : v197 c <;> simp [ClauseSat, litVal, assignment_36, assignment_197, assignment_198, v198, ha0, ha1, ha2]
  have hc835 : ClauseSat (assignment c) [73,396,393,395] := by
    cases ha0 : v36 c <;> cases ha1 : v196 c <;> cases ha2 : v197 c <;> simp [ClauseSat, litVal, assignment_36, assignment_196, assignment_197, assignment_198, v198, ha0, ha1, ha2]
  have hc836 : ClauseSat (assignment c) [72,396,393] := by
    cases ha0 : v36 c <;> cases ha1 : v196 c <;> cases ha2 : v197 c <;> simp [ClauseSat, litVal, assignment_36, assignment_196, assignment_198, v198, ha0, ha1, ha2]
  have hc837 : ClauseSat (assignment c) [72,396,395] := by
    cases ha0 : v36 c <;> cases ha1 : v196 c <;> cases ha2 : v197 c <;> simp [ClauseSat, litVal, assignment_36, assignment_197, assignment_198, v198, ha0, ha1, ha2]
  have hc838 : ClauseSat (assignment c) [72,397,392,394] := by
    cases ha0 : v36 c <;> cases ha1 : v196 c <;> cases ha2 : v197 c <;> simp [ClauseSat, litVal, assignment_36, assignment_196, assignment_197, assignment_198, v198, ha0, ha1, ha2]
  have hc839 : ClauseSat (assignment c) [121,398] := by
    by_cases hs : c.a3.val = 0
    · simp [ClauseSat, litVal, assignment_60, assignment_199, v199, v60, hs]
    · simp [ClauseSat, litVal, assignment_60, assignment_199, v60, hs]
  have hc840 : ClauseSat (assignment c) [123,399] := by
    by_cases hs : c.a3.val = 1
    · simp [ClauseSat, litVal, assignment_61, assignment_199, v199, v61, hs]
    · simp [ClauseSat, litVal, assignment_61, assignment_199, v61, hs]
  have hc841 : ClauseSat (assignment c) [125,398] := by
    by_cases hs : c.a3.val = 2
    · simp [ClauseSat, litVal, assignment_62, assignment_199, v199, v62, hs]
    · simp [ClauseSat, litVal, assignment_62, assignment_199, v62, hs]
  have hc842 : ClauseSat (assignment c) [127,399] := by
    by_cases hs : c.a3.val = 3
    · simp [ClauseSat, litVal, assignment_63, assignment_199, v199, v63, hs]
    · simp [ClauseSat, litVal, assignment_63, assignment_199, v63, hs]
  have hc843 : ClauseSat (assignment c) [129,399,384] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_192, assignment_199, v199, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_192, assignment_199, v64, hs]
  have hc844 : ClauseSat (assignment c) [129,398,385] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_192, assignment_199, v199, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_192, assignment_199, v64, hs]
  have hc845 : ClauseSat (assignment c) [131,399,390] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_195, assignment_199, v199, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_195, assignment_199, v65, hs]
  have hc846 : ClauseSat (assignment c) [131,398,391] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_195, assignment_199, v199, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_195, assignment_199, v65, hs]
  have hc847 : ClauseSat (assignment c) [133,399,396] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_198, assignment_199, v199, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_198, assignment_199, v66, hs]
  have hc848 : ClauseSat (assignment c) [133,398,397] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_198, assignment_199, v199, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_198, assignment_199, v66, hs]
  have hc849 : ClauseSat (assignment c) [135,400] := by
    by_cases hs : c.b3.val = 0
    · simp [ClauseSat, litVal, assignment_67, assignment_200, v200, v67, hs]
    · simp [ClauseSat, litVal, assignment_67, assignment_200, v67, hs]
  have hc850 : ClauseSat (assignment c) [137,401] := by
    by_cases hs : c.b3.val = 1
    · simp [ClauseSat, litVal, assignment_68, assignment_200, v200, v68, hs]
    · simp [ClauseSat, litVal, assignment_68, assignment_200, v68, hs]
  have hc851 : ClauseSat (assignment c) [139,400] := by
    by_cases hs : c.b3.val = 2
    · simp [ClauseSat, litVal, assignment_69, assignment_200, v200, v69, hs]
    · simp [ClauseSat, litVal, assignment_69, assignment_200, v69, hs]
  have hc852 : ClauseSat (assignment c) [141,401] := by
    by_cases hs : c.b3.val = 3
    · simp [ClauseSat, litVal, assignment_70, assignment_200, v200, v70, hs]
    · simp [ClauseSat, litVal, assignment_70, assignment_200, v70, hs]
  have hc853 : ClauseSat (assignment c) [143,401,384] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_192, assignment_200, v200, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_192, assignment_200, v71, hs]
  have hc854 : ClauseSat (assignment c) [143,400,385] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_192, assignment_200, v200, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_192, assignment_200, v71, hs]
  have hc855 : ClauseSat (assignment c) [145,401,390] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_195, assignment_200, v200, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_195, assignment_200, v72, hs]
  have hc856 : ClauseSat (assignment c) [145,400,391] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_195, assignment_200, v200, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_195, assignment_200, v72, hs]
  have hc857 : ClauseSat (assignment c) [147,401,396] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_198, assignment_200, v200, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_198, assignment_200, v73, hs]
  have hc858 : ClauseSat (assignment c) [147,400,397] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_198, assignment_200, v200, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_198, assignment_200, v73, hs]
  have hc859 : ClauseSat (assignment c) [119,403,398] := by
    cases ha0 : v59 c <;> cases ha1 : v199 c <;> cases ha2 : v200 c <;> simp [ClauseSat, litVal, assignment_59, assignment_199, assignment_201, v201, ha0, ha1, ha2]
  have hc860 : ClauseSat (assignment c) [119,403,400] := by
    cases ha0 : v59 c <;> cases ha1 : v199 c <;> cases ha2 : v200 c <;> simp [ClauseSat, litVal, assignment_59, assignment_200, assignment_201, v201, ha0, ha1, ha2]
  have hc861 : ClauseSat (assignment c) [119,402,399,401] := by
    cases ha0 : v59 c <;> cases ha1 : v199 c <;> cases ha2 : v200 c <;> simp [ClauseSat, litVal, assignment_59, assignment_199, assignment_200, assignment_201, v201, ha0, ha1, ha2]
  have hc862 : ClauseSat (assignment c) [118,402,399] := by
    cases ha0 : v59 c <;> cases ha1 : v199 c <;> cases ha2 : v200 c <;> simp [ClauseSat, litVal, assignment_59, assignment_199, assignment_201, v201, ha0, ha1, ha2]
  have hc863 : ClauseSat (assignment c) [118,402,401] := by
    cases ha0 : v59 c <;> cases ha1 : v199 c <;> cases ha2 : v200 c <;> simp [ClauseSat, litVal, assignment_59, assignment_200, assignment_201, v201, ha0, ha1, ha2]
  have hc864 : ClauseSat (assignment c) [118,403,398,400] := by
    cases ha0 : v59 c <;> cases ha1 : v199 c <;> cases ha2 : v200 c <;> simp [ClauseSat, litVal, assignment_59, assignment_199, assignment_200, assignment_201, v201, ha0, ha1, ha2]
  have hc865 : ClauseSat (assignment c) [175,404] := by
    by_cases hs : c.a4.val = 0
    · simp [ClauseSat, litVal, assignment_87, assignment_202, v202, v87, hs]
    · simp [ClauseSat, litVal, assignment_87, assignment_202, v87, hs]
  have hc866 : ClauseSat (assignment c) [177,405] := by
    by_cases hs : c.a4.val = 1
    · simp [ClauseSat, litVal, assignment_88, assignment_202, v202, v88, hs]
    · simp [ClauseSat, litVal, assignment_88, assignment_202, v88, hs]
  have hc867 : ClauseSat (assignment c) [179,404] := by
    by_cases hs : c.a4.val = 2
    · simp [ClauseSat, litVal, assignment_89, assignment_202, v202, v89, hs]
    · simp [ClauseSat, litVal, assignment_89, assignment_202, v89, hs]
  have hc868 : ClauseSat (assignment c) [181,405] := by
    by_cases hs : c.a4.val = 3
    · simp [ClauseSat, litVal, assignment_90, assignment_202, v202, v90, hs]
    · simp [ClauseSat, litVal, assignment_90, assignment_202, v90, hs]
  have hc869 : ClauseSat (assignment c) [183,405,384] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_192, assignment_202, v202, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_192, assignment_202, v91, hs]
  have hc870 : ClauseSat (assignment c) [183,404,385] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_192, assignment_202, v202, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_192, assignment_202, v91, hs]
  have hc871 : ClauseSat (assignment c) [185,405,390] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_195, assignment_202, v202, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_195, assignment_202, v92, hs]
  have hc872 : ClauseSat (assignment c) [185,404,391] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_195, assignment_202, v202, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_195, assignment_202, v92, hs]
  have hc873 : ClauseSat (assignment c) [187,405,396] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_198, assignment_202, v202, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_198, assignment_202, v93, hs]
  have hc874 : ClauseSat (assignment c) [187,404,397] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_198, assignment_202, v202, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_198, assignment_202, v93, hs]
  have hc875 : ClauseSat (assignment c) [189,405,402] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_201, assignment_202, v202, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_201, assignment_202, v94, hs]
  have hc876 : ClauseSat (assignment c) [189,404,403] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_201, assignment_202, v202, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_201, assignment_202, v94, hs]
  have hc877 : ClauseSat (assignment c) [191,406] := by
    by_cases hs : c.b4.val = 0
    · simp [ClauseSat, litVal, assignment_95, assignment_203, v203, v95, hs]
    · simp [ClauseSat, litVal, assignment_95, assignment_203, v95, hs]
  have hc878 : ClauseSat (assignment c) [193,407] := by
    by_cases hs : c.b4.val = 1
    · simp [ClauseSat, litVal, assignment_96, assignment_203, v203, v96, hs]
    · simp [ClauseSat, litVal, assignment_96, assignment_203, v96, hs]
  have hc879 : ClauseSat (assignment c) [195,406] := by
    by_cases hs : c.b4.val = 2
    · simp [ClauseSat, litVal, assignment_97, assignment_203, v203, v97, hs]
    · simp [ClauseSat, litVal, assignment_97, assignment_203, v97, hs]
  have hc880 : ClauseSat (assignment c) [197,407] := by
    by_cases hs : c.b4.val = 3
    · simp [ClauseSat, litVal, assignment_98, assignment_203, v203, v98, hs]
    · simp [ClauseSat, litVal, assignment_98, assignment_203, v98, hs]
  have hc881 : ClauseSat (assignment c) [199,407,384] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_192, assignment_203, v203, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_192, assignment_203, v99, hs]
  have hc882 : ClauseSat (assignment c) [199,406,385] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_192, assignment_203, v203, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_192, assignment_203, v99, hs]
  have hc883 : ClauseSat (assignment c) [201,407,390] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_195, assignment_203, v203, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_195, assignment_203, v100, hs]
  have hc884 : ClauseSat (assignment c) [201,406,391] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_195, assignment_203, v203, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_195, assignment_203, v100, hs]
  have hc885 : ClauseSat (assignment c) [203,407,396] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_198, assignment_203, v203, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_198, assignment_203, v101, hs]
  have hc886 : ClauseSat (assignment c) [203,406,397] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_198, assignment_203, v203, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_198, assignment_203, v101, hs]
  have hc887 : ClauseSat (assignment c) [205,407,402] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_201, assignment_203, v203, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_201, assignment_203, v102, hs]
  have hc888 : ClauseSat (assignment c) [205,406,403] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_201, assignment_203, v203, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_201, assignment_203, v102, hs]
  have hc889 : ClauseSat (assignment c) [173,409,404] := by
    cases ha0 : v86 c <;> cases ha1 : v202 c <;> cases ha2 : v203 c <;> simp [ClauseSat, litVal, assignment_86, assignment_202, assignment_204, v204, ha0, ha1, ha2]
  have hc890 : ClauseSat (assignment c) [173,409,406] := by
    cases ha0 : v86 c <;> cases ha1 : v202 c <;> cases ha2 : v203 c <;> simp [ClauseSat, litVal, assignment_86, assignment_203, assignment_204, v204, ha0, ha1, ha2]
  have hc891 : ClauseSat (assignment c) [173,408,405,407] := by
    cases ha0 : v86 c <;> cases ha1 : v202 c <;> cases ha2 : v203 c <;> simp [ClauseSat, litVal, assignment_86, assignment_202, assignment_203, assignment_204, v204, ha0, ha1, ha2]
  have hc892 : ClauseSat (assignment c) [172,408,405] := by
    cases ha0 : v86 c <;> cases ha1 : v202 c <;> cases ha2 : v203 c <;> simp [ClauseSat, litVal, assignment_86, assignment_202, assignment_204, v204, ha0, ha1, ha2]
  have hc893 : ClauseSat (assignment c) [172,408,407] := by
    cases ha0 : v86 c <;> cases ha1 : v202 c <;> cases ha2 : v203 c <;> simp [ClauseSat, litVal, assignment_86, assignment_203, assignment_204, v204, ha0, ha1, ha2]
  have hc894 : ClauseSat (assignment c) [172,409,404,406] := by
    cases ha0 : v86 c <;> cases ha1 : v202 c <;> cases ha2 : v203 c <;> simp [ClauseSat, litVal, assignment_86, assignment_202, assignment_203, assignment_204, v204, ha0, ha1, ha2]
  have hc895 : ClauseSat (assignment c) [408] := by
    have hh := hr ⟨5, by decide⟩
    have ht : target ⟨5, by decide⟩ = true := by decide
    rw [ht] at hh
    simpa [ClauseSat, litVal, assignment_204, output] using hh
  have hc896 : ClauseSat (assignment c) [7,411] := by
    by_cases hs : c.a0.val = 0
    · simp [ClauseSat, litVal, assignment_3, assignment_205, v205, v3, hs]
    · simp [ClauseSat, litVal, assignment_3, assignment_205, v3, hs]
  have hc897 : ClauseSat (assignment c) [9,410] := by
    by_cases hs : c.a0.val = 1
    · simp [ClauseSat, litVal, assignment_4, assignment_205, v205, v4, hs]
    · simp [ClauseSat, litVal, assignment_4, assignment_205, v4, hs]
  have hc898 : ClauseSat (assignment c) [11,410] := by
    by_cases hs : c.a0.val = 2
    · simp [ClauseSat, litVal, assignment_5, assignment_205, v205, v5, hs]
    · simp [ClauseSat, litVal, assignment_5, assignment_205, v5, hs]
  have hc899 : ClauseSat (assignment c) [13,411] := by
    by_cases hs : c.a0.val = 3
    · simp [ClauseSat, litVal, assignment_6, assignment_205, v205, v6, hs]
    · simp [ClauseSat, litVal, assignment_6, assignment_205, v6, hs]
  simp only [chunk8, List.forall_mem_cons]
  exact ⟨hc800, hc801, hc802, hc803, hc804, hc805, hc806, hc807, hc808, hc809, hc810, hc811, hc812, hc813, hc814, hc815, hc816, hc817, hc818, hc819, hc820, hc821, hc822, hc823, hc824, hc825, hc826, hc827, hc828, hc829, hc830, hc831, hc832, hc833, hc834, hc835, hc836, hc837, hc838, hc839, hc840, hc841, hc842, hc843, hc844, hc845, hc846, hc847, hc848, hc849, hc850, hc851, hc852, hc853, hc854, hc855, hc856, hc857, hc858, hc859, hc860, hc861, hc862, hc863, hc864, hc865, hc866, hc867, hc868, hc869, hc870, hc871, hc872, hc873, hc874, hc875, hc876, hc877, hc878, hc879, hc880, hc881, hc882, hc883, hc884, hc885, hc886, hc887, hc888, hc889, hc890, hc891, hc892, hc893, hc894, hc895, hc896, hc897, hc898, hc899, by simp⟩
#check satChunk8

def chunk9 : List (List Nat) := [[15, 413], [17, 412], [19, 412], [21, 413], [5, 415, 410], [5, 415, 412], [5, 414, 411, 413], [4, 414, 411], [4, 414, 413], [4, 415, 410, 412], [37, 417], [39, 416], [41, 416], [43, 417], [45, 417, 414], [45, 416, 415], [47, 419], [49, 418], [51, 418], [53, 419], [55, 419, 414], [55, 418, 415], [35, 421, 416], [35, 421, 418], [35, 420, 417, 419], [34, 420, 417], [34, 420, 419], [34, 421, 416, 418], [75, 423], [77, 422], [79, 422], [81, 423], [83, 423, 414], [83, 422, 415], [85, 423, 420], [85, 422, 421], [87, 425], [89, 424], [91, 424], [93, 425], [95, 425, 414], [95, 424, 415], [97, 425, 420], [97, 424, 421], [73, 427, 422], [73, 427, 424], [73, 426, 423, 425], [72, 426, 423], [72, 426, 425], [72, 427, 422, 424], [121, 429], [123, 428], [125, 428], [127, 429], [129, 429, 414], [129, 428, 415], [131, 429, 420], [131, 428, 421], [133, 429, 426], [133, 428, 427], [135, 431], [137, 430], [139, 430], [141, 431], [143, 431, 414], [143, 430, 415], [145, 431, 420], [145, 430, 421], [147, 431, 426], [147, 430, 427], [119, 433, 428], [119, 433, 430], [119, 432, 429, 431], [118, 432, 429], [118, 432, 431], [118, 433, 428, 430], [175, 435], [177, 434], [179, 434], [181, 435], [183, 435, 414], [183, 434, 415], [185, 435, 420], [185, 434, 421], [187, 435, 426], [187, 434, 427], [189, 435, 432], [189, 434, 433], [191, 437], [193, 436], [195, 436], [197, 437], [199, 437, 414], [199, 436, 415], [201, 437, 420], [201, 436, 421], [203, 437, 426], [203, 436, 427], [205, 437, 432], [205, 436, 433]]
theorem satChunk9 (c : Candidate) (hv : valid c)
    (hr : ∀ r : Fin 16, output c r = target r)
    (hl : derivativeLeft c = false) (hd : derivativeRight c = false) :
    ∀ cl ∈ chunk9, ClauseSat (assignment c) cl := by
  rcases hv with ⟨h0, h1, h2, h3, h4⟩
  have hc900 : ClauseSat (assignment c) [15,413] := by
    by_cases hs : c.b0.val = 0
    · simp [ClauseSat, litVal, assignment_7, assignment_206, v206, v7, hs]
    · simp [ClauseSat, litVal, assignment_7, assignment_206, v7, hs]
  have hc901 : ClauseSat (assignment c) [17,412] := by
    by_cases hs : c.b0.val = 1
    · simp [ClauseSat, litVal, assignment_8, assignment_206, v206, v8, hs]
    · simp [ClauseSat, litVal, assignment_8, assignment_206, v8, hs]
  have hc902 : ClauseSat (assignment c) [19,412] := by
    by_cases hs : c.b0.val = 2
    · simp [ClauseSat, litVal, assignment_9, assignment_206, v206, v9, hs]
    · simp [ClauseSat, litVal, assignment_9, assignment_206, v9, hs]
  have hc903 : ClauseSat (assignment c) [21,413] := by
    by_cases hs : c.b0.val = 3
    · simp [ClauseSat, litVal, assignment_10, assignment_206, v206, v10, hs]
    · simp [ClauseSat, litVal, assignment_10, assignment_206, v10, hs]
  have hc904 : ClauseSat (assignment c) [5,415,410] := by
    cases ha0 : v2 c <;> cases ha1 : v205 c <;> cases ha2 : v206 c <;> simp [ClauseSat, litVal, assignment_2, assignment_205, assignment_207, v207, ha0, ha1, ha2]
  have hc905 : ClauseSat (assignment c) [5,415,412] := by
    cases ha0 : v2 c <;> cases ha1 : v205 c <;> cases ha2 : v206 c <;> simp [ClauseSat, litVal, assignment_2, assignment_206, assignment_207, v207, ha0, ha1, ha2]
  have hc906 : ClauseSat (assignment c) [5,414,411,413] := by
    cases ha0 : v2 c <;> cases ha1 : v205 c <;> cases ha2 : v206 c <;> simp [ClauseSat, litVal, assignment_2, assignment_205, assignment_206, assignment_207, v207, ha0, ha1, ha2]
  have hc907 : ClauseSat (assignment c) [4,414,411] := by
    cases ha0 : v2 c <;> cases ha1 : v205 c <;> cases ha2 : v206 c <;> simp [ClauseSat, litVal, assignment_2, assignment_205, assignment_207, v207, ha0, ha1, ha2]
  have hc908 : ClauseSat (assignment c) [4,414,413] := by
    cases ha0 : v2 c <;> cases ha1 : v205 c <;> cases ha2 : v206 c <;> simp [ClauseSat, litVal, assignment_2, assignment_206, assignment_207, v207, ha0, ha1, ha2]
  have hc909 : ClauseSat (assignment c) [4,415,410,412] := by
    cases ha0 : v2 c <;> cases ha1 : v205 c <;> cases ha2 : v206 c <;> simp [ClauseSat, litVal, assignment_2, assignment_205, assignment_206, assignment_207, v207, ha0, ha1, ha2]
  have hc910 : ClauseSat (assignment c) [37,417] := by
    by_cases hs : c.a1.val = 0
    · simp [ClauseSat, litVal, assignment_18, assignment_208, v208, v18, hs]
    · simp [ClauseSat, litVal, assignment_18, assignment_208, v18, hs]
  have hc911 : ClauseSat (assignment c) [39,416] := by
    by_cases hs : c.a1.val = 1
    · simp [ClauseSat, litVal, assignment_19, assignment_208, v208, v19, hs]
    · simp [ClauseSat, litVal, assignment_19, assignment_208, v19, hs]
  have hc912 : ClauseSat (assignment c) [41,416] := by
    by_cases hs : c.a1.val = 2
    · simp [ClauseSat, litVal, assignment_20, assignment_208, v208, v20, hs]
    · simp [ClauseSat, litVal, assignment_20, assignment_208, v20, hs]
  have hc913 : ClauseSat (assignment c) [43,417] := by
    by_cases hs : c.a1.val = 3
    · simp [ClauseSat, litVal, assignment_21, assignment_208, v208, v21, hs]
    · simp [ClauseSat, litVal, assignment_21, assignment_208, v21, hs]
  have hc914 : ClauseSat (assignment c) [45,417,414] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_207, assignment_208, v208, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_207, assignment_208, v22, hs]
  have hc915 : ClauseSat (assignment c) [45,416,415] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_207, assignment_208, v208, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_207, assignment_208, v22, hs]
  have hc916 : ClauseSat (assignment c) [47,419] := by
    by_cases hs : c.b1.val = 0
    · simp [ClauseSat, litVal, assignment_23, assignment_209, v209, v23, hs]
    · simp [ClauseSat, litVal, assignment_23, assignment_209, v23, hs]
  have hc917 : ClauseSat (assignment c) [49,418] := by
    by_cases hs : c.b1.val = 1
    · simp [ClauseSat, litVal, assignment_24, assignment_209, v209, v24, hs]
    · simp [ClauseSat, litVal, assignment_24, assignment_209, v24, hs]
  have hc918 : ClauseSat (assignment c) [51,418] := by
    by_cases hs : c.b1.val = 2
    · simp [ClauseSat, litVal, assignment_25, assignment_209, v209, v25, hs]
    · simp [ClauseSat, litVal, assignment_25, assignment_209, v25, hs]
  have hc919 : ClauseSat (assignment c) [53,419] := by
    by_cases hs : c.b1.val = 3
    · simp [ClauseSat, litVal, assignment_26, assignment_209, v209, v26, hs]
    · simp [ClauseSat, litVal, assignment_26, assignment_209, v26, hs]
  have hc920 : ClauseSat (assignment c) [55,419,414] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_207, assignment_209, v209, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_207, assignment_209, v27, hs]
  have hc921 : ClauseSat (assignment c) [55,418,415] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_207, assignment_209, v209, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_207, assignment_209, v27, hs]
  have hc922 : ClauseSat (assignment c) [35,421,416] := by
    cases ha0 : v17 c <;> cases ha1 : v208 c <;> cases ha2 : v209 c <;> simp [ClauseSat, litVal, assignment_17, assignment_208, assignment_210, v210, ha0, ha1, ha2]
  have hc923 : ClauseSat (assignment c) [35,421,418] := by
    cases ha0 : v17 c <;> cases ha1 : v208 c <;> cases ha2 : v209 c <;> simp [ClauseSat, litVal, assignment_17, assignment_209, assignment_210, v210, ha0, ha1, ha2]
  have hc924 : ClauseSat (assignment c) [35,420,417,419] := by
    cases ha0 : v17 c <;> cases ha1 : v208 c <;> cases ha2 : v209 c <;> simp [ClauseSat, litVal, assignment_17, assignment_208, assignment_209, assignment_210, v210, ha0, ha1, ha2]
  have hc925 : ClauseSat (assignment c) [34,420,417] := by
    cases ha0 : v17 c <;> cases ha1 : v208 c <;> cases ha2 : v209 c <;> simp [ClauseSat, litVal, assignment_17, assignment_208, assignment_210, v210, ha0, ha1, ha2]
  have hc926 : ClauseSat (assignment c) [34,420,419] := by
    cases ha0 : v17 c <;> cases ha1 : v208 c <;> cases ha2 : v209 c <;> simp [ClauseSat, litVal, assignment_17, assignment_209, assignment_210, v210, ha0, ha1, ha2]
  have hc927 : ClauseSat (assignment c) [34,421,416,418] := by
    cases ha0 : v17 c <;> cases ha1 : v208 c <;> cases ha2 : v209 c <;> simp [ClauseSat, litVal, assignment_17, assignment_208, assignment_209, assignment_210, v210, ha0, ha1, ha2]
  have hc928 : ClauseSat (assignment c) [75,423] := by
    by_cases hs : c.a2.val = 0
    · simp [ClauseSat, litVal, assignment_37, assignment_211, v211, v37, hs]
    · simp [ClauseSat, litVal, assignment_37, assignment_211, v37, hs]
  have hc929 : ClauseSat (assignment c) [77,422] := by
    by_cases hs : c.a2.val = 1
    · simp [ClauseSat, litVal, assignment_38, assignment_211, v211, v38, hs]
    · simp [ClauseSat, litVal, assignment_38, assignment_211, v38, hs]
  have hc930 : ClauseSat (assignment c) [79,422] := by
    by_cases hs : c.a2.val = 2
    · simp [ClauseSat, litVal, assignment_39, assignment_211, v211, v39, hs]
    · simp [ClauseSat, litVal, assignment_39, assignment_211, v39, hs]
  have hc931 : ClauseSat (assignment c) [81,423] := by
    by_cases hs : c.a2.val = 3
    · simp [ClauseSat, litVal, assignment_40, assignment_211, v211, v40, hs]
    · simp [ClauseSat, litVal, assignment_40, assignment_211, v40, hs]
  have hc932 : ClauseSat (assignment c) [83,423,414] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_207, assignment_211, v211, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_207, assignment_211, v41, hs]
  have hc933 : ClauseSat (assignment c) [83,422,415] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_207, assignment_211, v211, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_207, assignment_211, v41, hs]
  have hc934 : ClauseSat (assignment c) [85,423,420] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_210, assignment_211, v211, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_210, assignment_211, v42, hs]
  have hc935 : ClauseSat (assignment c) [85,422,421] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_210, assignment_211, v211, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_210, assignment_211, v42, hs]
  have hc936 : ClauseSat (assignment c) [87,425] := by
    by_cases hs : c.b2.val = 0
    · simp [ClauseSat, litVal, assignment_43, assignment_212, v212, v43, hs]
    · simp [ClauseSat, litVal, assignment_43, assignment_212, v43, hs]
  have hc937 : ClauseSat (assignment c) [89,424] := by
    by_cases hs : c.b2.val = 1
    · simp [ClauseSat, litVal, assignment_44, assignment_212, v212, v44, hs]
    · simp [ClauseSat, litVal, assignment_44, assignment_212, v44, hs]
  have hc938 : ClauseSat (assignment c) [91,424] := by
    by_cases hs : c.b2.val = 2
    · simp [ClauseSat, litVal, assignment_45, assignment_212, v212, v45, hs]
    · simp [ClauseSat, litVal, assignment_45, assignment_212, v45, hs]
  have hc939 : ClauseSat (assignment c) [93,425] := by
    by_cases hs : c.b2.val = 3
    · simp [ClauseSat, litVal, assignment_46, assignment_212, v212, v46, hs]
    · simp [ClauseSat, litVal, assignment_46, assignment_212, v46, hs]
  have hc940 : ClauseSat (assignment c) [95,425,414] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_207, assignment_212, v212, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_207, assignment_212, v47, hs]
  have hc941 : ClauseSat (assignment c) [95,424,415] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_207, assignment_212, v212, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_207, assignment_212, v47, hs]
  have hc942 : ClauseSat (assignment c) [97,425,420] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_210, assignment_212, v212, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_210, assignment_212, v48, hs]
  have hc943 : ClauseSat (assignment c) [97,424,421] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_210, assignment_212, v212, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_210, assignment_212, v48, hs]
  have hc944 : ClauseSat (assignment c) [73,427,422] := by
    cases ha0 : v36 c <;> cases ha1 : v211 c <;> cases ha2 : v212 c <;> simp [ClauseSat, litVal, assignment_36, assignment_211, assignment_213, v213, ha0, ha1, ha2]
  have hc945 : ClauseSat (assignment c) [73,427,424] := by
    cases ha0 : v36 c <;> cases ha1 : v211 c <;> cases ha2 : v212 c <;> simp [ClauseSat, litVal, assignment_36, assignment_212, assignment_213, v213, ha0, ha1, ha2]
  have hc946 : ClauseSat (assignment c) [73,426,423,425] := by
    cases ha0 : v36 c <;> cases ha1 : v211 c <;> cases ha2 : v212 c <;> simp [ClauseSat, litVal, assignment_36, assignment_211, assignment_212, assignment_213, v213, ha0, ha1, ha2]
  have hc947 : ClauseSat (assignment c) [72,426,423] := by
    cases ha0 : v36 c <;> cases ha1 : v211 c <;> cases ha2 : v212 c <;> simp [ClauseSat, litVal, assignment_36, assignment_211, assignment_213, v213, ha0, ha1, ha2]
  have hc948 : ClauseSat (assignment c) [72,426,425] := by
    cases ha0 : v36 c <;> cases ha1 : v211 c <;> cases ha2 : v212 c <;> simp [ClauseSat, litVal, assignment_36, assignment_212, assignment_213, v213, ha0, ha1, ha2]
  have hc949 : ClauseSat (assignment c) [72,427,422,424] := by
    cases ha0 : v36 c <;> cases ha1 : v211 c <;> cases ha2 : v212 c <;> simp [ClauseSat, litVal, assignment_36, assignment_211, assignment_212, assignment_213, v213, ha0, ha1, ha2]
  have hc950 : ClauseSat (assignment c) [121,429] := by
    by_cases hs : c.a3.val = 0
    · simp [ClauseSat, litVal, assignment_60, assignment_214, v214, v60, hs]
    · simp [ClauseSat, litVal, assignment_60, assignment_214, v60, hs]
  have hc951 : ClauseSat (assignment c) [123,428] := by
    by_cases hs : c.a3.val = 1
    · simp [ClauseSat, litVal, assignment_61, assignment_214, v214, v61, hs]
    · simp [ClauseSat, litVal, assignment_61, assignment_214, v61, hs]
  have hc952 : ClauseSat (assignment c) [125,428] := by
    by_cases hs : c.a3.val = 2
    · simp [ClauseSat, litVal, assignment_62, assignment_214, v214, v62, hs]
    · simp [ClauseSat, litVal, assignment_62, assignment_214, v62, hs]
  have hc953 : ClauseSat (assignment c) [127,429] := by
    by_cases hs : c.a3.val = 3
    · simp [ClauseSat, litVal, assignment_63, assignment_214, v214, v63, hs]
    · simp [ClauseSat, litVal, assignment_63, assignment_214, v63, hs]
  have hc954 : ClauseSat (assignment c) [129,429,414] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_207, assignment_214, v214, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_207, assignment_214, v64, hs]
  have hc955 : ClauseSat (assignment c) [129,428,415] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_207, assignment_214, v214, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_207, assignment_214, v64, hs]
  have hc956 : ClauseSat (assignment c) [131,429,420] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_210, assignment_214, v214, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_210, assignment_214, v65, hs]
  have hc957 : ClauseSat (assignment c) [131,428,421] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_210, assignment_214, v214, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_210, assignment_214, v65, hs]
  have hc958 : ClauseSat (assignment c) [133,429,426] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_213, assignment_214, v214, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_213, assignment_214, v66, hs]
  have hc959 : ClauseSat (assignment c) [133,428,427] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_213, assignment_214, v214, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_213, assignment_214, v66, hs]
  have hc960 : ClauseSat (assignment c) [135,431] := by
    by_cases hs : c.b3.val = 0
    · simp [ClauseSat, litVal, assignment_67, assignment_215, v215, v67, hs]
    · simp [ClauseSat, litVal, assignment_67, assignment_215, v67, hs]
  have hc961 : ClauseSat (assignment c) [137,430] := by
    by_cases hs : c.b3.val = 1
    · simp [ClauseSat, litVal, assignment_68, assignment_215, v215, v68, hs]
    · simp [ClauseSat, litVal, assignment_68, assignment_215, v68, hs]
  have hc962 : ClauseSat (assignment c) [139,430] := by
    by_cases hs : c.b3.val = 2
    · simp [ClauseSat, litVal, assignment_69, assignment_215, v215, v69, hs]
    · simp [ClauseSat, litVal, assignment_69, assignment_215, v69, hs]
  have hc963 : ClauseSat (assignment c) [141,431] := by
    by_cases hs : c.b3.val = 3
    · simp [ClauseSat, litVal, assignment_70, assignment_215, v215, v70, hs]
    · simp [ClauseSat, litVal, assignment_70, assignment_215, v70, hs]
  have hc964 : ClauseSat (assignment c) [143,431,414] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_207, assignment_215, v215, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_207, assignment_215, v71, hs]
  have hc965 : ClauseSat (assignment c) [143,430,415] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_207, assignment_215, v215, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_207, assignment_215, v71, hs]
  have hc966 : ClauseSat (assignment c) [145,431,420] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_210, assignment_215, v215, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_210, assignment_215, v72, hs]
  have hc967 : ClauseSat (assignment c) [145,430,421] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_210, assignment_215, v215, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_210, assignment_215, v72, hs]
  have hc968 : ClauseSat (assignment c) [147,431,426] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_213, assignment_215, v215, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_213, assignment_215, v73, hs]
  have hc969 : ClauseSat (assignment c) [147,430,427] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_213, assignment_215, v215, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_213, assignment_215, v73, hs]
  have hc970 : ClauseSat (assignment c) [119,433,428] := by
    cases ha0 : v59 c <;> cases ha1 : v214 c <;> cases ha2 : v215 c <;> simp [ClauseSat, litVal, assignment_59, assignment_214, assignment_216, v216, ha0, ha1, ha2]
  have hc971 : ClauseSat (assignment c) [119,433,430] := by
    cases ha0 : v59 c <;> cases ha1 : v214 c <;> cases ha2 : v215 c <;> simp [ClauseSat, litVal, assignment_59, assignment_215, assignment_216, v216, ha0, ha1, ha2]
  have hc972 : ClauseSat (assignment c) [119,432,429,431] := by
    cases ha0 : v59 c <;> cases ha1 : v214 c <;> cases ha2 : v215 c <;> simp [ClauseSat, litVal, assignment_59, assignment_214, assignment_215, assignment_216, v216, ha0, ha1, ha2]
  have hc973 : ClauseSat (assignment c) [118,432,429] := by
    cases ha0 : v59 c <;> cases ha1 : v214 c <;> cases ha2 : v215 c <;> simp [ClauseSat, litVal, assignment_59, assignment_214, assignment_216, v216, ha0, ha1, ha2]
  have hc974 : ClauseSat (assignment c) [118,432,431] := by
    cases ha0 : v59 c <;> cases ha1 : v214 c <;> cases ha2 : v215 c <;> simp [ClauseSat, litVal, assignment_59, assignment_215, assignment_216, v216, ha0, ha1, ha2]
  have hc975 : ClauseSat (assignment c) [118,433,428,430] := by
    cases ha0 : v59 c <;> cases ha1 : v214 c <;> cases ha2 : v215 c <;> simp [ClauseSat, litVal, assignment_59, assignment_214, assignment_215, assignment_216, v216, ha0, ha1, ha2]
  have hc976 : ClauseSat (assignment c) [175,435] := by
    by_cases hs : c.a4.val = 0
    · simp [ClauseSat, litVal, assignment_87, assignment_217, v217, v87, hs]
    · simp [ClauseSat, litVal, assignment_87, assignment_217, v87, hs]
  have hc977 : ClauseSat (assignment c) [177,434] := by
    by_cases hs : c.a4.val = 1
    · simp [ClauseSat, litVal, assignment_88, assignment_217, v217, v88, hs]
    · simp [ClauseSat, litVal, assignment_88, assignment_217, v88, hs]
  have hc978 : ClauseSat (assignment c) [179,434] := by
    by_cases hs : c.a4.val = 2
    · simp [ClauseSat, litVal, assignment_89, assignment_217, v217, v89, hs]
    · simp [ClauseSat, litVal, assignment_89, assignment_217, v89, hs]
  have hc979 : ClauseSat (assignment c) [181,435] := by
    by_cases hs : c.a4.val = 3
    · simp [ClauseSat, litVal, assignment_90, assignment_217, v217, v90, hs]
    · simp [ClauseSat, litVal, assignment_90, assignment_217, v90, hs]
  have hc980 : ClauseSat (assignment c) [183,435,414] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_207, assignment_217, v217, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_207, assignment_217, v91, hs]
  have hc981 : ClauseSat (assignment c) [183,434,415] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_207, assignment_217, v217, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_207, assignment_217, v91, hs]
  have hc982 : ClauseSat (assignment c) [185,435,420] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_210, assignment_217, v217, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_210, assignment_217, v92, hs]
  have hc983 : ClauseSat (assignment c) [185,434,421] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_210, assignment_217, v217, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_210, assignment_217, v92, hs]
  have hc984 : ClauseSat (assignment c) [187,435,426] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_213, assignment_217, v217, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_213, assignment_217, v93, hs]
  have hc985 : ClauseSat (assignment c) [187,434,427] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_213, assignment_217, v217, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_213, assignment_217, v93, hs]
  have hc986 : ClauseSat (assignment c) [189,435,432] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_216, assignment_217, v217, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_216, assignment_217, v94, hs]
  have hc987 : ClauseSat (assignment c) [189,434,433] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_216, assignment_217, v217, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_216, assignment_217, v94, hs]
  have hc988 : ClauseSat (assignment c) [191,437] := by
    by_cases hs : c.b4.val = 0
    · simp [ClauseSat, litVal, assignment_95, assignment_218, v218, v95, hs]
    · simp [ClauseSat, litVal, assignment_95, assignment_218, v95, hs]
  have hc989 : ClauseSat (assignment c) [193,436] := by
    by_cases hs : c.b4.val = 1
    · simp [ClauseSat, litVal, assignment_96, assignment_218, v218, v96, hs]
    · simp [ClauseSat, litVal, assignment_96, assignment_218, v96, hs]
  have hc990 : ClauseSat (assignment c) [195,436] := by
    by_cases hs : c.b4.val = 2
    · simp [ClauseSat, litVal, assignment_97, assignment_218, v218, v97, hs]
    · simp [ClauseSat, litVal, assignment_97, assignment_218, v97, hs]
  have hc991 : ClauseSat (assignment c) [197,437] := by
    by_cases hs : c.b4.val = 3
    · simp [ClauseSat, litVal, assignment_98, assignment_218, v218, v98, hs]
    · simp [ClauseSat, litVal, assignment_98, assignment_218, v98, hs]
  have hc992 : ClauseSat (assignment c) [199,437,414] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_207, assignment_218, v218, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_207, assignment_218, v99, hs]
  have hc993 : ClauseSat (assignment c) [199,436,415] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_207, assignment_218, v218, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_207, assignment_218, v99, hs]
  have hc994 : ClauseSat (assignment c) [201,437,420] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_210, assignment_218, v218, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_210, assignment_218, v100, hs]
  have hc995 : ClauseSat (assignment c) [201,436,421] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_210, assignment_218, v218, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_210, assignment_218, v100, hs]
  have hc996 : ClauseSat (assignment c) [203,437,426] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_213, assignment_218, v218, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_213, assignment_218, v101, hs]
  have hc997 : ClauseSat (assignment c) [203,436,427] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_213, assignment_218, v218, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_213, assignment_218, v101, hs]
  have hc998 : ClauseSat (assignment c) [205,437,432] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_216, assignment_218, v218, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_216, assignment_218, v102, hs]
  have hc999 : ClauseSat (assignment c) [205,436,433] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_216, assignment_218, v218, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_216, assignment_218, v102, hs]
  simp only [chunk9, List.forall_mem_cons]
  exact ⟨hc900, hc901, hc902, hc903, hc904, hc905, hc906, hc907, hc908, hc909, hc910, hc911, hc912, hc913, hc914, hc915, hc916, hc917, hc918, hc919, hc920, hc921, hc922, hc923, hc924, hc925, hc926, hc927, hc928, hc929, hc930, hc931, hc932, hc933, hc934, hc935, hc936, hc937, hc938, hc939, hc940, hc941, hc942, hc943, hc944, hc945, hc946, hc947, hc948, hc949, hc950, hc951, hc952, hc953, hc954, hc955, hc956, hc957, hc958, hc959, hc960, hc961, hc962, hc963, hc964, hc965, hc966, hc967, hc968, hc969, hc970, hc971, hc972, hc973, hc974, hc975, hc976, hc977, hc978, hc979, hc980, hc981, hc982, hc983, hc984, hc985, hc986, hc987, hc988, hc989, hc990, hc991, hc992, hc993, hc994, hc995, hc996, hc997, hc998, hc999, by simp⟩
#check satChunk9

def chunk10 : List (List Nat) := [[173, 439, 434], [173, 439, 436], [173, 438, 435, 437], [172, 438, 435], [172, 438, 437], [172, 439, 434, 436], [439], [7, 440], [9, 440], [11, 440], [13, 441], [15, 442], [17, 442], [19, 442], [21, 443], [5, 445, 440], [5, 445, 442], [5, 444, 441, 443], [4, 444, 441], [4, 444, 443], [4, 445, 440, 442], [37, 446], [39, 446], [41, 446], [43, 447], [45, 447, 444], [45, 446, 445], [47, 448], [49, 448], [51, 448], [53, 449], [55, 449, 444], [55, 448, 445], [35, 451, 446], [35, 451, 448], [35, 450, 447, 449], [34, 450, 447], [34, 450, 449], [34, 451, 446, 448], [75, 452], [77, 452], [79, 452], [81, 453], [83, 453, 444], [83, 452, 445], [85, 453, 450], [85, 452, 451], [87, 454], [89, 454], [91, 454], [93, 455], [95, 455, 444], [95, 454, 445], [97, 455, 450], [97, 454, 451], [73, 457, 452], [73, 457, 454], [73, 456, 453, 455], [72, 456, 453], [72, 456, 455], [72, 457, 452, 454], [121, 458], [123, 458], [125, 458], [127, 459], [129, 459, 444], [129, 458, 445], [131, 459, 450], [131, 458, 451], [133, 459, 456], [133, 458, 457], [135, 460], [137, 460], [139, 460], [141, 461], [143, 461, 444], [143, 460, 445], [145, 461, 450], [145, 460, 451], [147, 461, 456], [147, 460, 457], [119, 463, 458], [119, 463, 460], [119, 462, 459, 461], [118, 462, 459], [118, 462, 461], [118, 463, 458, 460], [175, 464], [177, 464], [179, 464], [181, 465], [183, 465, 444], [183, 464, 445], [185, 465, 450], [185, 464, 451], [187, 465, 456], [187, 464, 457], [189, 465, 462], [189, 464, 463], [191, 466]]
theorem satChunk10 (c : Candidate) (hv : valid c)
    (hr : ∀ r : Fin 16, output c r = target r)
    (hl : derivativeLeft c = false) (hd : derivativeRight c = false) :
    ∀ cl ∈ chunk10, ClauseSat (assignment c) cl := by
  rcases hv with ⟨h0, h1, h2, h3, h4⟩
  have hc1000 : ClauseSat (assignment c) [173,439,434] := by
    cases ha0 : v86 c <;> cases ha1 : v217 c <;> cases ha2 : v218 c <;> simp [ClauseSat, litVal, assignment_86, assignment_217, assignment_219, v219, ha0, ha1, ha2]
  have hc1001 : ClauseSat (assignment c) [173,439,436] := by
    cases ha0 : v86 c <;> cases ha1 : v217 c <;> cases ha2 : v218 c <;> simp [ClauseSat, litVal, assignment_86, assignment_218, assignment_219, v219, ha0, ha1, ha2]
  have hc1002 : ClauseSat (assignment c) [173,438,435,437] := by
    cases ha0 : v86 c <;> cases ha1 : v217 c <;> cases ha2 : v218 c <;> simp [ClauseSat, litVal, assignment_86, assignment_217, assignment_218, assignment_219, v219, ha0, ha1, ha2]
  have hc1003 : ClauseSat (assignment c) [172,438,435] := by
    cases ha0 : v86 c <;> cases ha1 : v217 c <;> cases ha2 : v218 c <;> simp [ClauseSat, litVal, assignment_86, assignment_217, assignment_219, v219, ha0, ha1, ha2]
  have hc1004 : ClauseSat (assignment c) [172,438,437] := by
    cases ha0 : v86 c <;> cases ha1 : v217 c <;> cases ha2 : v218 c <;> simp [ClauseSat, litVal, assignment_86, assignment_218, assignment_219, v219, ha0, ha1, ha2]
  have hc1005 : ClauseSat (assignment c) [172,439,434,436] := by
    cases ha0 : v86 c <;> cases ha1 : v217 c <;> cases ha2 : v218 c <;> simp [ClauseSat, litVal, assignment_86, assignment_217, assignment_218, assignment_219, v219, ha0, ha1, ha2]
  have hc1006 : ClauseSat (assignment c) [439] := by
    have hh := hr ⟨6, by decide⟩
    have ht : target ⟨6, by decide⟩ = false := by decide
    rw [ht] at hh
    simpa [ClauseSat, litVal, assignment_219, output] using hh
  have hc1007 : ClauseSat (assignment c) [7,440] := by
    by_cases hs : c.a0.val = 0
    · simp [ClauseSat, litVal, assignment_3, assignment_220, v220, v3, hs]
    · simp [ClauseSat, litVal, assignment_3, assignment_220, v3, hs]
  have hc1008 : ClauseSat (assignment c) [9,440] := by
    by_cases hs : c.a0.val = 1
    · simp [ClauseSat, litVal, assignment_4, assignment_220, v220, v4, hs]
    · simp [ClauseSat, litVal, assignment_4, assignment_220, v4, hs]
  have hc1009 : ClauseSat (assignment c) [11,440] := by
    by_cases hs : c.a0.val = 2
    · simp [ClauseSat, litVal, assignment_5, assignment_220, v220, v5, hs]
    · simp [ClauseSat, litVal, assignment_5, assignment_220, v5, hs]
  have hc1010 : ClauseSat (assignment c) [13,441] := by
    by_cases hs : c.a0.val = 3
    · simp [ClauseSat, litVal, assignment_6, assignment_220, v220, v6, hs]
    · simp [ClauseSat, litVal, assignment_6, assignment_220, v6, hs]
  have hc1011 : ClauseSat (assignment c) [15,442] := by
    by_cases hs : c.b0.val = 0
    · simp [ClauseSat, litVal, assignment_7, assignment_221, v221, v7, hs]
    · simp [ClauseSat, litVal, assignment_7, assignment_221, v7, hs]
  have hc1012 : ClauseSat (assignment c) [17,442] := by
    by_cases hs : c.b0.val = 1
    · simp [ClauseSat, litVal, assignment_8, assignment_221, v221, v8, hs]
    · simp [ClauseSat, litVal, assignment_8, assignment_221, v8, hs]
  have hc1013 : ClauseSat (assignment c) [19,442] := by
    by_cases hs : c.b0.val = 2
    · simp [ClauseSat, litVal, assignment_9, assignment_221, v221, v9, hs]
    · simp [ClauseSat, litVal, assignment_9, assignment_221, v9, hs]
  have hc1014 : ClauseSat (assignment c) [21,443] := by
    by_cases hs : c.b0.val = 3
    · simp [ClauseSat, litVal, assignment_10, assignment_221, v221, v10, hs]
    · simp [ClauseSat, litVal, assignment_10, assignment_221, v10, hs]
  have hc1015 : ClauseSat (assignment c) [5,445,440] := by
    cases ha0 : v2 c <;> cases ha1 : v220 c <;> cases ha2 : v221 c <;> simp [ClauseSat, litVal, assignment_2, assignment_220, assignment_222, v222, ha0, ha1, ha2]
  have hc1016 : ClauseSat (assignment c) [5,445,442] := by
    cases ha0 : v2 c <;> cases ha1 : v220 c <;> cases ha2 : v221 c <;> simp [ClauseSat, litVal, assignment_2, assignment_221, assignment_222, v222, ha0, ha1, ha2]
  have hc1017 : ClauseSat (assignment c) [5,444,441,443] := by
    cases ha0 : v2 c <;> cases ha1 : v220 c <;> cases ha2 : v221 c <;> simp [ClauseSat, litVal, assignment_2, assignment_220, assignment_221, assignment_222, v222, ha0, ha1, ha2]
  have hc1018 : ClauseSat (assignment c) [4,444,441] := by
    cases ha0 : v2 c <;> cases ha1 : v220 c <;> cases ha2 : v221 c <;> simp [ClauseSat, litVal, assignment_2, assignment_220, assignment_222, v222, ha0, ha1, ha2]
  have hc1019 : ClauseSat (assignment c) [4,444,443] := by
    cases ha0 : v2 c <;> cases ha1 : v220 c <;> cases ha2 : v221 c <;> simp [ClauseSat, litVal, assignment_2, assignment_221, assignment_222, v222, ha0, ha1, ha2]
  have hc1020 : ClauseSat (assignment c) [4,445,440,442] := by
    cases ha0 : v2 c <;> cases ha1 : v220 c <;> cases ha2 : v221 c <;> simp [ClauseSat, litVal, assignment_2, assignment_220, assignment_221, assignment_222, v222, ha0, ha1, ha2]
  have hc1021 : ClauseSat (assignment c) [37,446] := by
    by_cases hs : c.a1.val = 0
    · simp [ClauseSat, litVal, assignment_18, assignment_223, v223, v18, hs]
    · simp [ClauseSat, litVal, assignment_18, assignment_223, v18, hs]
  have hc1022 : ClauseSat (assignment c) [39,446] := by
    by_cases hs : c.a1.val = 1
    · simp [ClauseSat, litVal, assignment_19, assignment_223, v223, v19, hs]
    · simp [ClauseSat, litVal, assignment_19, assignment_223, v19, hs]
  have hc1023 : ClauseSat (assignment c) [41,446] := by
    by_cases hs : c.a1.val = 2
    · simp [ClauseSat, litVal, assignment_20, assignment_223, v223, v20, hs]
    · simp [ClauseSat, litVal, assignment_20, assignment_223, v20, hs]
  have hc1024 : ClauseSat (assignment c) [43,447] := by
    by_cases hs : c.a1.val = 3
    · simp [ClauseSat, litVal, assignment_21, assignment_223, v223, v21, hs]
    · simp [ClauseSat, litVal, assignment_21, assignment_223, v21, hs]
  have hc1025 : ClauseSat (assignment c) [45,447,444] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_222, assignment_223, v223, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_222, assignment_223, v22, hs]
  have hc1026 : ClauseSat (assignment c) [45,446,445] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_222, assignment_223, v223, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_222, assignment_223, v22, hs]
  have hc1027 : ClauseSat (assignment c) [47,448] := by
    by_cases hs : c.b1.val = 0
    · simp [ClauseSat, litVal, assignment_23, assignment_224, v224, v23, hs]
    · simp [ClauseSat, litVal, assignment_23, assignment_224, v23, hs]
  have hc1028 : ClauseSat (assignment c) [49,448] := by
    by_cases hs : c.b1.val = 1
    · simp [ClauseSat, litVal, assignment_24, assignment_224, v224, v24, hs]
    · simp [ClauseSat, litVal, assignment_24, assignment_224, v24, hs]
  have hc1029 : ClauseSat (assignment c) [51,448] := by
    by_cases hs : c.b1.val = 2
    · simp [ClauseSat, litVal, assignment_25, assignment_224, v224, v25, hs]
    · simp [ClauseSat, litVal, assignment_25, assignment_224, v25, hs]
  have hc1030 : ClauseSat (assignment c) [53,449] := by
    by_cases hs : c.b1.val = 3
    · simp [ClauseSat, litVal, assignment_26, assignment_224, v224, v26, hs]
    · simp [ClauseSat, litVal, assignment_26, assignment_224, v26, hs]
  have hc1031 : ClauseSat (assignment c) [55,449,444] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_222, assignment_224, v224, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_222, assignment_224, v27, hs]
  have hc1032 : ClauseSat (assignment c) [55,448,445] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_222, assignment_224, v224, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_222, assignment_224, v27, hs]
  have hc1033 : ClauseSat (assignment c) [35,451,446] := by
    cases ha0 : v17 c <;> cases ha1 : v223 c <;> cases ha2 : v224 c <;> simp [ClauseSat, litVal, assignment_17, assignment_223, assignment_225, v225, ha0, ha1, ha2]
  have hc1034 : ClauseSat (assignment c) [35,451,448] := by
    cases ha0 : v17 c <;> cases ha1 : v223 c <;> cases ha2 : v224 c <;> simp [ClauseSat, litVal, assignment_17, assignment_224, assignment_225, v225, ha0, ha1, ha2]
  have hc1035 : ClauseSat (assignment c) [35,450,447,449] := by
    cases ha0 : v17 c <;> cases ha1 : v223 c <;> cases ha2 : v224 c <;> simp [ClauseSat, litVal, assignment_17, assignment_223, assignment_224, assignment_225, v225, ha0, ha1, ha2]
  have hc1036 : ClauseSat (assignment c) [34,450,447] := by
    cases ha0 : v17 c <;> cases ha1 : v223 c <;> cases ha2 : v224 c <;> simp [ClauseSat, litVal, assignment_17, assignment_223, assignment_225, v225, ha0, ha1, ha2]
  have hc1037 : ClauseSat (assignment c) [34,450,449] := by
    cases ha0 : v17 c <;> cases ha1 : v223 c <;> cases ha2 : v224 c <;> simp [ClauseSat, litVal, assignment_17, assignment_224, assignment_225, v225, ha0, ha1, ha2]
  have hc1038 : ClauseSat (assignment c) [34,451,446,448] := by
    cases ha0 : v17 c <;> cases ha1 : v223 c <;> cases ha2 : v224 c <;> simp [ClauseSat, litVal, assignment_17, assignment_223, assignment_224, assignment_225, v225, ha0, ha1, ha2]
  have hc1039 : ClauseSat (assignment c) [75,452] := by
    by_cases hs : c.a2.val = 0
    · simp [ClauseSat, litVal, assignment_37, assignment_226, v226, v37, hs]
    · simp [ClauseSat, litVal, assignment_37, assignment_226, v37, hs]
  have hc1040 : ClauseSat (assignment c) [77,452] := by
    by_cases hs : c.a2.val = 1
    · simp [ClauseSat, litVal, assignment_38, assignment_226, v226, v38, hs]
    · simp [ClauseSat, litVal, assignment_38, assignment_226, v38, hs]
  have hc1041 : ClauseSat (assignment c) [79,452] := by
    by_cases hs : c.a2.val = 2
    · simp [ClauseSat, litVal, assignment_39, assignment_226, v226, v39, hs]
    · simp [ClauseSat, litVal, assignment_39, assignment_226, v39, hs]
  have hc1042 : ClauseSat (assignment c) [81,453] := by
    by_cases hs : c.a2.val = 3
    · simp [ClauseSat, litVal, assignment_40, assignment_226, v226, v40, hs]
    · simp [ClauseSat, litVal, assignment_40, assignment_226, v40, hs]
  have hc1043 : ClauseSat (assignment c) [83,453,444] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_222, assignment_226, v226, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_222, assignment_226, v41, hs]
  have hc1044 : ClauseSat (assignment c) [83,452,445] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_222, assignment_226, v226, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_222, assignment_226, v41, hs]
  have hc1045 : ClauseSat (assignment c) [85,453,450] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_225, assignment_226, v226, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_225, assignment_226, v42, hs]
  have hc1046 : ClauseSat (assignment c) [85,452,451] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_225, assignment_226, v226, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_225, assignment_226, v42, hs]
  have hc1047 : ClauseSat (assignment c) [87,454] := by
    by_cases hs : c.b2.val = 0
    · simp [ClauseSat, litVal, assignment_43, assignment_227, v227, v43, hs]
    · simp [ClauseSat, litVal, assignment_43, assignment_227, v43, hs]
  have hc1048 : ClauseSat (assignment c) [89,454] := by
    by_cases hs : c.b2.val = 1
    · simp [ClauseSat, litVal, assignment_44, assignment_227, v227, v44, hs]
    · simp [ClauseSat, litVal, assignment_44, assignment_227, v44, hs]
  have hc1049 : ClauseSat (assignment c) [91,454] := by
    by_cases hs : c.b2.val = 2
    · simp [ClauseSat, litVal, assignment_45, assignment_227, v227, v45, hs]
    · simp [ClauseSat, litVal, assignment_45, assignment_227, v45, hs]
  have hc1050 : ClauseSat (assignment c) [93,455] := by
    by_cases hs : c.b2.val = 3
    · simp [ClauseSat, litVal, assignment_46, assignment_227, v227, v46, hs]
    · simp [ClauseSat, litVal, assignment_46, assignment_227, v46, hs]
  have hc1051 : ClauseSat (assignment c) [95,455,444] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_222, assignment_227, v227, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_222, assignment_227, v47, hs]
  have hc1052 : ClauseSat (assignment c) [95,454,445] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_222, assignment_227, v227, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_222, assignment_227, v47, hs]
  have hc1053 : ClauseSat (assignment c) [97,455,450] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_225, assignment_227, v227, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_225, assignment_227, v48, hs]
  have hc1054 : ClauseSat (assignment c) [97,454,451] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_225, assignment_227, v227, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_225, assignment_227, v48, hs]
  have hc1055 : ClauseSat (assignment c) [73,457,452] := by
    cases ha0 : v36 c <;> cases ha1 : v226 c <;> cases ha2 : v227 c <;> simp [ClauseSat, litVal, assignment_36, assignment_226, assignment_228, v228, ha0, ha1, ha2]
  have hc1056 : ClauseSat (assignment c) [73,457,454] := by
    cases ha0 : v36 c <;> cases ha1 : v226 c <;> cases ha2 : v227 c <;> simp [ClauseSat, litVal, assignment_36, assignment_227, assignment_228, v228, ha0, ha1, ha2]
  have hc1057 : ClauseSat (assignment c) [73,456,453,455] := by
    cases ha0 : v36 c <;> cases ha1 : v226 c <;> cases ha2 : v227 c <;> simp [ClauseSat, litVal, assignment_36, assignment_226, assignment_227, assignment_228, v228, ha0, ha1, ha2]
  have hc1058 : ClauseSat (assignment c) [72,456,453] := by
    cases ha0 : v36 c <;> cases ha1 : v226 c <;> cases ha2 : v227 c <;> simp [ClauseSat, litVal, assignment_36, assignment_226, assignment_228, v228, ha0, ha1, ha2]
  have hc1059 : ClauseSat (assignment c) [72,456,455] := by
    cases ha0 : v36 c <;> cases ha1 : v226 c <;> cases ha2 : v227 c <;> simp [ClauseSat, litVal, assignment_36, assignment_227, assignment_228, v228, ha0, ha1, ha2]
  have hc1060 : ClauseSat (assignment c) [72,457,452,454] := by
    cases ha0 : v36 c <;> cases ha1 : v226 c <;> cases ha2 : v227 c <;> simp [ClauseSat, litVal, assignment_36, assignment_226, assignment_227, assignment_228, v228, ha0, ha1, ha2]
  have hc1061 : ClauseSat (assignment c) [121,458] := by
    by_cases hs : c.a3.val = 0
    · simp [ClauseSat, litVal, assignment_60, assignment_229, v229, v60, hs]
    · simp [ClauseSat, litVal, assignment_60, assignment_229, v60, hs]
  have hc1062 : ClauseSat (assignment c) [123,458] := by
    by_cases hs : c.a3.val = 1
    · simp [ClauseSat, litVal, assignment_61, assignment_229, v229, v61, hs]
    · simp [ClauseSat, litVal, assignment_61, assignment_229, v61, hs]
  have hc1063 : ClauseSat (assignment c) [125,458] := by
    by_cases hs : c.a3.val = 2
    · simp [ClauseSat, litVal, assignment_62, assignment_229, v229, v62, hs]
    · simp [ClauseSat, litVal, assignment_62, assignment_229, v62, hs]
  have hc1064 : ClauseSat (assignment c) [127,459] := by
    by_cases hs : c.a3.val = 3
    · simp [ClauseSat, litVal, assignment_63, assignment_229, v229, v63, hs]
    · simp [ClauseSat, litVal, assignment_63, assignment_229, v63, hs]
  have hc1065 : ClauseSat (assignment c) [129,459,444] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_222, assignment_229, v229, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_222, assignment_229, v64, hs]
  have hc1066 : ClauseSat (assignment c) [129,458,445] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_222, assignment_229, v229, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_222, assignment_229, v64, hs]
  have hc1067 : ClauseSat (assignment c) [131,459,450] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_225, assignment_229, v229, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_225, assignment_229, v65, hs]
  have hc1068 : ClauseSat (assignment c) [131,458,451] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_225, assignment_229, v229, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_225, assignment_229, v65, hs]
  have hc1069 : ClauseSat (assignment c) [133,459,456] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_228, assignment_229, v229, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_228, assignment_229, v66, hs]
  have hc1070 : ClauseSat (assignment c) [133,458,457] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_228, assignment_229, v229, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_228, assignment_229, v66, hs]
  have hc1071 : ClauseSat (assignment c) [135,460] := by
    by_cases hs : c.b3.val = 0
    · simp [ClauseSat, litVal, assignment_67, assignment_230, v230, v67, hs]
    · simp [ClauseSat, litVal, assignment_67, assignment_230, v67, hs]
  have hc1072 : ClauseSat (assignment c) [137,460] := by
    by_cases hs : c.b3.val = 1
    · simp [ClauseSat, litVal, assignment_68, assignment_230, v230, v68, hs]
    · simp [ClauseSat, litVal, assignment_68, assignment_230, v68, hs]
  have hc1073 : ClauseSat (assignment c) [139,460] := by
    by_cases hs : c.b3.val = 2
    · simp [ClauseSat, litVal, assignment_69, assignment_230, v230, v69, hs]
    · simp [ClauseSat, litVal, assignment_69, assignment_230, v69, hs]
  have hc1074 : ClauseSat (assignment c) [141,461] := by
    by_cases hs : c.b3.val = 3
    · simp [ClauseSat, litVal, assignment_70, assignment_230, v230, v70, hs]
    · simp [ClauseSat, litVal, assignment_70, assignment_230, v70, hs]
  have hc1075 : ClauseSat (assignment c) [143,461,444] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_222, assignment_230, v230, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_222, assignment_230, v71, hs]
  have hc1076 : ClauseSat (assignment c) [143,460,445] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_222, assignment_230, v230, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_222, assignment_230, v71, hs]
  have hc1077 : ClauseSat (assignment c) [145,461,450] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_225, assignment_230, v230, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_225, assignment_230, v72, hs]
  have hc1078 : ClauseSat (assignment c) [145,460,451] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_225, assignment_230, v230, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_225, assignment_230, v72, hs]
  have hc1079 : ClauseSat (assignment c) [147,461,456] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_228, assignment_230, v230, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_228, assignment_230, v73, hs]
  have hc1080 : ClauseSat (assignment c) [147,460,457] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_228, assignment_230, v230, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_228, assignment_230, v73, hs]
  have hc1081 : ClauseSat (assignment c) [119,463,458] := by
    cases ha0 : v59 c <;> cases ha1 : v229 c <;> cases ha2 : v230 c <;> simp [ClauseSat, litVal, assignment_59, assignment_229, assignment_231, v231, ha0, ha1, ha2]
  have hc1082 : ClauseSat (assignment c) [119,463,460] := by
    cases ha0 : v59 c <;> cases ha1 : v229 c <;> cases ha2 : v230 c <;> simp [ClauseSat, litVal, assignment_59, assignment_230, assignment_231, v231, ha0, ha1, ha2]
  have hc1083 : ClauseSat (assignment c) [119,462,459,461] := by
    cases ha0 : v59 c <;> cases ha1 : v229 c <;> cases ha2 : v230 c <;> simp [ClauseSat, litVal, assignment_59, assignment_229, assignment_230, assignment_231, v231, ha0, ha1, ha2]
  have hc1084 : ClauseSat (assignment c) [118,462,459] := by
    cases ha0 : v59 c <;> cases ha1 : v229 c <;> cases ha2 : v230 c <;> simp [ClauseSat, litVal, assignment_59, assignment_229, assignment_231, v231, ha0, ha1, ha2]
  have hc1085 : ClauseSat (assignment c) [118,462,461] := by
    cases ha0 : v59 c <;> cases ha1 : v229 c <;> cases ha2 : v230 c <;> simp [ClauseSat, litVal, assignment_59, assignment_230, assignment_231, v231, ha0, ha1, ha2]
  have hc1086 : ClauseSat (assignment c) [118,463,458,460] := by
    cases ha0 : v59 c <;> cases ha1 : v229 c <;> cases ha2 : v230 c <;> simp [ClauseSat, litVal, assignment_59, assignment_229, assignment_230, assignment_231, v231, ha0, ha1, ha2]
  have hc1087 : ClauseSat (assignment c) [175,464] := by
    by_cases hs : c.a4.val = 0
    · simp [ClauseSat, litVal, assignment_87, assignment_232, v232, v87, hs]
    · simp [ClauseSat, litVal, assignment_87, assignment_232, v87, hs]
  have hc1088 : ClauseSat (assignment c) [177,464] := by
    by_cases hs : c.a4.val = 1
    · simp [ClauseSat, litVal, assignment_88, assignment_232, v232, v88, hs]
    · simp [ClauseSat, litVal, assignment_88, assignment_232, v88, hs]
  have hc1089 : ClauseSat (assignment c) [179,464] := by
    by_cases hs : c.a4.val = 2
    · simp [ClauseSat, litVal, assignment_89, assignment_232, v232, v89, hs]
    · simp [ClauseSat, litVal, assignment_89, assignment_232, v89, hs]
  have hc1090 : ClauseSat (assignment c) [181,465] := by
    by_cases hs : c.a4.val = 3
    · simp [ClauseSat, litVal, assignment_90, assignment_232, v232, v90, hs]
    · simp [ClauseSat, litVal, assignment_90, assignment_232, v90, hs]
  have hc1091 : ClauseSat (assignment c) [183,465,444] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_222, assignment_232, v232, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_222, assignment_232, v91, hs]
  have hc1092 : ClauseSat (assignment c) [183,464,445] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_222, assignment_232, v232, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_222, assignment_232, v91, hs]
  have hc1093 : ClauseSat (assignment c) [185,465,450] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_225, assignment_232, v232, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_225, assignment_232, v92, hs]
  have hc1094 : ClauseSat (assignment c) [185,464,451] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_225, assignment_232, v232, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_225, assignment_232, v92, hs]
  have hc1095 : ClauseSat (assignment c) [187,465,456] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_228, assignment_232, v232, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_228, assignment_232, v93, hs]
  have hc1096 : ClauseSat (assignment c) [187,464,457] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_228, assignment_232, v232, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_228, assignment_232, v93, hs]
  have hc1097 : ClauseSat (assignment c) [189,465,462] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_231, assignment_232, v232, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_231, assignment_232, v94, hs]
  have hc1098 : ClauseSat (assignment c) [189,464,463] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_231, assignment_232, v232, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_231, assignment_232, v94, hs]
  have hc1099 : ClauseSat (assignment c) [191,466] := by
    by_cases hs : c.b4.val = 0
    · simp [ClauseSat, litVal, assignment_95, assignment_233, v233, v95, hs]
    · simp [ClauseSat, litVal, assignment_95, assignment_233, v95, hs]
  simp only [chunk10, List.forall_mem_cons]
  exact ⟨hc1000, hc1001, hc1002, hc1003, hc1004, hc1005, hc1006, hc1007, hc1008, hc1009, hc1010, hc1011, hc1012, hc1013, hc1014, hc1015, hc1016, hc1017, hc1018, hc1019, hc1020, hc1021, hc1022, hc1023, hc1024, hc1025, hc1026, hc1027, hc1028, hc1029, hc1030, hc1031, hc1032, hc1033, hc1034, hc1035, hc1036, hc1037, hc1038, hc1039, hc1040, hc1041, hc1042, hc1043, hc1044, hc1045, hc1046, hc1047, hc1048, hc1049, hc1050, hc1051, hc1052, hc1053, hc1054, hc1055, hc1056, hc1057, hc1058, hc1059, hc1060, hc1061, hc1062, hc1063, hc1064, hc1065, hc1066, hc1067, hc1068, hc1069, hc1070, hc1071, hc1072, hc1073, hc1074, hc1075, hc1076, hc1077, hc1078, hc1079, hc1080, hc1081, hc1082, hc1083, hc1084, hc1085, hc1086, hc1087, hc1088, hc1089, hc1090, hc1091, hc1092, hc1093, hc1094, hc1095, hc1096, hc1097, hc1098, hc1099, by simp⟩
#check satChunk10

def chunk11 : List (List Nat) := [[193, 466], [195, 466], [197, 467], [199, 467, 444], [199, 466, 445], [201, 467, 450], [201, 466, 451], [203, 467, 456], [203, 466, 457], [205, 467, 462], [205, 466, 463], [173, 469, 464], [173, 469, 466], [173, 468, 465, 467], [172, 468, 465], [172, 468, 467], [172, 469, 464, 466], [468], [7, 471], [9, 471], [11, 471], [13, 470], [15, 473], [17, 473], [19, 473], [21, 472], [5, 475, 470], [5, 475, 472], [5, 474, 471, 473], [4, 474, 471], [4, 474, 473], [4, 475, 470, 472], [37, 477], [39, 477], [41, 477], [43, 476], [45, 477, 474], [45, 476, 475], [47, 479], [49, 479], [51, 479], [53, 478], [55, 479, 474], [55, 478, 475], [35, 481, 476], [35, 481, 478], [35, 480, 477, 479], [34, 480, 477], [34, 480, 479], [34, 481, 476, 478], [75, 483], [77, 483], [79, 483], [81, 482], [83, 483, 474], [83, 482, 475], [85, 483, 480], [85, 482, 481], [87, 485], [89, 485], [91, 485], [93, 484], [95, 485, 474], [95, 484, 475], [97, 485, 480], [97, 484, 481], [73, 487, 482], [73, 487, 484], [73, 486, 483, 485], [72, 486, 483], [72, 486, 485], [72, 487, 482, 484], [121, 489], [123, 489], [125, 489], [127, 488], [129, 489, 474], [129, 488, 475], [131, 489, 480], [131, 488, 481], [133, 489, 486], [133, 488, 487], [135, 491], [137, 491], [139, 491], [141, 490], [143, 491, 474], [143, 490, 475], [145, 491, 480], [145, 490, 481], [147, 491, 486], [147, 490, 487], [119, 493, 488], [119, 493, 490], [119, 492, 489, 491], [118, 492, 489], [118, 492, 491], [118, 493, 488, 490], [175, 495], [177, 495]]
theorem satChunk11 (c : Candidate) (hv : valid c)
    (hr : ∀ r : Fin 16, output c r = target r)
    (hl : derivativeLeft c = false) (hd : derivativeRight c = false) :
    ∀ cl ∈ chunk11, ClauseSat (assignment c) cl := by
  rcases hv with ⟨h0, h1, h2, h3, h4⟩
  have hc1100 : ClauseSat (assignment c) [193,466] := by
    by_cases hs : c.b4.val = 1
    · simp [ClauseSat, litVal, assignment_96, assignment_233, v233, v96, hs]
    · simp [ClauseSat, litVal, assignment_96, assignment_233, v96, hs]
  have hc1101 : ClauseSat (assignment c) [195,466] := by
    by_cases hs : c.b4.val = 2
    · simp [ClauseSat, litVal, assignment_97, assignment_233, v233, v97, hs]
    · simp [ClauseSat, litVal, assignment_97, assignment_233, v97, hs]
  have hc1102 : ClauseSat (assignment c) [197,467] := by
    by_cases hs : c.b4.val = 3
    · simp [ClauseSat, litVal, assignment_98, assignment_233, v233, v98, hs]
    · simp [ClauseSat, litVal, assignment_98, assignment_233, v98, hs]
  have hc1103 : ClauseSat (assignment c) [199,467,444] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_222, assignment_233, v233, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_222, assignment_233, v99, hs]
  have hc1104 : ClauseSat (assignment c) [199,466,445] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_222, assignment_233, v233, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_222, assignment_233, v99, hs]
  have hc1105 : ClauseSat (assignment c) [201,467,450] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_225, assignment_233, v233, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_225, assignment_233, v100, hs]
  have hc1106 : ClauseSat (assignment c) [201,466,451] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_225, assignment_233, v233, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_225, assignment_233, v100, hs]
  have hc1107 : ClauseSat (assignment c) [203,467,456] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_228, assignment_233, v233, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_228, assignment_233, v101, hs]
  have hc1108 : ClauseSat (assignment c) [203,466,457] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_228, assignment_233, v233, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_228, assignment_233, v101, hs]
  have hc1109 : ClauseSat (assignment c) [205,467,462] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_231, assignment_233, v233, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_231, assignment_233, v102, hs]
  have hc1110 : ClauseSat (assignment c) [205,466,463] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_231, assignment_233, v233, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_231, assignment_233, v102, hs]
  have hc1111 : ClauseSat (assignment c) [173,469,464] := by
    cases ha0 : v86 c <;> cases ha1 : v232 c <;> cases ha2 : v233 c <;> simp [ClauseSat, litVal, assignment_86, assignment_232, assignment_234, v234, ha0, ha1, ha2]
  have hc1112 : ClauseSat (assignment c) [173,469,466] := by
    cases ha0 : v86 c <;> cases ha1 : v232 c <;> cases ha2 : v233 c <;> simp [ClauseSat, litVal, assignment_86, assignment_233, assignment_234, v234, ha0, ha1, ha2]
  have hc1113 : ClauseSat (assignment c) [173,468,465,467] := by
    cases ha0 : v86 c <;> cases ha1 : v232 c <;> cases ha2 : v233 c <;> simp [ClauseSat, litVal, assignment_86, assignment_232, assignment_233, assignment_234, v234, ha0, ha1, ha2]
  have hc1114 : ClauseSat (assignment c) [172,468,465] := by
    cases ha0 : v86 c <;> cases ha1 : v232 c <;> cases ha2 : v233 c <;> simp [ClauseSat, litVal, assignment_86, assignment_232, assignment_234, v234, ha0, ha1, ha2]
  have hc1115 : ClauseSat (assignment c) [172,468,467] := by
    cases ha0 : v86 c <;> cases ha1 : v232 c <;> cases ha2 : v233 c <;> simp [ClauseSat, litVal, assignment_86, assignment_233, assignment_234, v234, ha0, ha1, ha2]
  have hc1116 : ClauseSat (assignment c) [172,469,464,466] := by
    cases ha0 : v86 c <;> cases ha1 : v232 c <;> cases ha2 : v233 c <;> simp [ClauseSat, litVal, assignment_86, assignment_232, assignment_233, assignment_234, v234, ha0, ha1, ha2]
  have hc1117 : ClauseSat (assignment c) [468] := by
    have hh := hr ⟨7, by decide⟩
    have ht : target ⟨7, by decide⟩ = true := by decide
    rw [ht] at hh
    simpa [ClauseSat, litVal, assignment_234, output] using hh
  have hc1118 : ClauseSat (assignment c) [7,471] := by
    by_cases hs : c.a0.val = 0
    · simp [ClauseSat, litVal, assignment_3, assignment_235, v235, v3, hs]
    · simp [ClauseSat, litVal, assignment_3, assignment_235, v3, hs]
  have hc1119 : ClauseSat (assignment c) [9,471] := by
    by_cases hs : c.a0.val = 1
    · simp [ClauseSat, litVal, assignment_4, assignment_235, v235, v4, hs]
    · simp [ClauseSat, litVal, assignment_4, assignment_235, v4, hs]
  have hc1120 : ClauseSat (assignment c) [11,471] := by
    by_cases hs : c.a0.val = 2
    · simp [ClauseSat, litVal, assignment_5, assignment_235, v235, v5, hs]
    · simp [ClauseSat, litVal, assignment_5, assignment_235, v5, hs]
  have hc1121 : ClauseSat (assignment c) [13,470] := by
    by_cases hs : c.a0.val = 3
    · simp [ClauseSat, litVal, assignment_6, assignment_235, v235, v6, hs]
    · simp [ClauseSat, litVal, assignment_6, assignment_235, v6, hs]
  have hc1122 : ClauseSat (assignment c) [15,473] := by
    by_cases hs : c.b0.val = 0
    · simp [ClauseSat, litVal, assignment_7, assignment_236, v236, v7, hs]
    · simp [ClauseSat, litVal, assignment_7, assignment_236, v7, hs]
  have hc1123 : ClauseSat (assignment c) [17,473] := by
    by_cases hs : c.b0.val = 1
    · simp [ClauseSat, litVal, assignment_8, assignment_236, v236, v8, hs]
    · simp [ClauseSat, litVal, assignment_8, assignment_236, v8, hs]
  have hc1124 : ClauseSat (assignment c) [19,473] := by
    by_cases hs : c.b0.val = 2
    · simp [ClauseSat, litVal, assignment_9, assignment_236, v236, v9, hs]
    · simp [ClauseSat, litVal, assignment_9, assignment_236, v9, hs]
  have hc1125 : ClauseSat (assignment c) [21,472] := by
    by_cases hs : c.b0.val = 3
    · simp [ClauseSat, litVal, assignment_10, assignment_236, v236, v10, hs]
    · simp [ClauseSat, litVal, assignment_10, assignment_236, v10, hs]
  have hc1126 : ClauseSat (assignment c) [5,475,470] := by
    cases ha0 : v2 c <;> cases ha1 : v235 c <;> cases ha2 : v236 c <;> simp [ClauseSat, litVal, assignment_2, assignment_235, assignment_237, v237, ha0, ha1, ha2]
  have hc1127 : ClauseSat (assignment c) [5,475,472] := by
    cases ha0 : v2 c <;> cases ha1 : v235 c <;> cases ha2 : v236 c <;> simp [ClauseSat, litVal, assignment_2, assignment_236, assignment_237, v237, ha0, ha1, ha2]
  have hc1128 : ClauseSat (assignment c) [5,474,471,473] := by
    cases ha0 : v2 c <;> cases ha1 : v235 c <;> cases ha2 : v236 c <;> simp [ClauseSat, litVal, assignment_2, assignment_235, assignment_236, assignment_237, v237, ha0, ha1, ha2]
  have hc1129 : ClauseSat (assignment c) [4,474,471] := by
    cases ha0 : v2 c <;> cases ha1 : v235 c <;> cases ha2 : v236 c <;> simp [ClauseSat, litVal, assignment_2, assignment_235, assignment_237, v237, ha0, ha1, ha2]
  have hc1130 : ClauseSat (assignment c) [4,474,473] := by
    cases ha0 : v2 c <;> cases ha1 : v235 c <;> cases ha2 : v236 c <;> simp [ClauseSat, litVal, assignment_2, assignment_236, assignment_237, v237, ha0, ha1, ha2]
  have hc1131 : ClauseSat (assignment c) [4,475,470,472] := by
    cases ha0 : v2 c <;> cases ha1 : v235 c <;> cases ha2 : v236 c <;> simp [ClauseSat, litVal, assignment_2, assignment_235, assignment_236, assignment_237, v237, ha0, ha1, ha2]
  have hc1132 : ClauseSat (assignment c) [37,477] := by
    by_cases hs : c.a1.val = 0
    · simp [ClauseSat, litVal, assignment_18, assignment_238, v238, v18, hs]
    · simp [ClauseSat, litVal, assignment_18, assignment_238, v18, hs]
  have hc1133 : ClauseSat (assignment c) [39,477] := by
    by_cases hs : c.a1.val = 1
    · simp [ClauseSat, litVal, assignment_19, assignment_238, v238, v19, hs]
    · simp [ClauseSat, litVal, assignment_19, assignment_238, v19, hs]
  have hc1134 : ClauseSat (assignment c) [41,477] := by
    by_cases hs : c.a1.val = 2
    · simp [ClauseSat, litVal, assignment_20, assignment_238, v238, v20, hs]
    · simp [ClauseSat, litVal, assignment_20, assignment_238, v20, hs]
  have hc1135 : ClauseSat (assignment c) [43,476] := by
    by_cases hs : c.a1.val = 3
    · simp [ClauseSat, litVal, assignment_21, assignment_238, v238, v21, hs]
    · simp [ClauseSat, litVal, assignment_21, assignment_238, v21, hs]
  have hc1136 : ClauseSat (assignment c) [45,477,474] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_237, assignment_238, v238, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_237, assignment_238, v22, hs]
  have hc1137 : ClauseSat (assignment c) [45,476,475] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_237, assignment_238, v238, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_237, assignment_238, v22, hs]
  have hc1138 : ClauseSat (assignment c) [47,479] := by
    by_cases hs : c.b1.val = 0
    · simp [ClauseSat, litVal, assignment_23, assignment_239, v239, v23, hs]
    · simp [ClauseSat, litVal, assignment_23, assignment_239, v23, hs]
  have hc1139 : ClauseSat (assignment c) [49,479] := by
    by_cases hs : c.b1.val = 1
    · simp [ClauseSat, litVal, assignment_24, assignment_239, v239, v24, hs]
    · simp [ClauseSat, litVal, assignment_24, assignment_239, v24, hs]
  have hc1140 : ClauseSat (assignment c) [51,479] := by
    by_cases hs : c.b1.val = 2
    · simp [ClauseSat, litVal, assignment_25, assignment_239, v239, v25, hs]
    · simp [ClauseSat, litVal, assignment_25, assignment_239, v25, hs]
  have hc1141 : ClauseSat (assignment c) [53,478] := by
    by_cases hs : c.b1.val = 3
    · simp [ClauseSat, litVal, assignment_26, assignment_239, v239, v26, hs]
    · simp [ClauseSat, litVal, assignment_26, assignment_239, v26, hs]
  have hc1142 : ClauseSat (assignment c) [55,479,474] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_237, assignment_239, v239, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_237, assignment_239, v27, hs]
  have hc1143 : ClauseSat (assignment c) [55,478,475] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_237, assignment_239, v239, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_237, assignment_239, v27, hs]
  have hc1144 : ClauseSat (assignment c) [35,481,476] := by
    cases ha0 : v17 c <;> cases ha1 : v238 c <;> cases ha2 : v239 c <;> simp [ClauseSat, litVal, assignment_17, assignment_238, assignment_240, v240, ha0, ha1, ha2]
  have hc1145 : ClauseSat (assignment c) [35,481,478] := by
    cases ha0 : v17 c <;> cases ha1 : v238 c <;> cases ha2 : v239 c <;> simp [ClauseSat, litVal, assignment_17, assignment_239, assignment_240, v240, ha0, ha1, ha2]
  have hc1146 : ClauseSat (assignment c) [35,480,477,479] := by
    cases ha0 : v17 c <;> cases ha1 : v238 c <;> cases ha2 : v239 c <;> simp [ClauseSat, litVal, assignment_17, assignment_238, assignment_239, assignment_240, v240, ha0, ha1, ha2]
  have hc1147 : ClauseSat (assignment c) [34,480,477] := by
    cases ha0 : v17 c <;> cases ha1 : v238 c <;> cases ha2 : v239 c <;> simp [ClauseSat, litVal, assignment_17, assignment_238, assignment_240, v240, ha0, ha1, ha2]
  have hc1148 : ClauseSat (assignment c) [34,480,479] := by
    cases ha0 : v17 c <;> cases ha1 : v238 c <;> cases ha2 : v239 c <;> simp [ClauseSat, litVal, assignment_17, assignment_239, assignment_240, v240, ha0, ha1, ha2]
  have hc1149 : ClauseSat (assignment c) [34,481,476,478] := by
    cases ha0 : v17 c <;> cases ha1 : v238 c <;> cases ha2 : v239 c <;> simp [ClauseSat, litVal, assignment_17, assignment_238, assignment_239, assignment_240, v240, ha0, ha1, ha2]
  have hc1150 : ClauseSat (assignment c) [75,483] := by
    by_cases hs : c.a2.val = 0
    · simp [ClauseSat, litVal, assignment_37, assignment_241, v241, v37, hs]
    · simp [ClauseSat, litVal, assignment_37, assignment_241, v37, hs]
  have hc1151 : ClauseSat (assignment c) [77,483] := by
    by_cases hs : c.a2.val = 1
    · simp [ClauseSat, litVal, assignment_38, assignment_241, v241, v38, hs]
    · simp [ClauseSat, litVal, assignment_38, assignment_241, v38, hs]
  have hc1152 : ClauseSat (assignment c) [79,483] := by
    by_cases hs : c.a2.val = 2
    · simp [ClauseSat, litVal, assignment_39, assignment_241, v241, v39, hs]
    · simp [ClauseSat, litVal, assignment_39, assignment_241, v39, hs]
  have hc1153 : ClauseSat (assignment c) [81,482] := by
    by_cases hs : c.a2.val = 3
    · simp [ClauseSat, litVal, assignment_40, assignment_241, v241, v40, hs]
    · simp [ClauseSat, litVal, assignment_40, assignment_241, v40, hs]
  have hc1154 : ClauseSat (assignment c) [83,483,474] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_237, assignment_241, v241, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_237, assignment_241, v41, hs]
  have hc1155 : ClauseSat (assignment c) [83,482,475] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_237, assignment_241, v241, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_237, assignment_241, v41, hs]
  have hc1156 : ClauseSat (assignment c) [85,483,480] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_240, assignment_241, v241, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_240, assignment_241, v42, hs]
  have hc1157 : ClauseSat (assignment c) [85,482,481] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_240, assignment_241, v241, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_240, assignment_241, v42, hs]
  have hc1158 : ClauseSat (assignment c) [87,485] := by
    by_cases hs : c.b2.val = 0
    · simp [ClauseSat, litVal, assignment_43, assignment_242, v242, v43, hs]
    · simp [ClauseSat, litVal, assignment_43, assignment_242, v43, hs]
  have hc1159 : ClauseSat (assignment c) [89,485] := by
    by_cases hs : c.b2.val = 1
    · simp [ClauseSat, litVal, assignment_44, assignment_242, v242, v44, hs]
    · simp [ClauseSat, litVal, assignment_44, assignment_242, v44, hs]
  have hc1160 : ClauseSat (assignment c) [91,485] := by
    by_cases hs : c.b2.val = 2
    · simp [ClauseSat, litVal, assignment_45, assignment_242, v242, v45, hs]
    · simp [ClauseSat, litVal, assignment_45, assignment_242, v45, hs]
  have hc1161 : ClauseSat (assignment c) [93,484] := by
    by_cases hs : c.b2.val = 3
    · simp [ClauseSat, litVal, assignment_46, assignment_242, v242, v46, hs]
    · simp [ClauseSat, litVal, assignment_46, assignment_242, v46, hs]
  have hc1162 : ClauseSat (assignment c) [95,485,474] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_237, assignment_242, v242, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_237, assignment_242, v47, hs]
  have hc1163 : ClauseSat (assignment c) [95,484,475] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_237, assignment_242, v242, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_237, assignment_242, v47, hs]
  have hc1164 : ClauseSat (assignment c) [97,485,480] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_240, assignment_242, v242, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_240, assignment_242, v48, hs]
  have hc1165 : ClauseSat (assignment c) [97,484,481] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_240, assignment_242, v242, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_240, assignment_242, v48, hs]
  have hc1166 : ClauseSat (assignment c) [73,487,482] := by
    cases ha0 : v36 c <;> cases ha1 : v241 c <;> cases ha2 : v242 c <;> simp [ClauseSat, litVal, assignment_36, assignment_241, assignment_243, v243, ha0, ha1, ha2]
  have hc1167 : ClauseSat (assignment c) [73,487,484] := by
    cases ha0 : v36 c <;> cases ha1 : v241 c <;> cases ha2 : v242 c <;> simp [ClauseSat, litVal, assignment_36, assignment_242, assignment_243, v243, ha0, ha1, ha2]
  have hc1168 : ClauseSat (assignment c) [73,486,483,485] := by
    cases ha0 : v36 c <;> cases ha1 : v241 c <;> cases ha2 : v242 c <;> simp [ClauseSat, litVal, assignment_36, assignment_241, assignment_242, assignment_243, v243, ha0, ha1, ha2]
  have hc1169 : ClauseSat (assignment c) [72,486,483] := by
    cases ha0 : v36 c <;> cases ha1 : v241 c <;> cases ha2 : v242 c <;> simp [ClauseSat, litVal, assignment_36, assignment_241, assignment_243, v243, ha0, ha1, ha2]
  have hc1170 : ClauseSat (assignment c) [72,486,485] := by
    cases ha0 : v36 c <;> cases ha1 : v241 c <;> cases ha2 : v242 c <;> simp [ClauseSat, litVal, assignment_36, assignment_242, assignment_243, v243, ha0, ha1, ha2]
  have hc1171 : ClauseSat (assignment c) [72,487,482,484] := by
    cases ha0 : v36 c <;> cases ha1 : v241 c <;> cases ha2 : v242 c <;> simp [ClauseSat, litVal, assignment_36, assignment_241, assignment_242, assignment_243, v243, ha0, ha1, ha2]
  have hc1172 : ClauseSat (assignment c) [121,489] := by
    by_cases hs : c.a3.val = 0
    · simp [ClauseSat, litVal, assignment_60, assignment_244, v244, v60, hs]
    · simp [ClauseSat, litVal, assignment_60, assignment_244, v60, hs]
  have hc1173 : ClauseSat (assignment c) [123,489] := by
    by_cases hs : c.a3.val = 1
    · simp [ClauseSat, litVal, assignment_61, assignment_244, v244, v61, hs]
    · simp [ClauseSat, litVal, assignment_61, assignment_244, v61, hs]
  have hc1174 : ClauseSat (assignment c) [125,489] := by
    by_cases hs : c.a3.val = 2
    · simp [ClauseSat, litVal, assignment_62, assignment_244, v244, v62, hs]
    · simp [ClauseSat, litVal, assignment_62, assignment_244, v62, hs]
  have hc1175 : ClauseSat (assignment c) [127,488] := by
    by_cases hs : c.a3.val = 3
    · simp [ClauseSat, litVal, assignment_63, assignment_244, v244, v63, hs]
    · simp [ClauseSat, litVal, assignment_63, assignment_244, v63, hs]
  have hc1176 : ClauseSat (assignment c) [129,489,474] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_237, assignment_244, v244, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_237, assignment_244, v64, hs]
  have hc1177 : ClauseSat (assignment c) [129,488,475] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_237, assignment_244, v244, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_237, assignment_244, v64, hs]
  have hc1178 : ClauseSat (assignment c) [131,489,480] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_240, assignment_244, v244, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_240, assignment_244, v65, hs]
  have hc1179 : ClauseSat (assignment c) [131,488,481] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_240, assignment_244, v244, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_240, assignment_244, v65, hs]
  have hc1180 : ClauseSat (assignment c) [133,489,486] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_243, assignment_244, v244, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_243, assignment_244, v66, hs]
  have hc1181 : ClauseSat (assignment c) [133,488,487] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_243, assignment_244, v244, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_243, assignment_244, v66, hs]
  have hc1182 : ClauseSat (assignment c) [135,491] := by
    by_cases hs : c.b3.val = 0
    · simp [ClauseSat, litVal, assignment_67, assignment_245, v245, v67, hs]
    · simp [ClauseSat, litVal, assignment_67, assignment_245, v67, hs]
  have hc1183 : ClauseSat (assignment c) [137,491] := by
    by_cases hs : c.b3.val = 1
    · simp [ClauseSat, litVal, assignment_68, assignment_245, v245, v68, hs]
    · simp [ClauseSat, litVal, assignment_68, assignment_245, v68, hs]
  have hc1184 : ClauseSat (assignment c) [139,491] := by
    by_cases hs : c.b3.val = 2
    · simp [ClauseSat, litVal, assignment_69, assignment_245, v245, v69, hs]
    · simp [ClauseSat, litVal, assignment_69, assignment_245, v69, hs]
  have hc1185 : ClauseSat (assignment c) [141,490] := by
    by_cases hs : c.b3.val = 3
    · simp [ClauseSat, litVal, assignment_70, assignment_245, v245, v70, hs]
    · simp [ClauseSat, litVal, assignment_70, assignment_245, v70, hs]
  have hc1186 : ClauseSat (assignment c) [143,491,474] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_237, assignment_245, v245, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_237, assignment_245, v71, hs]
  have hc1187 : ClauseSat (assignment c) [143,490,475] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_237, assignment_245, v245, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_237, assignment_245, v71, hs]
  have hc1188 : ClauseSat (assignment c) [145,491,480] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_240, assignment_245, v245, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_240, assignment_245, v72, hs]
  have hc1189 : ClauseSat (assignment c) [145,490,481] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_240, assignment_245, v245, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_240, assignment_245, v72, hs]
  have hc1190 : ClauseSat (assignment c) [147,491,486] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_243, assignment_245, v245, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_243, assignment_245, v73, hs]
  have hc1191 : ClauseSat (assignment c) [147,490,487] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_243, assignment_245, v245, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_243, assignment_245, v73, hs]
  have hc1192 : ClauseSat (assignment c) [119,493,488] := by
    cases ha0 : v59 c <;> cases ha1 : v244 c <;> cases ha2 : v245 c <;> simp [ClauseSat, litVal, assignment_59, assignment_244, assignment_246, v246, ha0, ha1, ha2]
  have hc1193 : ClauseSat (assignment c) [119,493,490] := by
    cases ha0 : v59 c <;> cases ha1 : v244 c <;> cases ha2 : v245 c <;> simp [ClauseSat, litVal, assignment_59, assignment_245, assignment_246, v246, ha0, ha1, ha2]
  have hc1194 : ClauseSat (assignment c) [119,492,489,491] := by
    cases ha0 : v59 c <;> cases ha1 : v244 c <;> cases ha2 : v245 c <;> simp [ClauseSat, litVal, assignment_59, assignment_244, assignment_245, assignment_246, v246, ha0, ha1, ha2]
  have hc1195 : ClauseSat (assignment c) [118,492,489] := by
    cases ha0 : v59 c <;> cases ha1 : v244 c <;> cases ha2 : v245 c <;> simp [ClauseSat, litVal, assignment_59, assignment_244, assignment_246, v246, ha0, ha1, ha2]
  have hc1196 : ClauseSat (assignment c) [118,492,491] := by
    cases ha0 : v59 c <;> cases ha1 : v244 c <;> cases ha2 : v245 c <;> simp [ClauseSat, litVal, assignment_59, assignment_245, assignment_246, v246, ha0, ha1, ha2]
  have hc1197 : ClauseSat (assignment c) [118,493,488,490] := by
    cases ha0 : v59 c <;> cases ha1 : v244 c <;> cases ha2 : v245 c <;> simp [ClauseSat, litVal, assignment_59, assignment_244, assignment_245, assignment_246, v246, ha0, ha1, ha2]
  have hc1198 : ClauseSat (assignment c) [175,495] := by
    by_cases hs : c.a4.val = 0
    · simp [ClauseSat, litVal, assignment_87, assignment_247, v247, v87, hs]
    · simp [ClauseSat, litVal, assignment_87, assignment_247, v87, hs]
  have hc1199 : ClauseSat (assignment c) [177,495] := by
    by_cases hs : c.a4.val = 1
    · simp [ClauseSat, litVal, assignment_88, assignment_247, v247, v88, hs]
    · simp [ClauseSat, litVal, assignment_88, assignment_247, v88, hs]
  simp only [chunk11, List.forall_mem_cons]
  exact ⟨hc1100, hc1101, hc1102, hc1103, hc1104, hc1105, hc1106, hc1107, hc1108, hc1109, hc1110, hc1111, hc1112, hc1113, hc1114, hc1115, hc1116, hc1117, hc1118, hc1119, hc1120, hc1121, hc1122, hc1123, hc1124, hc1125, hc1126, hc1127, hc1128, hc1129, hc1130, hc1131, hc1132, hc1133, hc1134, hc1135, hc1136, hc1137, hc1138, hc1139, hc1140, hc1141, hc1142, hc1143, hc1144, hc1145, hc1146, hc1147, hc1148, hc1149, hc1150, hc1151, hc1152, hc1153, hc1154, hc1155, hc1156, hc1157, hc1158, hc1159, hc1160, hc1161, hc1162, hc1163, hc1164, hc1165, hc1166, hc1167, hc1168, hc1169, hc1170, hc1171, hc1172, hc1173, hc1174, hc1175, hc1176, hc1177, hc1178, hc1179, hc1180, hc1181, hc1182, hc1183, hc1184, hc1185, hc1186, hc1187, hc1188, hc1189, hc1190, hc1191, hc1192, hc1193, hc1194, hc1195, hc1196, hc1197, hc1198, hc1199, by simp⟩
#check satChunk11

def chunk12 : List (List Nat) := [[179, 495], [181, 494], [183, 495, 474], [183, 494, 475], [185, 495, 480], [185, 494, 481], [187, 495, 486], [187, 494, 487], [189, 495, 492], [189, 494, 493], [191, 497], [193, 497], [195, 497], [197, 496], [199, 497, 474], [199, 496, 475], [201, 497, 480], [201, 496, 481], [203, 497, 486], [203, 496, 487], [205, 497, 492], [205, 496, 493], [173, 499, 494], [173, 499, 496], [173, 498, 495, 497], [172, 498, 495], [172, 498, 497], [172, 499, 494, 496], [499], [7, 500], [9, 501], [11, 501], [13, 500], [15, 502], [17, 503], [19, 503], [21, 502], [5, 505, 500], [5, 505, 502], [5, 504, 501, 503], [4, 504, 501], [4, 504, 503], [4, 505, 500, 502], [37, 506], [39, 507], [41, 507], [43, 506], [45, 507, 504], [45, 506, 505], [47, 508], [49, 509], [51, 509], [53, 508], [55, 509, 504], [55, 508, 505], [35, 511, 506], [35, 511, 508], [35, 510, 507, 509], [34, 510, 507], [34, 510, 509], [34, 511, 506, 508], [75, 512], [77, 513], [79, 513], [81, 512], [83, 513, 504], [83, 512, 505], [85, 513, 510], [85, 512, 511], [87, 514], [89, 515], [91, 515], [93, 514], [95, 515, 504], [95, 514, 505], [97, 515, 510], [97, 514, 511], [73, 517, 512], [73, 517, 514], [73, 516, 513, 515], [72, 516, 513], [72, 516, 515], [72, 517, 512, 514], [121, 518], [123, 519], [125, 519], [127, 518], [129, 519, 504], [129, 518, 505], [131, 519, 510], [131, 518, 511], [133, 519, 516], [133, 518, 517], [135, 520], [137, 521], [139, 521], [141, 520], [143, 521, 504], [143, 520, 505], [145, 521, 510]]
theorem satChunk12 (c : Candidate) (hv : valid c)
    (hr : ∀ r : Fin 16, output c r = target r)
    (hl : derivativeLeft c = false) (hd : derivativeRight c = false) :
    ∀ cl ∈ chunk12, ClauseSat (assignment c) cl := by
  rcases hv with ⟨h0, h1, h2, h3, h4⟩
  have hc1200 : ClauseSat (assignment c) [179,495] := by
    by_cases hs : c.a4.val = 2
    · simp [ClauseSat, litVal, assignment_89, assignment_247, v247, v89, hs]
    · simp [ClauseSat, litVal, assignment_89, assignment_247, v89, hs]
  have hc1201 : ClauseSat (assignment c) [181,494] := by
    by_cases hs : c.a4.val = 3
    · simp [ClauseSat, litVal, assignment_90, assignment_247, v247, v90, hs]
    · simp [ClauseSat, litVal, assignment_90, assignment_247, v90, hs]
  have hc1202 : ClauseSat (assignment c) [183,495,474] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_237, assignment_247, v247, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_237, assignment_247, v91, hs]
  have hc1203 : ClauseSat (assignment c) [183,494,475] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_237, assignment_247, v247, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_237, assignment_247, v91, hs]
  have hc1204 : ClauseSat (assignment c) [185,495,480] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_240, assignment_247, v247, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_240, assignment_247, v92, hs]
  have hc1205 : ClauseSat (assignment c) [185,494,481] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_240, assignment_247, v247, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_240, assignment_247, v92, hs]
  have hc1206 : ClauseSat (assignment c) [187,495,486] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_243, assignment_247, v247, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_243, assignment_247, v93, hs]
  have hc1207 : ClauseSat (assignment c) [187,494,487] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_243, assignment_247, v247, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_243, assignment_247, v93, hs]
  have hc1208 : ClauseSat (assignment c) [189,495,492] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_246, assignment_247, v247, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_246, assignment_247, v94, hs]
  have hc1209 : ClauseSat (assignment c) [189,494,493] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_246, assignment_247, v247, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_246, assignment_247, v94, hs]
  have hc1210 : ClauseSat (assignment c) [191,497] := by
    by_cases hs : c.b4.val = 0
    · simp [ClauseSat, litVal, assignment_95, assignment_248, v248, v95, hs]
    · simp [ClauseSat, litVal, assignment_95, assignment_248, v95, hs]
  have hc1211 : ClauseSat (assignment c) [193,497] := by
    by_cases hs : c.b4.val = 1
    · simp [ClauseSat, litVal, assignment_96, assignment_248, v248, v96, hs]
    · simp [ClauseSat, litVal, assignment_96, assignment_248, v96, hs]
  have hc1212 : ClauseSat (assignment c) [195,497] := by
    by_cases hs : c.b4.val = 2
    · simp [ClauseSat, litVal, assignment_97, assignment_248, v248, v97, hs]
    · simp [ClauseSat, litVal, assignment_97, assignment_248, v97, hs]
  have hc1213 : ClauseSat (assignment c) [197,496] := by
    by_cases hs : c.b4.val = 3
    · simp [ClauseSat, litVal, assignment_98, assignment_248, v248, v98, hs]
    · simp [ClauseSat, litVal, assignment_98, assignment_248, v98, hs]
  have hc1214 : ClauseSat (assignment c) [199,497,474] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_237, assignment_248, v248, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_237, assignment_248, v99, hs]
  have hc1215 : ClauseSat (assignment c) [199,496,475] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_237, assignment_248, v248, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_237, assignment_248, v99, hs]
  have hc1216 : ClauseSat (assignment c) [201,497,480] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_240, assignment_248, v248, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_240, assignment_248, v100, hs]
  have hc1217 : ClauseSat (assignment c) [201,496,481] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_240, assignment_248, v248, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_240, assignment_248, v100, hs]
  have hc1218 : ClauseSat (assignment c) [203,497,486] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_243, assignment_248, v248, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_243, assignment_248, v101, hs]
  have hc1219 : ClauseSat (assignment c) [203,496,487] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_243, assignment_248, v248, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_243, assignment_248, v101, hs]
  have hc1220 : ClauseSat (assignment c) [205,497,492] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_246, assignment_248, v248, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_246, assignment_248, v102, hs]
  have hc1221 : ClauseSat (assignment c) [205,496,493] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_246, assignment_248, v248, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_246, assignment_248, v102, hs]
  have hc1222 : ClauseSat (assignment c) [173,499,494] := by
    cases ha0 : v86 c <;> cases ha1 : v247 c <;> cases ha2 : v248 c <;> simp [ClauseSat, litVal, assignment_86, assignment_247, assignment_249, v249, ha0, ha1, ha2]
  have hc1223 : ClauseSat (assignment c) [173,499,496] := by
    cases ha0 : v86 c <;> cases ha1 : v247 c <;> cases ha2 : v248 c <;> simp [ClauseSat, litVal, assignment_86, assignment_248, assignment_249, v249, ha0, ha1, ha2]
  have hc1224 : ClauseSat (assignment c) [173,498,495,497] := by
    cases ha0 : v86 c <;> cases ha1 : v247 c <;> cases ha2 : v248 c <;> simp [ClauseSat, litVal, assignment_86, assignment_247, assignment_248, assignment_249, v249, ha0, ha1, ha2]
  have hc1225 : ClauseSat (assignment c) [172,498,495] := by
    cases ha0 : v86 c <;> cases ha1 : v247 c <;> cases ha2 : v248 c <;> simp [ClauseSat, litVal, assignment_86, assignment_247, assignment_249, v249, ha0, ha1, ha2]
  have hc1226 : ClauseSat (assignment c) [172,498,497] := by
    cases ha0 : v86 c <;> cases ha1 : v247 c <;> cases ha2 : v248 c <;> simp [ClauseSat, litVal, assignment_86, assignment_248, assignment_249, v249, ha0, ha1, ha2]
  have hc1227 : ClauseSat (assignment c) [172,499,494,496] := by
    cases ha0 : v86 c <;> cases ha1 : v247 c <;> cases ha2 : v248 c <;> simp [ClauseSat, litVal, assignment_86, assignment_247, assignment_248, assignment_249, v249, ha0, ha1, ha2]
  have hc1228 : ClauseSat (assignment c) [499] := by
    have hh := hr ⟨8, by decide⟩
    have ht : target ⟨8, by decide⟩ = false := by decide
    rw [ht] at hh
    simpa [ClauseSat, litVal, assignment_249, output] using hh
  have hc1229 : ClauseSat (assignment c) [7,500] := by
    by_cases hs : c.a0.val = 0
    · simp [ClauseSat, litVal, assignment_3, assignment_250, v250, v3, hs]
    · simp [ClauseSat, litVal, assignment_3, assignment_250, v3, hs]
  have hc1230 : ClauseSat (assignment c) [9,501] := by
    by_cases hs : c.a0.val = 1
    · simp [ClauseSat, litVal, assignment_4, assignment_250, v250, v4, hs]
    · simp [ClauseSat, litVal, assignment_4, assignment_250, v4, hs]
  have hc1231 : ClauseSat (assignment c) [11,501] := by
    by_cases hs : c.a0.val = 2
    · simp [ClauseSat, litVal, assignment_5, assignment_250, v250, v5, hs]
    · simp [ClauseSat, litVal, assignment_5, assignment_250, v5, hs]
  have hc1232 : ClauseSat (assignment c) [13,500] := by
    by_cases hs : c.a0.val = 3
    · simp [ClauseSat, litVal, assignment_6, assignment_250, v250, v6, hs]
    · simp [ClauseSat, litVal, assignment_6, assignment_250, v6, hs]
  have hc1233 : ClauseSat (assignment c) [15,502] := by
    by_cases hs : c.b0.val = 0
    · simp [ClauseSat, litVal, assignment_7, assignment_251, v251, v7, hs]
    · simp [ClauseSat, litVal, assignment_7, assignment_251, v7, hs]
  have hc1234 : ClauseSat (assignment c) [17,503] := by
    by_cases hs : c.b0.val = 1
    · simp [ClauseSat, litVal, assignment_8, assignment_251, v251, v8, hs]
    · simp [ClauseSat, litVal, assignment_8, assignment_251, v8, hs]
  have hc1235 : ClauseSat (assignment c) [19,503] := by
    by_cases hs : c.b0.val = 2
    · simp [ClauseSat, litVal, assignment_9, assignment_251, v251, v9, hs]
    · simp [ClauseSat, litVal, assignment_9, assignment_251, v9, hs]
  have hc1236 : ClauseSat (assignment c) [21,502] := by
    by_cases hs : c.b0.val = 3
    · simp [ClauseSat, litVal, assignment_10, assignment_251, v251, v10, hs]
    · simp [ClauseSat, litVal, assignment_10, assignment_251, v10, hs]
  have hc1237 : ClauseSat (assignment c) [5,505,500] := by
    cases ha0 : v2 c <;> cases ha1 : v250 c <;> cases ha2 : v251 c <;> simp [ClauseSat, litVal, assignment_2, assignment_250, assignment_252, v252, ha0, ha1, ha2]
  have hc1238 : ClauseSat (assignment c) [5,505,502] := by
    cases ha0 : v2 c <;> cases ha1 : v250 c <;> cases ha2 : v251 c <;> simp [ClauseSat, litVal, assignment_2, assignment_251, assignment_252, v252, ha0, ha1, ha2]
  have hc1239 : ClauseSat (assignment c) [5,504,501,503] := by
    cases ha0 : v2 c <;> cases ha1 : v250 c <;> cases ha2 : v251 c <;> simp [ClauseSat, litVal, assignment_2, assignment_250, assignment_251, assignment_252, v252, ha0, ha1, ha2]
  have hc1240 : ClauseSat (assignment c) [4,504,501] := by
    cases ha0 : v2 c <;> cases ha1 : v250 c <;> cases ha2 : v251 c <;> simp [ClauseSat, litVal, assignment_2, assignment_250, assignment_252, v252, ha0, ha1, ha2]
  have hc1241 : ClauseSat (assignment c) [4,504,503] := by
    cases ha0 : v2 c <;> cases ha1 : v250 c <;> cases ha2 : v251 c <;> simp [ClauseSat, litVal, assignment_2, assignment_251, assignment_252, v252, ha0, ha1, ha2]
  have hc1242 : ClauseSat (assignment c) [4,505,500,502] := by
    cases ha0 : v2 c <;> cases ha1 : v250 c <;> cases ha2 : v251 c <;> simp [ClauseSat, litVal, assignment_2, assignment_250, assignment_251, assignment_252, v252, ha0, ha1, ha2]
  have hc1243 : ClauseSat (assignment c) [37,506] := by
    by_cases hs : c.a1.val = 0
    · simp [ClauseSat, litVal, assignment_18, assignment_253, v253, v18, hs]
    · simp [ClauseSat, litVal, assignment_18, assignment_253, v18, hs]
  have hc1244 : ClauseSat (assignment c) [39,507] := by
    by_cases hs : c.a1.val = 1
    · simp [ClauseSat, litVal, assignment_19, assignment_253, v253, v19, hs]
    · simp [ClauseSat, litVal, assignment_19, assignment_253, v19, hs]
  have hc1245 : ClauseSat (assignment c) [41,507] := by
    by_cases hs : c.a1.val = 2
    · simp [ClauseSat, litVal, assignment_20, assignment_253, v253, v20, hs]
    · simp [ClauseSat, litVal, assignment_20, assignment_253, v20, hs]
  have hc1246 : ClauseSat (assignment c) [43,506] := by
    by_cases hs : c.a1.val = 3
    · simp [ClauseSat, litVal, assignment_21, assignment_253, v253, v21, hs]
    · simp [ClauseSat, litVal, assignment_21, assignment_253, v21, hs]
  have hc1247 : ClauseSat (assignment c) [45,507,504] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_252, assignment_253, v253, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_252, assignment_253, v22, hs]
  have hc1248 : ClauseSat (assignment c) [45,506,505] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_252, assignment_253, v253, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_252, assignment_253, v22, hs]
  have hc1249 : ClauseSat (assignment c) [47,508] := by
    by_cases hs : c.b1.val = 0
    · simp [ClauseSat, litVal, assignment_23, assignment_254, v254, v23, hs]
    · simp [ClauseSat, litVal, assignment_23, assignment_254, v23, hs]
  have hc1250 : ClauseSat (assignment c) [49,509] := by
    by_cases hs : c.b1.val = 1
    · simp [ClauseSat, litVal, assignment_24, assignment_254, v254, v24, hs]
    · simp [ClauseSat, litVal, assignment_24, assignment_254, v24, hs]
  have hc1251 : ClauseSat (assignment c) [51,509] := by
    by_cases hs : c.b1.val = 2
    · simp [ClauseSat, litVal, assignment_25, assignment_254, v254, v25, hs]
    · simp [ClauseSat, litVal, assignment_25, assignment_254, v25, hs]
  have hc1252 : ClauseSat (assignment c) [53,508] := by
    by_cases hs : c.b1.val = 3
    · simp [ClauseSat, litVal, assignment_26, assignment_254, v254, v26, hs]
    · simp [ClauseSat, litVal, assignment_26, assignment_254, v26, hs]
  have hc1253 : ClauseSat (assignment c) [55,509,504] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_252, assignment_254, v254, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_252, assignment_254, v27, hs]
  have hc1254 : ClauseSat (assignment c) [55,508,505] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_252, assignment_254, v254, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_252, assignment_254, v27, hs]
  have hc1255 : ClauseSat (assignment c) [35,511,506] := by
    cases ha0 : v17 c <;> cases ha1 : v253 c <;> cases ha2 : v254 c <;> simp [ClauseSat, litVal, assignment_17, assignment_253, assignment_255, v255, ha0, ha1, ha2]
  have hc1256 : ClauseSat (assignment c) [35,511,508] := by
    cases ha0 : v17 c <;> cases ha1 : v253 c <;> cases ha2 : v254 c <;> simp [ClauseSat, litVal, assignment_17, assignment_254, assignment_255, v255, ha0, ha1, ha2]
  have hc1257 : ClauseSat (assignment c) [35,510,507,509] := by
    cases ha0 : v17 c <;> cases ha1 : v253 c <;> cases ha2 : v254 c <;> simp [ClauseSat, litVal, assignment_17, assignment_253, assignment_254, assignment_255, v255, ha0, ha1, ha2]
  have hc1258 : ClauseSat (assignment c) [34,510,507] := by
    cases ha0 : v17 c <;> cases ha1 : v253 c <;> cases ha2 : v254 c <;> simp [ClauseSat, litVal, assignment_17, assignment_253, assignment_255, v255, ha0, ha1, ha2]
  have hc1259 : ClauseSat (assignment c) [34,510,509] := by
    cases ha0 : v17 c <;> cases ha1 : v253 c <;> cases ha2 : v254 c <;> simp [ClauseSat, litVal, assignment_17, assignment_254, assignment_255, v255, ha0, ha1, ha2]
  have hc1260 : ClauseSat (assignment c) [34,511,506,508] := by
    cases ha0 : v17 c <;> cases ha1 : v253 c <;> cases ha2 : v254 c <;> simp [ClauseSat, litVal, assignment_17, assignment_253, assignment_254, assignment_255, v255, ha0, ha1, ha2]
  have hc1261 : ClauseSat (assignment c) [75,512] := by
    by_cases hs : c.a2.val = 0
    · simp [ClauseSat, litVal, assignment_37, assignment_256, v256, v37, hs]
    · simp [ClauseSat, litVal, assignment_37, assignment_256, v37, hs]
  have hc1262 : ClauseSat (assignment c) [77,513] := by
    by_cases hs : c.a2.val = 1
    · simp [ClauseSat, litVal, assignment_38, assignment_256, v256, v38, hs]
    · simp [ClauseSat, litVal, assignment_38, assignment_256, v38, hs]
  have hc1263 : ClauseSat (assignment c) [79,513] := by
    by_cases hs : c.a2.val = 2
    · simp [ClauseSat, litVal, assignment_39, assignment_256, v256, v39, hs]
    · simp [ClauseSat, litVal, assignment_39, assignment_256, v39, hs]
  have hc1264 : ClauseSat (assignment c) [81,512] := by
    by_cases hs : c.a2.val = 3
    · simp [ClauseSat, litVal, assignment_40, assignment_256, v256, v40, hs]
    · simp [ClauseSat, litVal, assignment_40, assignment_256, v40, hs]
  have hc1265 : ClauseSat (assignment c) [83,513,504] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_252, assignment_256, v256, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_252, assignment_256, v41, hs]
  have hc1266 : ClauseSat (assignment c) [83,512,505] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_252, assignment_256, v256, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_252, assignment_256, v41, hs]
  have hc1267 : ClauseSat (assignment c) [85,513,510] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_255, assignment_256, v256, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_255, assignment_256, v42, hs]
  have hc1268 : ClauseSat (assignment c) [85,512,511] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_255, assignment_256, v256, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_255, assignment_256, v42, hs]
  have hc1269 : ClauseSat (assignment c) [87,514] := by
    by_cases hs : c.b2.val = 0
    · simp [ClauseSat, litVal, assignment_43, assignment_257, v257, v43, hs]
    · simp [ClauseSat, litVal, assignment_43, assignment_257, v43, hs]
  have hc1270 : ClauseSat (assignment c) [89,515] := by
    by_cases hs : c.b2.val = 1
    · simp [ClauseSat, litVal, assignment_44, assignment_257, v257, v44, hs]
    · simp [ClauseSat, litVal, assignment_44, assignment_257, v44, hs]
  have hc1271 : ClauseSat (assignment c) [91,515] := by
    by_cases hs : c.b2.val = 2
    · simp [ClauseSat, litVal, assignment_45, assignment_257, v257, v45, hs]
    · simp [ClauseSat, litVal, assignment_45, assignment_257, v45, hs]
  have hc1272 : ClauseSat (assignment c) [93,514] := by
    by_cases hs : c.b2.val = 3
    · simp [ClauseSat, litVal, assignment_46, assignment_257, v257, v46, hs]
    · simp [ClauseSat, litVal, assignment_46, assignment_257, v46, hs]
  have hc1273 : ClauseSat (assignment c) [95,515,504] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_252, assignment_257, v257, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_252, assignment_257, v47, hs]
  have hc1274 : ClauseSat (assignment c) [95,514,505] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_252, assignment_257, v257, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_252, assignment_257, v47, hs]
  have hc1275 : ClauseSat (assignment c) [97,515,510] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_255, assignment_257, v257, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_255, assignment_257, v48, hs]
  have hc1276 : ClauseSat (assignment c) [97,514,511] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_255, assignment_257, v257, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_255, assignment_257, v48, hs]
  have hc1277 : ClauseSat (assignment c) [73,517,512] := by
    cases ha0 : v36 c <;> cases ha1 : v256 c <;> cases ha2 : v257 c <;> simp [ClauseSat, litVal, assignment_36, assignment_256, assignment_258, v258, ha0, ha1, ha2]
  have hc1278 : ClauseSat (assignment c) [73,517,514] := by
    cases ha0 : v36 c <;> cases ha1 : v256 c <;> cases ha2 : v257 c <;> simp [ClauseSat, litVal, assignment_36, assignment_257, assignment_258, v258, ha0, ha1, ha2]
  have hc1279 : ClauseSat (assignment c) [73,516,513,515] := by
    cases ha0 : v36 c <;> cases ha1 : v256 c <;> cases ha2 : v257 c <;> simp [ClauseSat, litVal, assignment_36, assignment_256, assignment_257, assignment_258, v258, ha0, ha1, ha2]
  have hc1280 : ClauseSat (assignment c) [72,516,513] := by
    cases ha0 : v36 c <;> cases ha1 : v256 c <;> cases ha2 : v257 c <;> simp [ClauseSat, litVal, assignment_36, assignment_256, assignment_258, v258, ha0, ha1, ha2]
  have hc1281 : ClauseSat (assignment c) [72,516,515] := by
    cases ha0 : v36 c <;> cases ha1 : v256 c <;> cases ha2 : v257 c <;> simp [ClauseSat, litVal, assignment_36, assignment_257, assignment_258, v258, ha0, ha1, ha2]
  have hc1282 : ClauseSat (assignment c) [72,517,512,514] := by
    cases ha0 : v36 c <;> cases ha1 : v256 c <;> cases ha2 : v257 c <;> simp [ClauseSat, litVal, assignment_36, assignment_256, assignment_257, assignment_258, v258, ha0, ha1, ha2]
  have hc1283 : ClauseSat (assignment c) [121,518] := by
    by_cases hs : c.a3.val = 0
    · simp [ClauseSat, litVal, assignment_60, assignment_259, v259, v60, hs]
    · simp [ClauseSat, litVal, assignment_60, assignment_259, v60, hs]
  have hc1284 : ClauseSat (assignment c) [123,519] := by
    by_cases hs : c.a3.val = 1
    · simp [ClauseSat, litVal, assignment_61, assignment_259, v259, v61, hs]
    · simp [ClauseSat, litVal, assignment_61, assignment_259, v61, hs]
  have hc1285 : ClauseSat (assignment c) [125,519] := by
    by_cases hs : c.a3.val = 2
    · simp [ClauseSat, litVal, assignment_62, assignment_259, v259, v62, hs]
    · simp [ClauseSat, litVal, assignment_62, assignment_259, v62, hs]
  have hc1286 : ClauseSat (assignment c) [127,518] := by
    by_cases hs : c.a3.val = 3
    · simp [ClauseSat, litVal, assignment_63, assignment_259, v259, v63, hs]
    · simp [ClauseSat, litVal, assignment_63, assignment_259, v63, hs]
  have hc1287 : ClauseSat (assignment c) [129,519,504] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_252, assignment_259, v259, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_252, assignment_259, v64, hs]
  have hc1288 : ClauseSat (assignment c) [129,518,505] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_252, assignment_259, v259, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_252, assignment_259, v64, hs]
  have hc1289 : ClauseSat (assignment c) [131,519,510] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_255, assignment_259, v259, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_255, assignment_259, v65, hs]
  have hc1290 : ClauseSat (assignment c) [131,518,511] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_255, assignment_259, v259, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_255, assignment_259, v65, hs]
  have hc1291 : ClauseSat (assignment c) [133,519,516] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_258, assignment_259, v259, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_258, assignment_259, v66, hs]
  have hc1292 : ClauseSat (assignment c) [133,518,517] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_258, assignment_259, v259, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_258, assignment_259, v66, hs]
  have hc1293 : ClauseSat (assignment c) [135,520] := by
    by_cases hs : c.b3.val = 0
    · simp [ClauseSat, litVal, assignment_67, assignment_260, v260, v67, hs]
    · simp [ClauseSat, litVal, assignment_67, assignment_260, v67, hs]
  have hc1294 : ClauseSat (assignment c) [137,521] := by
    by_cases hs : c.b3.val = 1
    · simp [ClauseSat, litVal, assignment_68, assignment_260, v260, v68, hs]
    · simp [ClauseSat, litVal, assignment_68, assignment_260, v68, hs]
  have hc1295 : ClauseSat (assignment c) [139,521] := by
    by_cases hs : c.b3.val = 2
    · simp [ClauseSat, litVal, assignment_69, assignment_260, v260, v69, hs]
    · simp [ClauseSat, litVal, assignment_69, assignment_260, v69, hs]
  have hc1296 : ClauseSat (assignment c) [141,520] := by
    by_cases hs : c.b3.val = 3
    · simp [ClauseSat, litVal, assignment_70, assignment_260, v260, v70, hs]
    · simp [ClauseSat, litVal, assignment_70, assignment_260, v70, hs]
  have hc1297 : ClauseSat (assignment c) [143,521,504] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_252, assignment_260, v260, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_252, assignment_260, v71, hs]
  have hc1298 : ClauseSat (assignment c) [143,520,505] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_252, assignment_260, v260, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_252, assignment_260, v71, hs]
  have hc1299 : ClauseSat (assignment c) [145,521,510] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_255, assignment_260, v260, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_255, assignment_260, v72, hs]
  simp only [chunk12, List.forall_mem_cons]
  exact ⟨hc1200, hc1201, hc1202, hc1203, hc1204, hc1205, hc1206, hc1207, hc1208, hc1209, hc1210, hc1211, hc1212, hc1213, hc1214, hc1215, hc1216, hc1217, hc1218, hc1219, hc1220, hc1221, hc1222, hc1223, hc1224, hc1225, hc1226, hc1227, hc1228, hc1229, hc1230, hc1231, hc1232, hc1233, hc1234, hc1235, hc1236, hc1237, hc1238, hc1239, hc1240, hc1241, hc1242, hc1243, hc1244, hc1245, hc1246, hc1247, hc1248, hc1249, hc1250, hc1251, hc1252, hc1253, hc1254, hc1255, hc1256, hc1257, hc1258, hc1259, hc1260, hc1261, hc1262, hc1263, hc1264, hc1265, hc1266, hc1267, hc1268, hc1269, hc1270, hc1271, hc1272, hc1273, hc1274, hc1275, hc1276, hc1277, hc1278, hc1279, hc1280, hc1281, hc1282, hc1283, hc1284, hc1285, hc1286, hc1287, hc1288, hc1289, hc1290, hc1291, hc1292, hc1293, hc1294, hc1295, hc1296, hc1297, hc1298, hc1299, by simp⟩
#check satChunk12

def chunk13 : List (List Nat) := [[145, 520, 511], [147, 521, 516], [147, 520, 517], [119, 523, 518], [119, 523, 520], [119, 522, 519, 521], [118, 522, 519], [118, 522, 521], [118, 523, 518, 520], [175, 524], [177, 525], [179, 525], [181, 524], [183, 525, 504], [183, 524, 505], [185, 525, 510], [185, 524, 511], [187, 525, 516], [187, 524, 517], [189, 525, 522], [189, 524, 523], [191, 526], [193, 527], [195, 527], [197, 526], [199, 527, 504], [199, 526, 505], [201, 527, 510], [201, 526, 511], [203, 527, 516], [203, 526, 517], [205, 527, 522], [205, 526, 523], [173, 529, 524], [173, 529, 526], [173, 528, 525, 527], [172, 528, 525], [172, 528, 527], [172, 529, 524, 526], [529], [7, 531], [9, 530], [11, 531], [13, 530], [15, 533], [17, 532], [19, 533], [21, 532], [5, 535, 530], [5, 535, 532], [5, 534, 531, 533], [4, 534, 531], [4, 534, 533], [4, 535, 530, 532], [37, 537], [39, 536], [41, 537], [43, 536], [45, 537, 534], [45, 536, 535], [47, 539], [49, 538], [51, 539], [53, 538], [55, 539, 534], [55, 538, 535], [35, 541, 536], [35, 541, 538], [35, 540, 537, 539], [34, 540, 537], [34, 540, 539], [34, 541, 536, 538], [75, 543], [77, 542], [79, 543], [81, 542], [83, 543, 534], [83, 542, 535], [85, 543, 540], [85, 542, 541], [87, 545], [89, 544], [91, 545], [93, 544], [95, 545, 534], [95, 544, 535], [97, 545, 540], [97, 544, 541], [73, 547, 542], [73, 547, 544], [73, 546, 543, 545], [72, 546, 543], [72, 546, 545], [72, 547, 542, 544], [121, 549], [123, 548], [125, 549], [127, 548], [129, 549, 534], [129, 548, 535]]
theorem satChunk13 (c : Candidate) (hv : valid c)
    (hr : ∀ r : Fin 16, output c r = target r)
    (hl : derivativeLeft c = false) (hd : derivativeRight c = false) :
    ∀ cl ∈ chunk13, ClauseSat (assignment c) cl := by
  rcases hv with ⟨h0, h1, h2, h3, h4⟩
  have hc1300 : ClauseSat (assignment c) [145,520,511] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_255, assignment_260, v260, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_255, assignment_260, v72, hs]
  have hc1301 : ClauseSat (assignment c) [147,521,516] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_258, assignment_260, v260, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_258, assignment_260, v73, hs]
  have hc1302 : ClauseSat (assignment c) [147,520,517] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_258, assignment_260, v260, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_258, assignment_260, v73, hs]
  have hc1303 : ClauseSat (assignment c) [119,523,518] := by
    cases ha0 : v59 c <;> cases ha1 : v259 c <;> cases ha2 : v260 c <;> simp [ClauseSat, litVal, assignment_59, assignment_259, assignment_261, v261, ha0, ha1, ha2]
  have hc1304 : ClauseSat (assignment c) [119,523,520] := by
    cases ha0 : v59 c <;> cases ha1 : v259 c <;> cases ha2 : v260 c <;> simp [ClauseSat, litVal, assignment_59, assignment_260, assignment_261, v261, ha0, ha1, ha2]
  have hc1305 : ClauseSat (assignment c) [119,522,519,521] := by
    cases ha0 : v59 c <;> cases ha1 : v259 c <;> cases ha2 : v260 c <;> simp [ClauseSat, litVal, assignment_59, assignment_259, assignment_260, assignment_261, v261, ha0, ha1, ha2]
  have hc1306 : ClauseSat (assignment c) [118,522,519] := by
    cases ha0 : v59 c <;> cases ha1 : v259 c <;> cases ha2 : v260 c <;> simp [ClauseSat, litVal, assignment_59, assignment_259, assignment_261, v261, ha0, ha1, ha2]
  have hc1307 : ClauseSat (assignment c) [118,522,521] := by
    cases ha0 : v59 c <;> cases ha1 : v259 c <;> cases ha2 : v260 c <;> simp [ClauseSat, litVal, assignment_59, assignment_260, assignment_261, v261, ha0, ha1, ha2]
  have hc1308 : ClauseSat (assignment c) [118,523,518,520] := by
    cases ha0 : v59 c <;> cases ha1 : v259 c <;> cases ha2 : v260 c <;> simp [ClauseSat, litVal, assignment_59, assignment_259, assignment_260, assignment_261, v261, ha0, ha1, ha2]
  have hc1309 : ClauseSat (assignment c) [175,524] := by
    by_cases hs : c.a4.val = 0
    · simp [ClauseSat, litVal, assignment_87, assignment_262, v262, v87, hs]
    · simp [ClauseSat, litVal, assignment_87, assignment_262, v87, hs]
  have hc1310 : ClauseSat (assignment c) [177,525] := by
    by_cases hs : c.a4.val = 1
    · simp [ClauseSat, litVal, assignment_88, assignment_262, v262, v88, hs]
    · simp [ClauseSat, litVal, assignment_88, assignment_262, v88, hs]
  have hc1311 : ClauseSat (assignment c) [179,525] := by
    by_cases hs : c.a4.val = 2
    · simp [ClauseSat, litVal, assignment_89, assignment_262, v262, v89, hs]
    · simp [ClauseSat, litVal, assignment_89, assignment_262, v89, hs]
  have hc1312 : ClauseSat (assignment c) [181,524] := by
    by_cases hs : c.a4.val = 3
    · simp [ClauseSat, litVal, assignment_90, assignment_262, v262, v90, hs]
    · simp [ClauseSat, litVal, assignment_90, assignment_262, v90, hs]
  have hc1313 : ClauseSat (assignment c) [183,525,504] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_252, assignment_262, v262, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_252, assignment_262, v91, hs]
  have hc1314 : ClauseSat (assignment c) [183,524,505] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_252, assignment_262, v262, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_252, assignment_262, v91, hs]
  have hc1315 : ClauseSat (assignment c) [185,525,510] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_255, assignment_262, v262, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_255, assignment_262, v92, hs]
  have hc1316 : ClauseSat (assignment c) [185,524,511] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_255, assignment_262, v262, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_255, assignment_262, v92, hs]
  have hc1317 : ClauseSat (assignment c) [187,525,516] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_258, assignment_262, v262, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_258, assignment_262, v93, hs]
  have hc1318 : ClauseSat (assignment c) [187,524,517] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_258, assignment_262, v262, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_258, assignment_262, v93, hs]
  have hc1319 : ClauseSat (assignment c) [189,525,522] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_261, assignment_262, v262, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_261, assignment_262, v94, hs]
  have hc1320 : ClauseSat (assignment c) [189,524,523] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_261, assignment_262, v262, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_261, assignment_262, v94, hs]
  have hc1321 : ClauseSat (assignment c) [191,526] := by
    by_cases hs : c.b4.val = 0
    · simp [ClauseSat, litVal, assignment_95, assignment_263, v263, v95, hs]
    · simp [ClauseSat, litVal, assignment_95, assignment_263, v95, hs]
  have hc1322 : ClauseSat (assignment c) [193,527] := by
    by_cases hs : c.b4.val = 1
    · simp [ClauseSat, litVal, assignment_96, assignment_263, v263, v96, hs]
    · simp [ClauseSat, litVal, assignment_96, assignment_263, v96, hs]
  have hc1323 : ClauseSat (assignment c) [195,527] := by
    by_cases hs : c.b4.val = 2
    · simp [ClauseSat, litVal, assignment_97, assignment_263, v263, v97, hs]
    · simp [ClauseSat, litVal, assignment_97, assignment_263, v97, hs]
  have hc1324 : ClauseSat (assignment c) [197,526] := by
    by_cases hs : c.b4.val = 3
    · simp [ClauseSat, litVal, assignment_98, assignment_263, v263, v98, hs]
    · simp [ClauseSat, litVal, assignment_98, assignment_263, v98, hs]
  have hc1325 : ClauseSat (assignment c) [199,527,504] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_252, assignment_263, v263, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_252, assignment_263, v99, hs]
  have hc1326 : ClauseSat (assignment c) [199,526,505] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_252, assignment_263, v263, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_252, assignment_263, v99, hs]
  have hc1327 : ClauseSat (assignment c) [201,527,510] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_255, assignment_263, v263, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_255, assignment_263, v100, hs]
  have hc1328 : ClauseSat (assignment c) [201,526,511] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_255, assignment_263, v263, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_255, assignment_263, v100, hs]
  have hc1329 : ClauseSat (assignment c) [203,527,516] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_258, assignment_263, v263, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_258, assignment_263, v101, hs]
  have hc1330 : ClauseSat (assignment c) [203,526,517] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_258, assignment_263, v263, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_258, assignment_263, v101, hs]
  have hc1331 : ClauseSat (assignment c) [205,527,522] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_261, assignment_263, v263, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_261, assignment_263, v102, hs]
  have hc1332 : ClauseSat (assignment c) [205,526,523] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_261, assignment_263, v263, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_261, assignment_263, v102, hs]
  have hc1333 : ClauseSat (assignment c) [173,529,524] := by
    cases ha0 : v86 c <;> cases ha1 : v262 c <;> cases ha2 : v263 c <;> simp [ClauseSat, litVal, assignment_86, assignment_262, assignment_264, v264, ha0, ha1, ha2]
  have hc1334 : ClauseSat (assignment c) [173,529,526] := by
    cases ha0 : v86 c <;> cases ha1 : v262 c <;> cases ha2 : v263 c <;> simp [ClauseSat, litVal, assignment_86, assignment_263, assignment_264, v264, ha0, ha1, ha2]
  have hc1335 : ClauseSat (assignment c) [173,528,525,527] := by
    cases ha0 : v86 c <;> cases ha1 : v262 c <;> cases ha2 : v263 c <;> simp [ClauseSat, litVal, assignment_86, assignment_262, assignment_263, assignment_264, v264, ha0, ha1, ha2]
  have hc1336 : ClauseSat (assignment c) [172,528,525] := by
    cases ha0 : v86 c <;> cases ha1 : v262 c <;> cases ha2 : v263 c <;> simp [ClauseSat, litVal, assignment_86, assignment_262, assignment_264, v264, ha0, ha1, ha2]
  have hc1337 : ClauseSat (assignment c) [172,528,527] := by
    cases ha0 : v86 c <;> cases ha1 : v262 c <;> cases ha2 : v263 c <;> simp [ClauseSat, litVal, assignment_86, assignment_263, assignment_264, v264, ha0, ha1, ha2]
  have hc1338 : ClauseSat (assignment c) [172,529,524,526] := by
    cases ha0 : v86 c <;> cases ha1 : v262 c <;> cases ha2 : v263 c <;> simp [ClauseSat, litVal, assignment_86, assignment_262, assignment_263, assignment_264, v264, ha0, ha1, ha2]
  have hc1339 : ClauseSat (assignment c) [529] := by
    have hh := hr ⟨9, by decide⟩
    have ht : target ⟨9, by decide⟩ = false := by decide
    rw [ht] at hh
    simpa [ClauseSat, litVal, assignment_264, output] using hh
  have hc1340 : ClauseSat (assignment c) [7,531] := by
    by_cases hs : c.a0.val = 0
    · simp [ClauseSat, litVal, assignment_3, assignment_265, v265, v3, hs]
    · simp [ClauseSat, litVal, assignment_3, assignment_265, v3, hs]
  have hc1341 : ClauseSat (assignment c) [9,530] := by
    by_cases hs : c.a0.val = 1
    · simp [ClauseSat, litVal, assignment_4, assignment_265, v265, v4, hs]
    · simp [ClauseSat, litVal, assignment_4, assignment_265, v4, hs]
  have hc1342 : ClauseSat (assignment c) [11,531] := by
    by_cases hs : c.a0.val = 2
    · simp [ClauseSat, litVal, assignment_5, assignment_265, v265, v5, hs]
    · simp [ClauseSat, litVal, assignment_5, assignment_265, v5, hs]
  have hc1343 : ClauseSat (assignment c) [13,530] := by
    by_cases hs : c.a0.val = 3
    · simp [ClauseSat, litVal, assignment_6, assignment_265, v265, v6, hs]
    · simp [ClauseSat, litVal, assignment_6, assignment_265, v6, hs]
  have hc1344 : ClauseSat (assignment c) [15,533] := by
    by_cases hs : c.b0.val = 0
    · simp [ClauseSat, litVal, assignment_7, assignment_266, v266, v7, hs]
    · simp [ClauseSat, litVal, assignment_7, assignment_266, v7, hs]
  have hc1345 : ClauseSat (assignment c) [17,532] := by
    by_cases hs : c.b0.val = 1
    · simp [ClauseSat, litVal, assignment_8, assignment_266, v266, v8, hs]
    · simp [ClauseSat, litVal, assignment_8, assignment_266, v8, hs]
  have hc1346 : ClauseSat (assignment c) [19,533] := by
    by_cases hs : c.b0.val = 2
    · simp [ClauseSat, litVal, assignment_9, assignment_266, v266, v9, hs]
    · simp [ClauseSat, litVal, assignment_9, assignment_266, v9, hs]
  have hc1347 : ClauseSat (assignment c) [21,532] := by
    by_cases hs : c.b0.val = 3
    · simp [ClauseSat, litVal, assignment_10, assignment_266, v266, v10, hs]
    · simp [ClauseSat, litVal, assignment_10, assignment_266, v10, hs]
  have hc1348 : ClauseSat (assignment c) [5,535,530] := by
    cases ha0 : v2 c <;> cases ha1 : v265 c <;> cases ha2 : v266 c <;> simp [ClauseSat, litVal, assignment_2, assignment_265, assignment_267, v267, ha0, ha1, ha2]
  have hc1349 : ClauseSat (assignment c) [5,535,532] := by
    cases ha0 : v2 c <;> cases ha1 : v265 c <;> cases ha2 : v266 c <;> simp [ClauseSat, litVal, assignment_2, assignment_266, assignment_267, v267, ha0, ha1, ha2]
  have hc1350 : ClauseSat (assignment c) [5,534,531,533] := by
    cases ha0 : v2 c <;> cases ha1 : v265 c <;> cases ha2 : v266 c <;> simp [ClauseSat, litVal, assignment_2, assignment_265, assignment_266, assignment_267, v267, ha0, ha1, ha2]
  have hc1351 : ClauseSat (assignment c) [4,534,531] := by
    cases ha0 : v2 c <;> cases ha1 : v265 c <;> cases ha2 : v266 c <;> simp [ClauseSat, litVal, assignment_2, assignment_265, assignment_267, v267, ha0, ha1, ha2]
  have hc1352 : ClauseSat (assignment c) [4,534,533] := by
    cases ha0 : v2 c <;> cases ha1 : v265 c <;> cases ha2 : v266 c <;> simp [ClauseSat, litVal, assignment_2, assignment_266, assignment_267, v267, ha0, ha1, ha2]
  have hc1353 : ClauseSat (assignment c) [4,535,530,532] := by
    cases ha0 : v2 c <;> cases ha1 : v265 c <;> cases ha2 : v266 c <;> simp [ClauseSat, litVal, assignment_2, assignment_265, assignment_266, assignment_267, v267, ha0, ha1, ha2]
  have hc1354 : ClauseSat (assignment c) [37,537] := by
    by_cases hs : c.a1.val = 0
    · simp [ClauseSat, litVal, assignment_18, assignment_268, v268, v18, hs]
    · simp [ClauseSat, litVal, assignment_18, assignment_268, v18, hs]
  have hc1355 : ClauseSat (assignment c) [39,536] := by
    by_cases hs : c.a1.val = 1
    · simp [ClauseSat, litVal, assignment_19, assignment_268, v268, v19, hs]
    · simp [ClauseSat, litVal, assignment_19, assignment_268, v19, hs]
  have hc1356 : ClauseSat (assignment c) [41,537] := by
    by_cases hs : c.a1.val = 2
    · simp [ClauseSat, litVal, assignment_20, assignment_268, v268, v20, hs]
    · simp [ClauseSat, litVal, assignment_20, assignment_268, v20, hs]
  have hc1357 : ClauseSat (assignment c) [43,536] := by
    by_cases hs : c.a1.val = 3
    · simp [ClauseSat, litVal, assignment_21, assignment_268, v268, v21, hs]
    · simp [ClauseSat, litVal, assignment_21, assignment_268, v21, hs]
  have hc1358 : ClauseSat (assignment c) [45,537,534] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_267, assignment_268, v268, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_267, assignment_268, v22, hs]
  have hc1359 : ClauseSat (assignment c) [45,536,535] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_267, assignment_268, v268, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_267, assignment_268, v22, hs]
  have hc1360 : ClauseSat (assignment c) [47,539] := by
    by_cases hs : c.b1.val = 0
    · simp [ClauseSat, litVal, assignment_23, assignment_269, v269, v23, hs]
    · simp [ClauseSat, litVal, assignment_23, assignment_269, v23, hs]
  have hc1361 : ClauseSat (assignment c) [49,538] := by
    by_cases hs : c.b1.val = 1
    · simp [ClauseSat, litVal, assignment_24, assignment_269, v269, v24, hs]
    · simp [ClauseSat, litVal, assignment_24, assignment_269, v24, hs]
  have hc1362 : ClauseSat (assignment c) [51,539] := by
    by_cases hs : c.b1.val = 2
    · simp [ClauseSat, litVal, assignment_25, assignment_269, v269, v25, hs]
    · simp [ClauseSat, litVal, assignment_25, assignment_269, v25, hs]
  have hc1363 : ClauseSat (assignment c) [53,538] := by
    by_cases hs : c.b1.val = 3
    · simp [ClauseSat, litVal, assignment_26, assignment_269, v269, v26, hs]
    · simp [ClauseSat, litVal, assignment_26, assignment_269, v26, hs]
  have hc1364 : ClauseSat (assignment c) [55,539,534] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_267, assignment_269, v269, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_267, assignment_269, v27, hs]
  have hc1365 : ClauseSat (assignment c) [55,538,535] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_267, assignment_269, v269, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_267, assignment_269, v27, hs]
  have hc1366 : ClauseSat (assignment c) [35,541,536] := by
    cases ha0 : v17 c <;> cases ha1 : v268 c <;> cases ha2 : v269 c <;> simp [ClauseSat, litVal, assignment_17, assignment_268, assignment_270, v270, ha0, ha1, ha2]
  have hc1367 : ClauseSat (assignment c) [35,541,538] := by
    cases ha0 : v17 c <;> cases ha1 : v268 c <;> cases ha2 : v269 c <;> simp [ClauseSat, litVal, assignment_17, assignment_269, assignment_270, v270, ha0, ha1, ha2]
  have hc1368 : ClauseSat (assignment c) [35,540,537,539] := by
    cases ha0 : v17 c <;> cases ha1 : v268 c <;> cases ha2 : v269 c <;> simp [ClauseSat, litVal, assignment_17, assignment_268, assignment_269, assignment_270, v270, ha0, ha1, ha2]
  have hc1369 : ClauseSat (assignment c) [34,540,537] := by
    cases ha0 : v17 c <;> cases ha1 : v268 c <;> cases ha2 : v269 c <;> simp [ClauseSat, litVal, assignment_17, assignment_268, assignment_270, v270, ha0, ha1, ha2]
  have hc1370 : ClauseSat (assignment c) [34,540,539] := by
    cases ha0 : v17 c <;> cases ha1 : v268 c <;> cases ha2 : v269 c <;> simp [ClauseSat, litVal, assignment_17, assignment_269, assignment_270, v270, ha0, ha1, ha2]
  have hc1371 : ClauseSat (assignment c) [34,541,536,538] := by
    cases ha0 : v17 c <;> cases ha1 : v268 c <;> cases ha2 : v269 c <;> simp [ClauseSat, litVal, assignment_17, assignment_268, assignment_269, assignment_270, v270, ha0, ha1, ha2]
  have hc1372 : ClauseSat (assignment c) [75,543] := by
    by_cases hs : c.a2.val = 0
    · simp [ClauseSat, litVal, assignment_37, assignment_271, v271, v37, hs]
    · simp [ClauseSat, litVal, assignment_37, assignment_271, v37, hs]
  have hc1373 : ClauseSat (assignment c) [77,542] := by
    by_cases hs : c.a2.val = 1
    · simp [ClauseSat, litVal, assignment_38, assignment_271, v271, v38, hs]
    · simp [ClauseSat, litVal, assignment_38, assignment_271, v38, hs]
  have hc1374 : ClauseSat (assignment c) [79,543] := by
    by_cases hs : c.a2.val = 2
    · simp [ClauseSat, litVal, assignment_39, assignment_271, v271, v39, hs]
    · simp [ClauseSat, litVal, assignment_39, assignment_271, v39, hs]
  have hc1375 : ClauseSat (assignment c) [81,542] := by
    by_cases hs : c.a2.val = 3
    · simp [ClauseSat, litVal, assignment_40, assignment_271, v271, v40, hs]
    · simp [ClauseSat, litVal, assignment_40, assignment_271, v40, hs]
  have hc1376 : ClauseSat (assignment c) [83,543,534] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_267, assignment_271, v271, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_267, assignment_271, v41, hs]
  have hc1377 : ClauseSat (assignment c) [83,542,535] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_267, assignment_271, v271, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_267, assignment_271, v41, hs]
  have hc1378 : ClauseSat (assignment c) [85,543,540] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_270, assignment_271, v271, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_270, assignment_271, v42, hs]
  have hc1379 : ClauseSat (assignment c) [85,542,541] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_270, assignment_271, v271, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_270, assignment_271, v42, hs]
  have hc1380 : ClauseSat (assignment c) [87,545] := by
    by_cases hs : c.b2.val = 0
    · simp [ClauseSat, litVal, assignment_43, assignment_272, v272, v43, hs]
    · simp [ClauseSat, litVal, assignment_43, assignment_272, v43, hs]
  have hc1381 : ClauseSat (assignment c) [89,544] := by
    by_cases hs : c.b2.val = 1
    · simp [ClauseSat, litVal, assignment_44, assignment_272, v272, v44, hs]
    · simp [ClauseSat, litVal, assignment_44, assignment_272, v44, hs]
  have hc1382 : ClauseSat (assignment c) [91,545] := by
    by_cases hs : c.b2.val = 2
    · simp [ClauseSat, litVal, assignment_45, assignment_272, v272, v45, hs]
    · simp [ClauseSat, litVal, assignment_45, assignment_272, v45, hs]
  have hc1383 : ClauseSat (assignment c) [93,544] := by
    by_cases hs : c.b2.val = 3
    · simp [ClauseSat, litVal, assignment_46, assignment_272, v272, v46, hs]
    · simp [ClauseSat, litVal, assignment_46, assignment_272, v46, hs]
  have hc1384 : ClauseSat (assignment c) [95,545,534] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_267, assignment_272, v272, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_267, assignment_272, v47, hs]
  have hc1385 : ClauseSat (assignment c) [95,544,535] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_267, assignment_272, v272, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_267, assignment_272, v47, hs]
  have hc1386 : ClauseSat (assignment c) [97,545,540] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_270, assignment_272, v272, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_270, assignment_272, v48, hs]
  have hc1387 : ClauseSat (assignment c) [97,544,541] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_270, assignment_272, v272, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_270, assignment_272, v48, hs]
  have hc1388 : ClauseSat (assignment c) [73,547,542] := by
    cases ha0 : v36 c <;> cases ha1 : v271 c <;> cases ha2 : v272 c <;> simp [ClauseSat, litVal, assignment_36, assignment_271, assignment_273, v273, ha0, ha1, ha2]
  have hc1389 : ClauseSat (assignment c) [73,547,544] := by
    cases ha0 : v36 c <;> cases ha1 : v271 c <;> cases ha2 : v272 c <;> simp [ClauseSat, litVal, assignment_36, assignment_272, assignment_273, v273, ha0, ha1, ha2]
  have hc1390 : ClauseSat (assignment c) [73,546,543,545] := by
    cases ha0 : v36 c <;> cases ha1 : v271 c <;> cases ha2 : v272 c <;> simp [ClauseSat, litVal, assignment_36, assignment_271, assignment_272, assignment_273, v273, ha0, ha1, ha2]
  have hc1391 : ClauseSat (assignment c) [72,546,543] := by
    cases ha0 : v36 c <;> cases ha1 : v271 c <;> cases ha2 : v272 c <;> simp [ClauseSat, litVal, assignment_36, assignment_271, assignment_273, v273, ha0, ha1, ha2]
  have hc1392 : ClauseSat (assignment c) [72,546,545] := by
    cases ha0 : v36 c <;> cases ha1 : v271 c <;> cases ha2 : v272 c <;> simp [ClauseSat, litVal, assignment_36, assignment_272, assignment_273, v273, ha0, ha1, ha2]
  have hc1393 : ClauseSat (assignment c) [72,547,542,544] := by
    cases ha0 : v36 c <;> cases ha1 : v271 c <;> cases ha2 : v272 c <;> simp [ClauseSat, litVal, assignment_36, assignment_271, assignment_272, assignment_273, v273, ha0, ha1, ha2]
  have hc1394 : ClauseSat (assignment c) [121,549] := by
    by_cases hs : c.a3.val = 0
    · simp [ClauseSat, litVal, assignment_60, assignment_274, v274, v60, hs]
    · simp [ClauseSat, litVal, assignment_60, assignment_274, v60, hs]
  have hc1395 : ClauseSat (assignment c) [123,548] := by
    by_cases hs : c.a3.val = 1
    · simp [ClauseSat, litVal, assignment_61, assignment_274, v274, v61, hs]
    · simp [ClauseSat, litVal, assignment_61, assignment_274, v61, hs]
  have hc1396 : ClauseSat (assignment c) [125,549] := by
    by_cases hs : c.a3.val = 2
    · simp [ClauseSat, litVal, assignment_62, assignment_274, v274, v62, hs]
    · simp [ClauseSat, litVal, assignment_62, assignment_274, v62, hs]
  have hc1397 : ClauseSat (assignment c) [127,548] := by
    by_cases hs : c.a3.val = 3
    · simp [ClauseSat, litVal, assignment_63, assignment_274, v274, v63, hs]
    · simp [ClauseSat, litVal, assignment_63, assignment_274, v63, hs]
  have hc1398 : ClauseSat (assignment c) [129,549,534] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_267, assignment_274, v274, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_267, assignment_274, v64, hs]
  have hc1399 : ClauseSat (assignment c) [129,548,535] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_267, assignment_274, v274, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_267, assignment_274, v64, hs]
  simp only [chunk13, List.forall_mem_cons]
  exact ⟨hc1300, hc1301, hc1302, hc1303, hc1304, hc1305, hc1306, hc1307, hc1308, hc1309, hc1310, hc1311, hc1312, hc1313, hc1314, hc1315, hc1316, hc1317, hc1318, hc1319, hc1320, hc1321, hc1322, hc1323, hc1324, hc1325, hc1326, hc1327, hc1328, hc1329, hc1330, hc1331, hc1332, hc1333, hc1334, hc1335, hc1336, hc1337, hc1338, hc1339, hc1340, hc1341, hc1342, hc1343, hc1344, hc1345, hc1346, hc1347, hc1348, hc1349, hc1350, hc1351, hc1352, hc1353, hc1354, hc1355, hc1356, hc1357, hc1358, hc1359, hc1360, hc1361, hc1362, hc1363, hc1364, hc1365, hc1366, hc1367, hc1368, hc1369, hc1370, hc1371, hc1372, hc1373, hc1374, hc1375, hc1376, hc1377, hc1378, hc1379, hc1380, hc1381, hc1382, hc1383, hc1384, hc1385, hc1386, hc1387, hc1388, hc1389, hc1390, hc1391, hc1392, hc1393, hc1394, hc1395, hc1396, hc1397, hc1398, hc1399, by simp⟩
#check satChunk13

def chunk14 : List (List Nat) := [[131, 549, 540], [131, 548, 541], [133, 549, 546], [133, 548, 547], [135, 551], [137, 550], [139, 551], [141, 550], [143, 551, 534], [143, 550, 535], [145, 551, 540], [145, 550, 541], [147, 551, 546], [147, 550, 547], [119, 553, 548], [119, 553, 550], [119, 552, 549, 551], [118, 552, 549], [118, 552, 551], [118, 553, 548, 550], [175, 555], [177, 554], [179, 555], [181, 554], [183, 555, 534], [183, 554, 535], [185, 555, 540], [185, 554, 541], [187, 555, 546], [187, 554, 547], [189, 555, 552], [189, 554, 553], [191, 557], [193, 556], [195, 557], [197, 556], [199, 557, 534], [199, 556, 535], [201, 557, 540], [201, 556, 541], [203, 557, 546], [203, 556, 547], [205, 557, 552], [205, 556, 553], [173, 559, 554], [173, 559, 556], [173, 558, 555, 557], [172, 558, 555], [172, 558, 557], [172, 559, 554, 556], [558], [7, 560], [9, 560], [11, 561], [13, 560], [15, 562], [17, 562], [19, 563], [21, 562], [5, 565, 560], [5, 565, 562], [5, 564, 561, 563], [4, 564, 561], [4, 564, 563], [4, 565, 560, 562], [37, 566], [39, 566], [41, 567], [43, 566], [45, 567, 564], [45, 566, 565], [47, 568], [49, 568], [51, 569], [53, 568], [55, 569, 564], [55, 568, 565], [35, 571, 566], [35, 571, 568], [35, 570, 567, 569], [34, 570, 567], [34, 570, 569], [34, 571, 566, 568], [75, 572], [77, 572], [79, 573], [81, 572], [83, 573, 564], [83, 572, 565], [85, 573, 570], [85, 572, 571], [87, 574], [89, 574], [91, 575], [93, 574], [95, 575, 564], [95, 574, 565], [97, 575, 570], [97, 574, 571], [73, 577, 572]]
theorem satChunk14 (c : Candidate) (hv : valid c)
    (hr : ∀ r : Fin 16, output c r = target r)
    (hl : derivativeLeft c = false) (hd : derivativeRight c = false) :
    ∀ cl ∈ chunk14, ClauseSat (assignment c) cl := by
  rcases hv with ⟨h0, h1, h2, h3, h4⟩
  have hc1400 : ClauseSat (assignment c) [131,549,540] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_270, assignment_274, v274, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_270, assignment_274, v65, hs]
  have hc1401 : ClauseSat (assignment c) [131,548,541] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_270, assignment_274, v274, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_270, assignment_274, v65, hs]
  have hc1402 : ClauseSat (assignment c) [133,549,546] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_273, assignment_274, v274, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_273, assignment_274, v66, hs]
  have hc1403 : ClauseSat (assignment c) [133,548,547] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_273, assignment_274, v274, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_273, assignment_274, v66, hs]
  have hc1404 : ClauseSat (assignment c) [135,551] := by
    by_cases hs : c.b3.val = 0
    · simp [ClauseSat, litVal, assignment_67, assignment_275, v275, v67, hs]
    · simp [ClauseSat, litVal, assignment_67, assignment_275, v67, hs]
  have hc1405 : ClauseSat (assignment c) [137,550] := by
    by_cases hs : c.b3.val = 1
    · simp [ClauseSat, litVal, assignment_68, assignment_275, v275, v68, hs]
    · simp [ClauseSat, litVal, assignment_68, assignment_275, v68, hs]
  have hc1406 : ClauseSat (assignment c) [139,551] := by
    by_cases hs : c.b3.val = 2
    · simp [ClauseSat, litVal, assignment_69, assignment_275, v275, v69, hs]
    · simp [ClauseSat, litVal, assignment_69, assignment_275, v69, hs]
  have hc1407 : ClauseSat (assignment c) [141,550] := by
    by_cases hs : c.b3.val = 3
    · simp [ClauseSat, litVal, assignment_70, assignment_275, v275, v70, hs]
    · simp [ClauseSat, litVal, assignment_70, assignment_275, v70, hs]
  have hc1408 : ClauseSat (assignment c) [143,551,534] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_267, assignment_275, v275, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_267, assignment_275, v71, hs]
  have hc1409 : ClauseSat (assignment c) [143,550,535] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_267, assignment_275, v275, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_267, assignment_275, v71, hs]
  have hc1410 : ClauseSat (assignment c) [145,551,540] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_270, assignment_275, v275, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_270, assignment_275, v72, hs]
  have hc1411 : ClauseSat (assignment c) [145,550,541] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_270, assignment_275, v275, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_270, assignment_275, v72, hs]
  have hc1412 : ClauseSat (assignment c) [147,551,546] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_273, assignment_275, v275, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_273, assignment_275, v73, hs]
  have hc1413 : ClauseSat (assignment c) [147,550,547] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_273, assignment_275, v275, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_273, assignment_275, v73, hs]
  have hc1414 : ClauseSat (assignment c) [119,553,548] := by
    cases ha0 : v59 c <;> cases ha1 : v274 c <;> cases ha2 : v275 c <;> simp [ClauseSat, litVal, assignment_59, assignment_274, assignment_276, v276, ha0, ha1, ha2]
  have hc1415 : ClauseSat (assignment c) [119,553,550] := by
    cases ha0 : v59 c <;> cases ha1 : v274 c <;> cases ha2 : v275 c <;> simp [ClauseSat, litVal, assignment_59, assignment_275, assignment_276, v276, ha0, ha1, ha2]
  have hc1416 : ClauseSat (assignment c) [119,552,549,551] := by
    cases ha0 : v59 c <;> cases ha1 : v274 c <;> cases ha2 : v275 c <;> simp [ClauseSat, litVal, assignment_59, assignment_274, assignment_275, assignment_276, v276, ha0, ha1, ha2]
  have hc1417 : ClauseSat (assignment c) [118,552,549] := by
    cases ha0 : v59 c <;> cases ha1 : v274 c <;> cases ha2 : v275 c <;> simp [ClauseSat, litVal, assignment_59, assignment_274, assignment_276, v276, ha0, ha1, ha2]
  have hc1418 : ClauseSat (assignment c) [118,552,551] := by
    cases ha0 : v59 c <;> cases ha1 : v274 c <;> cases ha2 : v275 c <;> simp [ClauseSat, litVal, assignment_59, assignment_275, assignment_276, v276, ha0, ha1, ha2]
  have hc1419 : ClauseSat (assignment c) [118,553,548,550] := by
    cases ha0 : v59 c <;> cases ha1 : v274 c <;> cases ha2 : v275 c <;> simp [ClauseSat, litVal, assignment_59, assignment_274, assignment_275, assignment_276, v276, ha0, ha1, ha2]
  have hc1420 : ClauseSat (assignment c) [175,555] := by
    by_cases hs : c.a4.val = 0
    · simp [ClauseSat, litVal, assignment_87, assignment_277, v277, v87, hs]
    · simp [ClauseSat, litVal, assignment_87, assignment_277, v87, hs]
  have hc1421 : ClauseSat (assignment c) [177,554] := by
    by_cases hs : c.a4.val = 1
    · simp [ClauseSat, litVal, assignment_88, assignment_277, v277, v88, hs]
    · simp [ClauseSat, litVal, assignment_88, assignment_277, v88, hs]
  have hc1422 : ClauseSat (assignment c) [179,555] := by
    by_cases hs : c.a4.val = 2
    · simp [ClauseSat, litVal, assignment_89, assignment_277, v277, v89, hs]
    · simp [ClauseSat, litVal, assignment_89, assignment_277, v89, hs]
  have hc1423 : ClauseSat (assignment c) [181,554] := by
    by_cases hs : c.a4.val = 3
    · simp [ClauseSat, litVal, assignment_90, assignment_277, v277, v90, hs]
    · simp [ClauseSat, litVal, assignment_90, assignment_277, v90, hs]
  have hc1424 : ClauseSat (assignment c) [183,555,534] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_267, assignment_277, v277, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_267, assignment_277, v91, hs]
  have hc1425 : ClauseSat (assignment c) [183,554,535] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_267, assignment_277, v277, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_267, assignment_277, v91, hs]
  have hc1426 : ClauseSat (assignment c) [185,555,540] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_270, assignment_277, v277, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_270, assignment_277, v92, hs]
  have hc1427 : ClauseSat (assignment c) [185,554,541] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_270, assignment_277, v277, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_270, assignment_277, v92, hs]
  have hc1428 : ClauseSat (assignment c) [187,555,546] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_273, assignment_277, v277, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_273, assignment_277, v93, hs]
  have hc1429 : ClauseSat (assignment c) [187,554,547] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_273, assignment_277, v277, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_273, assignment_277, v93, hs]
  have hc1430 : ClauseSat (assignment c) [189,555,552] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_276, assignment_277, v277, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_276, assignment_277, v94, hs]
  have hc1431 : ClauseSat (assignment c) [189,554,553] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_276, assignment_277, v277, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_276, assignment_277, v94, hs]
  have hc1432 : ClauseSat (assignment c) [191,557] := by
    by_cases hs : c.b4.val = 0
    · simp [ClauseSat, litVal, assignment_95, assignment_278, v278, v95, hs]
    · simp [ClauseSat, litVal, assignment_95, assignment_278, v95, hs]
  have hc1433 : ClauseSat (assignment c) [193,556] := by
    by_cases hs : c.b4.val = 1
    · simp [ClauseSat, litVal, assignment_96, assignment_278, v278, v96, hs]
    · simp [ClauseSat, litVal, assignment_96, assignment_278, v96, hs]
  have hc1434 : ClauseSat (assignment c) [195,557] := by
    by_cases hs : c.b4.val = 2
    · simp [ClauseSat, litVal, assignment_97, assignment_278, v278, v97, hs]
    · simp [ClauseSat, litVal, assignment_97, assignment_278, v97, hs]
  have hc1435 : ClauseSat (assignment c) [197,556] := by
    by_cases hs : c.b4.val = 3
    · simp [ClauseSat, litVal, assignment_98, assignment_278, v278, v98, hs]
    · simp [ClauseSat, litVal, assignment_98, assignment_278, v98, hs]
  have hc1436 : ClauseSat (assignment c) [199,557,534] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_267, assignment_278, v278, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_267, assignment_278, v99, hs]
  have hc1437 : ClauseSat (assignment c) [199,556,535] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_267, assignment_278, v278, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_267, assignment_278, v99, hs]
  have hc1438 : ClauseSat (assignment c) [201,557,540] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_270, assignment_278, v278, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_270, assignment_278, v100, hs]
  have hc1439 : ClauseSat (assignment c) [201,556,541] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_270, assignment_278, v278, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_270, assignment_278, v100, hs]
  have hc1440 : ClauseSat (assignment c) [203,557,546] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_273, assignment_278, v278, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_273, assignment_278, v101, hs]
  have hc1441 : ClauseSat (assignment c) [203,556,547] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_273, assignment_278, v278, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_273, assignment_278, v101, hs]
  have hc1442 : ClauseSat (assignment c) [205,557,552] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_276, assignment_278, v278, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_276, assignment_278, v102, hs]
  have hc1443 : ClauseSat (assignment c) [205,556,553] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_276, assignment_278, v278, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_276, assignment_278, v102, hs]
  have hc1444 : ClauseSat (assignment c) [173,559,554] := by
    cases ha0 : v86 c <;> cases ha1 : v277 c <;> cases ha2 : v278 c <;> simp [ClauseSat, litVal, assignment_86, assignment_277, assignment_279, v279, ha0, ha1, ha2]
  have hc1445 : ClauseSat (assignment c) [173,559,556] := by
    cases ha0 : v86 c <;> cases ha1 : v277 c <;> cases ha2 : v278 c <;> simp [ClauseSat, litVal, assignment_86, assignment_278, assignment_279, v279, ha0, ha1, ha2]
  have hc1446 : ClauseSat (assignment c) [173,558,555,557] := by
    cases ha0 : v86 c <;> cases ha1 : v277 c <;> cases ha2 : v278 c <;> simp [ClauseSat, litVal, assignment_86, assignment_277, assignment_278, assignment_279, v279, ha0, ha1, ha2]
  have hc1447 : ClauseSat (assignment c) [172,558,555] := by
    cases ha0 : v86 c <;> cases ha1 : v277 c <;> cases ha2 : v278 c <;> simp [ClauseSat, litVal, assignment_86, assignment_277, assignment_279, v279, ha0, ha1, ha2]
  have hc1448 : ClauseSat (assignment c) [172,558,557] := by
    cases ha0 : v86 c <;> cases ha1 : v277 c <;> cases ha2 : v278 c <;> simp [ClauseSat, litVal, assignment_86, assignment_278, assignment_279, v279, ha0, ha1, ha2]
  have hc1449 : ClauseSat (assignment c) [172,559,554,556] := by
    cases ha0 : v86 c <;> cases ha1 : v277 c <;> cases ha2 : v278 c <;> simp [ClauseSat, litVal, assignment_86, assignment_277, assignment_278, assignment_279, v279, ha0, ha1, ha2]
  have hc1450 : ClauseSat (assignment c) [558] := by
    have hh := hr ⟨10, by decide⟩
    have ht : target ⟨10, by decide⟩ = true := by decide
    rw [ht] at hh
    simpa [ClauseSat, litVal, assignment_279, output] using hh
  have hc1451 : ClauseSat (assignment c) [7,560] := by
    by_cases hs : c.a0.val = 0
    · simp [ClauseSat, litVal, assignment_3, assignment_280, v280, v3, hs]
    · simp [ClauseSat, litVal, assignment_3, assignment_280, v3, hs]
  have hc1452 : ClauseSat (assignment c) [9,560] := by
    by_cases hs : c.a0.val = 1
    · simp [ClauseSat, litVal, assignment_4, assignment_280, v280, v4, hs]
    · simp [ClauseSat, litVal, assignment_4, assignment_280, v4, hs]
  have hc1453 : ClauseSat (assignment c) [11,561] := by
    by_cases hs : c.a0.val = 2
    · simp [ClauseSat, litVal, assignment_5, assignment_280, v280, v5, hs]
    · simp [ClauseSat, litVal, assignment_5, assignment_280, v5, hs]
  have hc1454 : ClauseSat (assignment c) [13,560] := by
    by_cases hs : c.a0.val = 3
    · simp [ClauseSat, litVal, assignment_6, assignment_280, v280, v6, hs]
    · simp [ClauseSat, litVal, assignment_6, assignment_280, v6, hs]
  have hc1455 : ClauseSat (assignment c) [15,562] := by
    by_cases hs : c.b0.val = 0
    · simp [ClauseSat, litVal, assignment_7, assignment_281, v281, v7, hs]
    · simp [ClauseSat, litVal, assignment_7, assignment_281, v7, hs]
  have hc1456 : ClauseSat (assignment c) [17,562] := by
    by_cases hs : c.b0.val = 1
    · simp [ClauseSat, litVal, assignment_8, assignment_281, v281, v8, hs]
    · simp [ClauseSat, litVal, assignment_8, assignment_281, v8, hs]
  have hc1457 : ClauseSat (assignment c) [19,563] := by
    by_cases hs : c.b0.val = 2
    · simp [ClauseSat, litVal, assignment_9, assignment_281, v281, v9, hs]
    · simp [ClauseSat, litVal, assignment_9, assignment_281, v9, hs]
  have hc1458 : ClauseSat (assignment c) [21,562] := by
    by_cases hs : c.b0.val = 3
    · simp [ClauseSat, litVal, assignment_10, assignment_281, v281, v10, hs]
    · simp [ClauseSat, litVal, assignment_10, assignment_281, v10, hs]
  have hc1459 : ClauseSat (assignment c) [5,565,560] := by
    cases ha0 : v2 c <;> cases ha1 : v280 c <;> cases ha2 : v281 c <;> simp [ClauseSat, litVal, assignment_2, assignment_280, assignment_282, v282, ha0, ha1, ha2]
  have hc1460 : ClauseSat (assignment c) [5,565,562] := by
    cases ha0 : v2 c <;> cases ha1 : v280 c <;> cases ha2 : v281 c <;> simp [ClauseSat, litVal, assignment_2, assignment_281, assignment_282, v282, ha0, ha1, ha2]
  have hc1461 : ClauseSat (assignment c) [5,564,561,563] := by
    cases ha0 : v2 c <;> cases ha1 : v280 c <;> cases ha2 : v281 c <;> simp [ClauseSat, litVal, assignment_2, assignment_280, assignment_281, assignment_282, v282, ha0, ha1, ha2]
  have hc1462 : ClauseSat (assignment c) [4,564,561] := by
    cases ha0 : v2 c <;> cases ha1 : v280 c <;> cases ha2 : v281 c <;> simp [ClauseSat, litVal, assignment_2, assignment_280, assignment_282, v282, ha0, ha1, ha2]
  have hc1463 : ClauseSat (assignment c) [4,564,563] := by
    cases ha0 : v2 c <;> cases ha1 : v280 c <;> cases ha2 : v281 c <;> simp [ClauseSat, litVal, assignment_2, assignment_281, assignment_282, v282, ha0, ha1, ha2]
  have hc1464 : ClauseSat (assignment c) [4,565,560,562] := by
    cases ha0 : v2 c <;> cases ha1 : v280 c <;> cases ha2 : v281 c <;> simp [ClauseSat, litVal, assignment_2, assignment_280, assignment_281, assignment_282, v282, ha0, ha1, ha2]
  have hc1465 : ClauseSat (assignment c) [37,566] := by
    by_cases hs : c.a1.val = 0
    · simp [ClauseSat, litVal, assignment_18, assignment_283, v283, v18, hs]
    · simp [ClauseSat, litVal, assignment_18, assignment_283, v18, hs]
  have hc1466 : ClauseSat (assignment c) [39,566] := by
    by_cases hs : c.a1.val = 1
    · simp [ClauseSat, litVal, assignment_19, assignment_283, v283, v19, hs]
    · simp [ClauseSat, litVal, assignment_19, assignment_283, v19, hs]
  have hc1467 : ClauseSat (assignment c) [41,567] := by
    by_cases hs : c.a1.val = 2
    · simp [ClauseSat, litVal, assignment_20, assignment_283, v283, v20, hs]
    · simp [ClauseSat, litVal, assignment_20, assignment_283, v20, hs]
  have hc1468 : ClauseSat (assignment c) [43,566] := by
    by_cases hs : c.a1.val = 3
    · simp [ClauseSat, litVal, assignment_21, assignment_283, v283, v21, hs]
    · simp [ClauseSat, litVal, assignment_21, assignment_283, v21, hs]
  have hc1469 : ClauseSat (assignment c) [45,567,564] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_282, assignment_283, v283, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_282, assignment_283, v22, hs]
  have hc1470 : ClauseSat (assignment c) [45,566,565] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_282, assignment_283, v283, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_282, assignment_283, v22, hs]
  have hc1471 : ClauseSat (assignment c) [47,568] := by
    by_cases hs : c.b1.val = 0
    · simp [ClauseSat, litVal, assignment_23, assignment_284, v284, v23, hs]
    · simp [ClauseSat, litVal, assignment_23, assignment_284, v23, hs]
  have hc1472 : ClauseSat (assignment c) [49,568] := by
    by_cases hs : c.b1.val = 1
    · simp [ClauseSat, litVal, assignment_24, assignment_284, v284, v24, hs]
    · simp [ClauseSat, litVal, assignment_24, assignment_284, v24, hs]
  have hc1473 : ClauseSat (assignment c) [51,569] := by
    by_cases hs : c.b1.val = 2
    · simp [ClauseSat, litVal, assignment_25, assignment_284, v284, v25, hs]
    · simp [ClauseSat, litVal, assignment_25, assignment_284, v25, hs]
  have hc1474 : ClauseSat (assignment c) [53,568] := by
    by_cases hs : c.b1.val = 3
    · simp [ClauseSat, litVal, assignment_26, assignment_284, v284, v26, hs]
    · simp [ClauseSat, litVal, assignment_26, assignment_284, v26, hs]
  have hc1475 : ClauseSat (assignment c) [55,569,564] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_282, assignment_284, v284, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_282, assignment_284, v27, hs]
  have hc1476 : ClauseSat (assignment c) [55,568,565] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_282, assignment_284, v284, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_282, assignment_284, v27, hs]
  have hc1477 : ClauseSat (assignment c) [35,571,566] := by
    cases ha0 : v17 c <;> cases ha1 : v283 c <;> cases ha2 : v284 c <;> simp [ClauseSat, litVal, assignment_17, assignment_283, assignment_285, v285, ha0, ha1, ha2]
  have hc1478 : ClauseSat (assignment c) [35,571,568] := by
    cases ha0 : v17 c <;> cases ha1 : v283 c <;> cases ha2 : v284 c <;> simp [ClauseSat, litVal, assignment_17, assignment_284, assignment_285, v285, ha0, ha1, ha2]
  have hc1479 : ClauseSat (assignment c) [35,570,567,569] := by
    cases ha0 : v17 c <;> cases ha1 : v283 c <;> cases ha2 : v284 c <;> simp [ClauseSat, litVal, assignment_17, assignment_283, assignment_284, assignment_285, v285, ha0, ha1, ha2]
  have hc1480 : ClauseSat (assignment c) [34,570,567] := by
    cases ha0 : v17 c <;> cases ha1 : v283 c <;> cases ha2 : v284 c <;> simp [ClauseSat, litVal, assignment_17, assignment_283, assignment_285, v285, ha0, ha1, ha2]
  have hc1481 : ClauseSat (assignment c) [34,570,569] := by
    cases ha0 : v17 c <;> cases ha1 : v283 c <;> cases ha2 : v284 c <;> simp [ClauseSat, litVal, assignment_17, assignment_284, assignment_285, v285, ha0, ha1, ha2]
  have hc1482 : ClauseSat (assignment c) [34,571,566,568] := by
    cases ha0 : v17 c <;> cases ha1 : v283 c <;> cases ha2 : v284 c <;> simp [ClauseSat, litVal, assignment_17, assignment_283, assignment_284, assignment_285, v285, ha0, ha1, ha2]
  have hc1483 : ClauseSat (assignment c) [75,572] := by
    by_cases hs : c.a2.val = 0
    · simp [ClauseSat, litVal, assignment_37, assignment_286, v286, v37, hs]
    · simp [ClauseSat, litVal, assignment_37, assignment_286, v37, hs]
  have hc1484 : ClauseSat (assignment c) [77,572] := by
    by_cases hs : c.a2.val = 1
    · simp [ClauseSat, litVal, assignment_38, assignment_286, v286, v38, hs]
    · simp [ClauseSat, litVal, assignment_38, assignment_286, v38, hs]
  have hc1485 : ClauseSat (assignment c) [79,573] := by
    by_cases hs : c.a2.val = 2
    · simp [ClauseSat, litVal, assignment_39, assignment_286, v286, v39, hs]
    · simp [ClauseSat, litVal, assignment_39, assignment_286, v39, hs]
  have hc1486 : ClauseSat (assignment c) [81,572] := by
    by_cases hs : c.a2.val = 3
    · simp [ClauseSat, litVal, assignment_40, assignment_286, v286, v40, hs]
    · simp [ClauseSat, litVal, assignment_40, assignment_286, v40, hs]
  have hc1487 : ClauseSat (assignment c) [83,573,564] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_282, assignment_286, v286, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_282, assignment_286, v41, hs]
  have hc1488 : ClauseSat (assignment c) [83,572,565] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_282, assignment_286, v286, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_282, assignment_286, v41, hs]
  have hc1489 : ClauseSat (assignment c) [85,573,570] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_285, assignment_286, v286, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_285, assignment_286, v42, hs]
  have hc1490 : ClauseSat (assignment c) [85,572,571] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_285, assignment_286, v286, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_285, assignment_286, v42, hs]
  have hc1491 : ClauseSat (assignment c) [87,574] := by
    by_cases hs : c.b2.val = 0
    · simp [ClauseSat, litVal, assignment_43, assignment_287, v287, v43, hs]
    · simp [ClauseSat, litVal, assignment_43, assignment_287, v43, hs]
  have hc1492 : ClauseSat (assignment c) [89,574] := by
    by_cases hs : c.b2.val = 1
    · simp [ClauseSat, litVal, assignment_44, assignment_287, v287, v44, hs]
    · simp [ClauseSat, litVal, assignment_44, assignment_287, v44, hs]
  have hc1493 : ClauseSat (assignment c) [91,575] := by
    by_cases hs : c.b2.val = 2
    · simp [ClauseSat, litVal, assignment_45, assignment_287, v287, v45, hs]
    · simp [ClauseSat, litVal, assignment_45, assignment_287, v45, hs]
  have hc1494 : ClauseSat (assignment c) [93,574] := by
    by_cases hs : c.b2.val = 3
    · simp [ClauseSat, litVal, assignment_46, assignment_287, v287, v46, hs]
    · simp [ClauseSat, litVal, assignment_46, assignment_287, v46, hs]
  have hc1495 : ClauseSat (assignment c) [95,575,564] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_282, assignment_287, v287, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_282, assignment_287, v47, hs]
  have hc1496 : ClauseSat (assignment c) [95,574,565] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_282, assignment_287, v287, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_282, assignment_287, v47, hs]
  have hc1497 : ClauseSat (assignment c) [97,575,570] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_285, assignment_287, v287, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_285, assignment_287, v48, hs]
  have hc1498 : ClauseSat (assignment c) [97,574,571] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_285, assignment_287, v287, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_285, assignment_287, v48, hs]
  have hc1499 : ClauseSat (assignment c) [73,577,572] := by
    cases ha0 : v36 c <;> cases ha1 : v286 c <;> cases ha2 : v287 c <;> simp [ClauseSat, litVal, assignment_36, assignment_286, assignment_288, v288, ha0, ha1, ha2]
  simp only [chunk14, List.forall_mem_cons]
  exact ⟨hc1400, hc1401, hc1402, hc1403, hc1404, hc1405, hc1406, hc1407, hc1408, hc1409, hc1410, hc1411, hc1412, hc1413, hc1414, hc1415, hc1416, hc1417, hc1418, hc1419, hc1420, hc1421, hc1422, hc1423, hc1424, hc1425, hc1426, hc1427, hc1428, hc1429, hc1430, hc1431, hc1432, hc1433, hc1434, hc1435, hc1436, hc1437, hc1438, hc1439, hc1440, hc1441, hc1442, hc1443, hc1444, hc1445, hc1446, hc1447, hc1448, hc1449, hc1450, hc1451, hc1452, hc1453, hc1454, hc1455, hc1456, hc1457, hc1458, hc1459, hc1460, hc1461, hc1462, hc1463, hc1464, hc1465, hc1466, hc1467, hc1468, hc1469, hc1470, hc1471, hc1472, hc1473, hc1474, hc1475, hc1476, hc1477, hc1478, hc1479, hc1480, hc1481, hc1482, hc1483, hc1484, hc1485, hc1486, hc1487, hc1488, hc1489, hc1490, hc1491, hc1492, hc1493, hc1494, hc1495, hc1496, hc1497, hc1498, hc1499, by simp⟩
#check satChunk14

def chunk15 : List (List Nat) := [[73, 577, 574], [73, 576, 573, 575], [72, 576, 573], [72, 576, 575], [72, 577, 572, 574], [121, 578], [123, 578], [125, 579], [127, 578], [129, 579, 564], [129, 578, 565], [131, 579, 570], [131, 578, 571], [133, 579, 576], [133, 578, 577], [135, 580], [137, 580], [139, 581], [141, 580], [143, 581, 564], [143, 580, 565], [145, 581, 570], [145, 580, 571], [147, 581, 576], [147, 580, 577], [119, 583, 578], [119, 583, 580], [119, 582, 579, 581], [118, 582, 579], [118, 582, 581], [118, 583, 578, 580], [175, 584], [177, 584], [179, 585], [181, 584], [183, 585, 564], [183, 584, 565], [185, 585, 570], [185, 584, 571], [187, 585, 576], [187, 584, 577], [189, 585, 582], [189, 584, 583], [191, 586], [193, 586], [195, 587], [197, 586], [199, 587, 564], [199, 586, 565], [201, 587, 570], [201, 586, 571], [203, 587, 576], [203, 586, 577], [205, 587, 582], [205, 586, 583], [173, 589, 584], [173, 589, 586], [173, 588, 585, 587], [172, 588, 585], [172, 588, 587], [172, 589, 584, 586], [588], [7, 591], [9, 591], [11, 590], [13, 590], [15, 593], [17, 593], [19, 592], [21, 592], [5, 595, 590], [5, 595, 592], [5, 594, 591, 593], [4, 594, 591], [4, 594, 593], [4, 595, 590, 592], [37, 597], [39, 597], [41, 596], [43, 596], [45, 597, 594], [45, 596, 595], [47, 599], [49, 599], [51, 598], [53, 598], [55, 599, 594], [55, 598, 595], [35, 601, 596], [35, 601, 598], [35, 600, 597, 599], [34, 600, 597], [34, 600, 599], [34, 601, 596, 598], [75, 603], [77, 603], [79, 602], [81, 602], [83, 603, 594], [83, 602, 595]]
theorem satChunk15 (c : Candidate) (hv : valid c)
    (hr : ∀ r : Fin 16, output c r = target r)
    (hl : derivativeLeft c = false) (hd : derivativeRight c = false) :
    ∀ cl ∈ chunk15, ClauseSat (assignment c) cl := by
  rcases hv with ⟨h0, h1, h2, h3, h4⟩
  have hc1500 : ClauseSat (assignment c) [73,577,574] := by
    cases ha0 : v36 c <;> cases ha1 : v286 c <;> cases ha2 : v287 c <;> simp [ClauseSat, litVal, assignment_36, assignment_287, assignment_288, v288, ha0, ha1, ha2]
  have hc1501 : ClauseSat (assignment c) [73,576,573,575] := by
    cases ha0 : v36 c <;> cases ha1 : v286 c <;> cases ha2 : v287 c <;> simp [ClauseSat, litVal, assignment_36, assignment_286, assignment_287, assignment_288, v288, ha0, ha1, ha2]
  have hc1502 : ClauseSat (assignment c) [72,576,573] := by
    cases ha0 : v36 c <;> cases ha1 : v286 c <;> cases ha2 : v287 c <;> simp [ClauseSat, litVal, assignment_36, assignment_286, assignment_288, v288, ha0, ha1, ha2]
  have hc1503 : ClauseSat (assignment c) [72,576,575] := by
    cases ha0 : v36 c <;> cases ha1 : v286 c <;> cases ha2 : v287 c <;> simp [ClauseSat, litVal, assignment_36, assignment_287, assignment_288, v288, ha0, ha1, ha2]
  have hc1504 : ClauseSat (assignment c) [72,577,572,574] := by
    cases ha0 : v36 c <;> cases ha1 : v286 c <;> cases ha2 : v287 c <;> simp [ClauseSat, litVal, assignment_36, assignment_286, assignment_287, assignment_288, v288, ha0, ha1, ha2]
  have hc1505 : ClauseSat (assignment c) [121,578] := by
    by_cases hs : c.a3.val = 0
    · simp [ClauseSat, litVal, assignment_60, assignment_289, v289, v60, hs]
    · simp [ClauseSat, litVal, assignment_60, assignment_289, v60, hs]
  have hc1506 : ClauseSat (assignment c) [123,578] := by
    by_cases hs : c.a3.val = 1
    · simp [ClauseSat, litVal, assignment_61, assignment_289, v289, v61, hs]
    · simp [ClauseSat, litVal, assignment_61, assignment_289, v61, hs]
  have hc1507 : ClauseSat (assignment c) [125,579] := by
    by_cases hs : c.a3.val = 2
    · simp [ClauseSat, litVal, assignment_62, assignment_289, v289, v62, hs]
    · simp [ClauseSat, litVal, assignment_62, assignment_289, v62, hs]
  have hc1508 : ClauseSat (assignment c) [127,578] := by
    by_cases hs : c.a3.val = 3
    · simp [ClauseSat, litVal, assignment_63, assignment_289, v289, v63, hs]
    · simp [ClauseSat, litVal, assignment_63, assignment_289, v63, hs]
  have hc1509 : ClauseSat (assignment c) [129,579,564] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_282, assignment_289, v289, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_282, assignment_289, v64, hs]
  have hc1510 : ClauseSat (assignment c) [129,578,565] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_282, assignment_289, v289, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_282, assignment_289, v64, hs]
  have hc1511 : ClauseSat (assignment c) [131,579,570] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_285, assignment_289, v289, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_285, assignment_289, v65, hs]
  have hc1512 : ClauseSat (assignment c) [131,578,571] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_285, assignment_289, v289, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_285, assignment_289, v65, hs]
  have hc1513 : ClauseSat (assignment c) [133,579,576] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_288, assignment_289, v289, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_288, assignment_289, v66, hs]
  have hc1514 : ClauseSat (assignment c) [133,578,577] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_288, assignment_289, v289, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_288, assignment_289, v66, hs]
  have hc1515 : ClauseSat (assignment c) [135,580] := by
    by_cases hs : c.b3.val = 0
    · simp [ClauseSat, litVal, assignment_67, assignment_290, v290, v67, hs]
    · simp [ClauseSat, litVal, assignment_67, assignment_290, v67, hs]
  have hc1516 : ClauseSat (assignment c) [137,580] := by
    by_cases hs : c.b3.val = 1
    · simp [ClauseSat, litVal, assignment_68, assignment_290, v290, v68, hs]
    · simp [ClauseSat, litVal, assignment_68, assignment_290, v68, hs]
  have hc1517 : ClauseSat (assignment c) [139,581] := by
    by_cases hs : c.b3.val = 2
    · simp [ClauseSat, litVal, assignment_69, assignment_290, v290, v69, hs]
    · simp [ClauseSat, litVal, assignment_69, assignment_290, v69, hs]
  have hc1518 : ClauseSat (assignment c) [141,580] := by
    by_cases hs : c.b3.val = 3
    · simp [ClauseSat, litVal, assignment_70, assignment_290, v290, v70, hs]
    · simp [ClauseSat, litVal, assignment_70, assignment_290, v70, hs]
  have hc1519 : ClauseSat (assignment c) [143,581,564] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_282, assignment_290, v290, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_282, assignment_290, v71, hs]
  have hc1520 : ClauseSat (assignment c) [143,580,565] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_282, assignment_290, v290, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_282, assignment_290, v71, hs]
  have hc1521 : ClauseSat (assignment c) [145,581,570] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_285, assignment_290, v290, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_285, assignment_290, v72, hs]
  have hc1522 : ClauseSat (assignment c) [145,580,571] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_285, assignment_290, v290, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_285, assignment_290, v72, hs]
  have hc1523 : ClauseSat (assignment c) [147,581,576] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_288, assignment_290, v290, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_288, assignment_290, v73, hs]
  have hc1524 : ClauseSat (assignment c) [147,580,577] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_288, assignment_290, v290, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_288, assignment_290, v73, hs]
  have hc1525 : ClauseSat (assignment c) [119,583,578] := by
    cases ha0 : v59 c <;> cases ha1 : v289 c <;> cases ha2 : v290 c <;> simp [ClauseSat, litVal, assignment_59, assignment_289, assignment_291, v291, ha0, ha1, ha2]
  have hc1526 : ClauseSat (assignment c) [119,583,580] := by
    cases ha0 : v59 c <;> cases ha1 : v289 c <;> cases ha2 : v290 c <;> simp [ClauseSat, litVal, assignment_59, assignment_290, assignment_291, v291, ha0, ha1, ha2]
  have hc1527 : ClauseSat (assignment c) [119,582,579,581] := by
    cases ha0 : v59 c <;> cases ha1 : v289 c <;> cases ha2 : v290 c <;> simp [ClauseSat, litVal, assignment_59, assignment_289, assignment_290, assignment_291, v291, ha0, ha1, ha2]
  have hc1528 : ClauseSat (assignment c) [118,582,579] := by
    cases ha0 : v59 c <;> cases ha1 : v289 c <;> cases ha2 : v290 c <;> simp [ClauseSat, litVal, assignment_59, assignment_289, assignment_291, v291, ha0, ha1, ha2]
  have hc1529 : ClauseSat (assignment c) [118,582,581] := by
    cases ha0 : v59 c <;> cases ha1 : v289 c <;> cases ha2 : v290 c <;> simp [ClauseSat, litVal, assignment_59, assignment_290, assignment_291, v291, ha0, ha1, ha2]
  have hc1530 : ClauseSat (assignment c) [118,583,578,580] := by
    cases ha0 : v59 c <;> cases ha1 : v289 c <;> cases ha2 : v290 c <;> simp [ClauseSat, litVal, assignment_59, assignment_289, assignment_290, assignment_291, v291, ha0, ha1, ha2]
  have hc1531 : ClauseSat (assignment c) [175,584] := by
    by_cases hs : c.a4.val = 0
    · simp [ClauseSat, litVal, assignment_87, assignment_292, v292, v87, hs]
    · simp [ClauseSat, litVal, assignment_87, assignment_292, v87, hs]
  have hc1532 : ClauseSat (assignment c) [177,584] := by
    by_cases hs : c.a4.val = 1
    · simp [ClauseSat, litVal, assignment_88, assignment_292, v292, v88, hs]
    · simp [ClauseSat, litVal, assignment_88, assignment_292, v88, hs]
  have hc1533 : ClauseSat (assignment c) [179,585] := by
    by_cases hs : c.a4.val = 2
    · simp [ClauseSat, litVal, assignment_89, assignment_292, v292, v89, hs]
    · simp [ClauseSat, litVal, assignment_89, assignment_292, v89, hs]
  have hc1534 : ClauseSat (assignment c) [181,584] := by
    by_cases hs : c.a4.val = 3
    · simp [ClauseSat, litVal, assignment_90, assignment_292, v292, v90, hs]
    · simp [ClauseSat, litVal, assignment_90, assignment_292, v90, hs]
  have hc1535 : ClauseSat (assignment c) [183,585,564] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_282, assignment_292, v292, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_282, assignment_292, v91, hs]
  have hc1536 : ClauseSat (assignment c) [183,584,565] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_282, assignment_292, v292, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_282, assignment_292, v91, hs]
  have hc1537 : ClauseSat (assignment c) [185,585,570] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_285, assignment_292, v292, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_285, assignment_292, v92, hs]
  have hc1538 : ClauseSat (assignment c) [185,584,571] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_285, assignment_292, v292, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_285, assignment_292, v92, hs]
  have hc1539 : ClauseSat (assignment c) [187,585,576] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_288, assignment_292, v292, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_288, assignment_292, v93, hs]
  have hc1540 : ClauseSat (assignment c) [187,584,577] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_288, assignment_292, v292, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_288, assignment_292, v93, hs]
  have hc1541 : ClauseSat (assignment c) [189,585,582] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_291, assignment_292, v292, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_291, assignment_292, v94, hs]
  have hc1542 : ClauseSat (assignment c) [189,584,583] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_291, assignment_292, v292, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_291, assignment_292, v94, hs]
  have hc1543 : ClauseSat (assignment c) [191,586] := by
    by_cases hs : c.b4.val = 0
    · simp [ClauseSat, litVal, assignment_95, assignment_293, v293, v95, hs]
    · simp [ClauseSat, litVal, assignment_95, assignment_293, v95, hs]
  have hc1544 : ClauseSat (assignment c) [193,586] := by
    by_cases hs : c.b4.val = 1
    · simp [ClauseSat, litVal, assignment_96, assignment_293, v293, v96, hs]
    · simp [ClauseSat, litVal, assignment_96, assignment_293, v96, hs]
  have hc1545 : ClauseSat (assignment c) [195,587] := by
    by_cases hs : c.b4.val = 2
    · simp [ClauseSat, litVal, assignment_97, assignment_293, v293, v97, hs]
    · simp [ClauseSat, litVal, assignment_97, assignment_293, v97, hs]
  have hc1546 : ClauseSat (assignment c) [197,586] := by
    by_cases hs : c.b4.val = 3
    · simp [ClauseSat, litVal, assignment_98, assignment_293, v293, v98, hs]
    · simp [ClauseSat, litVal, assignment_98, assignment_293, v98, hs]
  have hc1547 : ClauseSat (assignment c) [199,587,564] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_282, assignment_293, v293, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_282, assignment_293, v99, hs]
  have hc1548 : ClauseSat (assignment c) [199,586,565] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_282, assignment_293, v293, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_282, assignment_293, v99, hs]
  have hc1549 : ClauseSat (assignment c) [201,587,570] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_285, assignment_293, v293, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_285, assignment_293, v100, hs]
  have hc1550 : ClauseSat (assignment c) [201,586,571] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_285, assignment_293, v293, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_285, assignment_293, v100, hs]
  have hc1551 : ClauseSat (assignment c) [203,587,576] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_288, assignment_293, v293, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_288, assignment_293, v101, hs]
  have hc1552 : ClauseSat (assignment c) [203,586,577] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_288, assignment_293, v293, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_288, assignment_293, v101, hs]
  have hc1553 : ClauseSat (assignment c) [205,587,582] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_291, assignment_293, v293, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_291, assignment_293, v102, hs]
  have hc1554 : ClauseSat (assignment c) [205,586,583] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_291, assignment_293, v293, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_291, assignment_293, v102, hs]
  have hc1555 : ClauseSat (assignment c) [173,589,584] := by
    cases ha0 : v86 c <;> cases ha1 : v292 c <;> cases ha2 : v293 c <;> simp [ClauseSat, litVal, assignment_86, assignment_292, assignment_294, v294, ha0, ha1, ha2]
  have hc1556 : ClauseSat (assignment c) [173,589,586] := by
    cases ha0 : v86 c <;> cases ha1 : v292 c <;> cases ha2 : v293 c <;> simp [ClauseSat, litVal, assignment_86, assignment_293, assignment_294, v294, ha0, ha1, ha2]
  have hc1557 : ClauseSat (assignment c) [173,588,585,587] := by
    cases ha0 : v86 c <;> cases ha1 : v292 c <;> cases ha2 : v293 c <;> simp [ClauseSat, litVal, assignment_86, assignment_292, assignment_293, assignment_294, v294, ha0, ha1, ha2]
  have hc1558 : ClauseSat (assignment c) [172,588,585] := by
    cases ha0 : v86 c <;> cases ha1 : v292 c <;> cases ha2 : v293 c <;> simp [ClauseSat, litVal, assignment_86, assignment_292, assignment_294, v294, ha0, ha1, ha2]
  have hc1559 : ClauseSat (assignment c) [172,588,587] := by
    cases ha0 : v86 c <;> cases ha1 : v292 c <;> cases ha2 : v293 c <;> simp [ClauseSat, litVal, assignment_86, assignment_293, assignment_294, v294, ha0, ha1, ha2]
  have hc1560 : ClauseSat (assignment c) [172,589,584,586] := by
    cases ha0 : v86 c <;> cases ha1 : v292 c <;> cases ha2 : v293 c <;> simp [ClauseSat, litVal, assignment_86, assignment_292, assignment_293, assignment_294, v294, ha0, ha1, ha2]
  have hc1561 : ClauseSat (assignment c) [588] := by
    have hh := hr ⟨11, by decide⟩
    have ht : target ⟨11, by decide⟩ = true := by decide
    rw [ht] at hh
    simpa [ClauseSat, litVal, assignment_294, output] using hh
  have hc1562 : ClauseSat (assignment c) [7,591] := by
    by_cases hs : c.a0.val = 0
    · simp [ClauseSat, litVal, assignment_3, assignment_295, v295, v3, hs]
    · simp [ClauseSat, litVal, assignment_3, assignment_295, v3, hs]
  have hc1563 : ClauseSat (assignment c) [9,591] := by
    by_cases hs : c.a0.val = 1
    · simp [ClauseSat, litVal, assignment_4, assignment_295, v295, v4, hs]
    · simp [ClauseSat, litVal, assignment_4, assignment_295, v4, hs]
  have hc1564 : ClauseSat (assignment c) [11,590] := by
    by_cases hs : c.a0.val = 2
    · simp [ClauseSat, litVal, assignment_5, assignment_295, v295, v5, hs]
    · simp [ClauseSat, litVal, assignment_5, assignment_295, v5, hs]
  have hc1565 : ClauseSat (assignment c) [13,590] := by
    by_cases hs : c.a0.val = 3
    · simp [ClauseSat, litVal, assignment_6, assignment_295, v295, v6, hs]
    · simp [ClauseSat, litVal, assignment_6, assignment_295, v6, hs]
  have hc1566 : ClauseSat (assignment c) [15,593] := by
    by_cases hs : c.b0.val = 0
    · simp [ClauseSat, litVal, assignment_7, assignment_296, v296, v7, hs]
    · simp [ClauseSat, litVal, assignment_7, assignment_296, v7, hs]
  have hc1567 : ClauseSat (assignment c) [17,593] := by
    by_cases hs : c.b0.val = 1
    · simp [ClauseSat, litVal, assignment_8, assignment_296, v296, v8, hs]
    · simp [ClauseSat, litVal, assignment_8, assignment_296, v8, hs]
  have hc1568 : ClauseSat (assignment c) [19,592] := by
    by_cases hs : c.b0.val = 2
    · simp [ClauseSat, litVal, assignment_9, assignment_296, v296, v9, hs]
    · simp [ClauseSat, litVal, assignment_9, assignment_296, v9, hs]
  have hc1569 : ClauseSat (assignment c) [21,592] := by
    by_cases hs : c.b0.val = 3
    · simp [ClauseSat, litVal, assignment_10, assignment_296, v296, v10, hs]
    · simp [ClauseSat, litVal, assignment_10, assignment_296, v10, hs]
  have hc1570 : ClauseSat (assignment c) [5,595,590] := by
    cases ha0 : v2 c <;> cases ha1 : v295 c <;> cases ha2 : v296 c <;> simp [ClauseSat, litVal, assignment_2, assignment_295, assignment_297, v297, ha0, ha1, ha2]
  have hc1571 : ClauseSat (assignment c) [5,595,592] := by
    cases ha0 : v2 c <;> cases ha1 : v295 c <;> cases ha2 : v296 c <;> simp [ClauseSat, litVal, assignment_2, assignment_296, assignment_297, v297, ha0, ha1, ha2]
  have hc1572 : ClauseSat (assignment c) [5,594,591,593] := by
    cases ha0 : v2 c <;> cases ha1 : v295 c <;> cases ha2 : v296 c <;> simp [ClauseSat, litVal, assignment_2, assignment_295, assignment_296, assignment_297, v297, ha0, ha1, ha2]
  have hc1573 : ClauseSat (assignment c) [4,594,591] := by
    cases ha0 : v2 c <;> cases ha1 : v295 c <;> cases ha2 : v296 c <;> simp [ClauseSat, litVal, assignment_2, assignment_295, assignment_297, v297, ha0, ha1, ha2]
  have hc1574 : ClauseSat (assignment c) [4,594,593] := by
    cases ha0 : v2 c <;> cases ha1 : v295 c <;> cases ha2 : v296 c <;> simp [ClauseSat, litVal, assignment_2, assignment_296, assignment_297, v297, ha0, ha1, ha2]
  have hc1575 : ClauseSat (assignment c) [4,595,590,592] := by
    cases ha0 : v2 c <;> cases ha1 : v295 c <;> cases ha2 : v296 c <;> simp [ClauseSat, litVal, assignment_2, assignment_295, assignment_296, assignment_297, v297, ha0, ha1, ha2]
  have hc1576 : ClauseSat (assignment c) [37,597] := by
    by_cases hs : c.a1.val = 0
    · simp [ClauseSat, litVal, assignment_18, assignment_298, v298, v18, hs]
    · simp [ClauseSat, litVal, assignment_18, assignment_298, v18, hs]
  have hc1577 : ClauseSat (assignment c) [39,597] := by
    by_cases hs : c.a1.val = 1
    · simp [ClauseSat, litVal, assignment_19, assignment_298, v298, v19, hs]
    · simp [ClauseSat, litVal, assignment_19, assignment_298, v19, hs]
  have hc1578 : ClauseSat (assignment c) [41,596] := by
    by_cases hs : c.a1.val = 2
    · simp [ClauseSat, litVal, assignment_20, assignment_298, v298, v20, hs]
    · simp [ClauseSat, litVal, assignment_20, assignment_298, v20, hs]
  have hc1579 : ClauseSat (assignment c) [43,596] := by
    by_cases hs : c.a1.val = 3
    · simp [ClauseSat, litVal, assignment_21, assignment_298, v298, v21, hs]
    · simp [ClauseSat, litVal, assignment_21, assignment_298, v21, hs]
  have hc1580 : ClauseSat (assignment c) [45,597,594] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_297, assignment_298, v298, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_297, assignment_298, v22, hs]
  have hc1581 : ClauseSat (assignment c) [45,596,595] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_297, assignment_298, v298, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_297, assignment_298, v22, hs]
  have hc1582 : ClauseSat (assignment c) [47,599] := by
    by_cases hs : c.b1.val = 0
    · simp [ClauseSat, litVal, assignment_23, assignment_299, v299, v23, hs]
    · simp [ClauseSat, litVal, assignment_23, assignment_299, v23, hs]
  have hc1583 : ClauseSat (assignment c) [49,599] := by
    by_cases hs : c.b1.val = 1
    · simp [ClauseSat, litVal, assignment_24, assignment_299, v299, v24, hs]
    · simp [ClauseSat, litVal, assignment_24, assignment_299, v24, hs]
  have hc1584 : ClauseSat (assignment c) [51,598] := by
    by_cases hs : c.b1.val = 2
    · simp [ClauseSat, litVal, assignment_25, assignment_299, v299, v25, hs]
    · simp [ClauseSat, litVal, assignment_25, assignment_299, v25, hs]
  have hc1585 : ClauseSat (assignment c) [53,598] := by
    by_cases hs : c.b1.val = 3
    · simp [ClauseSat, litVal, assignment_26, assignment_299, v299, v26, hs]
    · simp [ClauseSat, litVal, assignment_26, assignment_299, v26, hs]
  have hc1586 : ClauseSat (assignment c) [55,599,594] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_297, assignment_299, v299, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_297, assignment_299, v27, hs]
  have hc1587 : ClauseSat (assignment c) [55,598,595] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_297, assignment_299, v299, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_297, assignment_299, v27, hs]
  have hc1588 : ClauseSat (assignment c) [35,601,596] := by
    cases ha0 : v17 c <;> cases ha1 : v298 c <;> cases ha2 : v299 c <;> simp [ClauseSat, litVal, assignment_17, assignment_298, assignment_300, v300, ha0, ha1, ha2]
  have hc1589 : ClauseSat (assignment c) [35,601,598] := by
    cases ha0 : v17 c <;> cases ha1 : v298 c <;> cases ha2 : v299 c <;> simp [ClauseSat, litVal, assignment_17, assignment_299, assignment_300, v300, ha0, ha1, ha2]
  have hc1590 : ClauseSat (assignment c) [35,600,597,599] := by
    cases ha0 : v17 c <;> cases ha1 : v298 c <;> cases ha2 : v299 c <;> simp [ClauseSat, litVal, assignment_17, assignment_298, assignment_299, assignment_300, v300, ha0, ha1, ha2]
  have hc1591 : ClauseSat (assignment c) [34,600,597] := by
    cases ha0 : v17 c <;> cases ha1 : v298 c <;> cases ha2 : v299 c <;> simp [ClauseSat, litVal, assignment_17, assignment_298, assignment_300, v300, ha0, ha1, ha2]
  have hc1592 : ClauseSat (assignment c) [34,600,599] := by
    cases ha0 : v17 c <;> cases ha1 : v298 c <;> cases ha2 : v299 c <;> simp [ClauseSat, litVal, assignment_17, assignment_299, assignment_300, v300, ha0, ha1, ha2]
  have hc1593 : ClauseSat (assignment c) [34,601,596,598] := by
    cases ha0 : v17 c <;> cases ha1 : v298 c <;> cases ha2 : v299 c <;> simp [ClauseSat, litVal, assignment_17, assignment_298, assignment_299, assignment_300, v300, ha0, ha1, ha2]
  have hc1594 : ClauseSat (assignment c) [75,603] := by
    by_cases hs : c.a2.val = 0
    · simp [ClauseSat, litVal, assignment_37, assignment_301, v301, v37, hs]
    · simp [ClauseSat, litVal, assignment_37, assignment_301, v37, hs]
  have hc1595 : ClauseSat (assignment c) [77,603] := by
    by_cases hs : c.a2.val = 1
    · simp [ClauseSat, litVal, assignment_38, assignment_301, v301, v38, hs]
    · simp [ClauseSat, litVal, assignment_38, assignment_301, v38, hs]
  have hc1596 : ClauseSat (assignment c) [79,602] := by
    by_cases hs : c.a2.val = 2
    · simp [ClauseSat, litVal, assignment_39, assignment_301, v301, v39, hs]
    · simp [ClauseSat, litVal, assignment_39, assignment_301, v39, hs]
  have hc1597 : ClauseSat (assignment c) [81,602] := by
    by_cases hs : c.a2.val = 3
    · simp [ClauseSat, litVal, assignment_40, assignment_301, v301, v40, hs]
    · simp [ClauseSat, litVal, assignment_40, assignment_301, v40, hs]
  have hc1598 : ClauseSat (assignment c) [83,603,594] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_297, assignment_301, v301, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_297, assignment_301, v41, hs]
  have hc1599 : ClauseSat (assignment c) [83,602,595] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_297, assignment_301, v301, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_297, assignment_301, v41, hs]
  simp only [chunk15, List.forall_mem_cons]
  exact ⟨hc1500, hc1501, hc1502, hc1503, hc1504, hc1505, hc1506, hc1507, hc1508, hc1509, hc1510, hc1511, hc1512, hc1513, hc1514, hc1515, hc1516, hc1517, hc1518, hc1519, hc1520, hc1521, hc1522, hc1523, hc1524, hc1525, hc1526, hc1527, hc1528, hc1529, hc1530, hc1531, hc1532, hc1533, hc1534, hc1535, hc1536, hc1537, hc1538, hc1539, hc1540, hc1541, hc1542, hc1543, hc1544, hc1545, hc1546, hc1547, hc1548, hc1549, hc1550, hc1551, hc1552, hc1553, hc1554, hc1555, hc1556, hc1557, hc1558, hc1559, hc1560, hc1561, hc1562, hc1563, hc1564, hc1565, hc1566, hc1567, hc1568, hc1569, hc1570, hc1571, hc1572, hc1573, hc1574, hc1575, hc1576, hc1577, hc1578, hc1579, hc1580, hc1581, hc1582, hc1583, hc1584, hc1585, hc1586, hc1587, hc1588, hc1589, hc1590, hc1591, hc1592, hc1593, hc1594, hc1595, hc1596, hc1597, hc1598, hc1599, by simp⟩
#check satChunk15

def chunk16 : List (List Nat) := [[85, 603, 600], [85, 602, 601], [87, 605], [89, 605], [91, 604], [93, 604], [95, 605, 594], [95, 604, 595], [97, 605, 600], [97, 604, 601], [73, 607, 602], [73, 607, 604], [73, 606, 603, 605], [72, 606, 603], [72, 606, 605], [72, 607, 602, 604], [121, 609], [123, 609], [125, 608], [127, 608], [129, 609, 594], [129, 608, 595], [131, 609, 600], [131, 608, 601], [133, 609, 606], [133, 608, 607], [135, 611], [137, 611], [139, 610], [141, 610], [143, 611, 594], [143, 610, 595], [145, 611, 600], [145, 610, 601], [147, 611, 606], [147, 610, 607], [119, 613, 608], [119, 613, 610], [119, 612, 609, 611], [118, 612, 609], [118, 612, 611], [118, 613, 608, 610], [175, 615], [177, 615], [179, 614], [181, 614], [183, 615, 594], [183, 614, 595], [185, 615, 600], [185, 614, 601], [187, 615, 606], [187, 614, 607], [189, 615, 612], [189, 614, 613], [191, 617], [193, 617], [195, 616], [197, 616], [199, 617, 594], [199, 616, 595], [201, 617, 600], [201, 616, 601], [203, 617, 606], [203, 616, 607], [205, 617, 612], [205, 616, 613], [173, 619, 614], [173, 619, 616], [173, 618, 615, 617], [172, 618, 615], [172, 618, 617], [172, 619, 614, 616], [619], [7, 620], [9, 621], [11, 620], [13, 620], [15, 622], [17, 623], [19, 622], [21, 622], [5, 625, 620], [5, 625, 622], [5, 624, 621, 623], [4, 624, 621], [4, 624, 623], [4, 625, 620, 622], [37, 626], [39, 627], [41, 626], [43, 626], [45, 627, 624], [45, 626, 625], [47, 628], [49, 629], [51, 628], [53, 628], [55, 629, 624], [55, 628, 625], [35, 631, 626]]
theorem satChunk16 (c : Candidate) (hv : valid c)
    (hr : ∀ r : Fin 16, output c r = target r)
    (hl : derivativeLeft c = false) (hd : derivativeRight c = false) :
    ∀ cl ∈ chunk16, ClauseSat (assignment c) cl := by
  rcases hv with ⟨h0, h1, h2, h3, h4⟩
  have hc1600 : ClauseSat (assignment c) [85,603,600] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_300, assignment_301, v301, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_300, assignment_301, v42, hs]
  have hc1601 : ClauseSat (assignment c) [85,602,601] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_300, assignment_301, v301, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_300, assignment_301, v42, hs]
  have hc1602 : ClauseSat (assignment c) [87,605] := by
    by_cases hs : c.b2.val = 0
    · simp [ClauseSat, litVal, assignment_43, assignment_302, v302, v43, hs]
    · simp [ClauseSat, litVal, assignment_43, assignment_302, v43, hs]
  have hc1603 : ClauseSat (assignment c) [89,605] := by
    by_cases hs : c.b2.val = 1
    · simp [ClauseSat, litVal, assignment_44, assignment_302, v302, v44, hs]
    · simp [ClauseSat, litVal, assignment_44, assignment_302, v44, hs]
  have hc1604 : ClauseSat (assignment c) [91,604] := by
    by_cases hs : c.b2.val = 2
    · simp [ClauseSat, litVal, assignment_45, assignment_302, v302, v45, hs]
    · simp [ClauseSat, litVal, assignment_45, assignment_302, v45, hs]
  have hc1605 : ClauseSat (assignment c) [93,604] := by
    by_cases hs : c.b2.val = 3
    · simp [ClauseSat, litVal, assignment_46, assignment_302, v302, v46, hs]
    · simp [ClauseSat, litVal, assignment_46, assignment_302, v46, hs]
  have hc1606 : ClauseSat (assignment c) [95,605,594] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_297, assignment_302, v302, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_297, assignment_302, v47, hs]
  have hc1607 : ClauseSat (assignment c) [95,604,595] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_297, assignment_302, v302, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_297, assignment_302, v47, hs]
  have hc1608 : ClauseSat (assignment c) [97,605,600] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_300, assignment_302, v302, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_300, assignment_302, v48, hs]
  have hc1609 : ClauseSat (assignment c) [97,604,601] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_300, assignment_302, v302, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_300, assignment_302, v48, hs]
  have hc1610 : ClauseSat (assignment c) [73,607,602] := by
    cases ha0 : v36 c <;> cases ha1 : v301 c <;> cases ha2 : v302 c <;> simp [ClauseSat, litVal, assignment_36, assignment_301, assignment_303, v303, ha0, ha1, ha2]
  have hc1611 : ClauseSat (assignment c) [73,607,604] := by
    cases ha0 : v36 c <;> cases ha1 : v301 c <;> cases ha2 : v302 c <;> simp [ClauseSat, litVal, assignment_36, assignment_302, assignment_303, v303, ha0, ha1, ha2]
  have hc1612 : ClauseSat (assignment c) [73,606,603,605] := by
    cases ha0 : v36 c <;> cases ha1 : v301 c <;> cases ha2 : v302 c <;> simp [ClauseSat, litVal, assignment_36, assignment_301, assignment_302, assignment_303, v303, ha0, ha1, ha2]
  have hc1613 : ClauseSat (assignment c) [72,606,603] := by
    cases ha0 : v36 c <;> cases ha1 : v301 c <;> cases ha2 : v302 c <;> simp [ClauseSat, litVal, assignment_36, assignment_301, assignment_303, v303, ha0, ha1, ha2]
  have hc1614 : ClauseSat (assignment c) [72,606,605] := by
    cases ha0 : v36 c <;> cases ha1 : v301 c <;> cases ha2 : v302 c <;> simp [ClauseSat, litVal, assignment_36, assignment_302, assignment_303, v303, ha0, ha1, ha2]
  have hc1615 : ClauseSat (assignment c) [72,607,602,604] := by
    cases ha0 : v36 c <;> cases ha1 : v301 c <;> cases ha2 : v302 c <;> simp [ClauseSat, litVal, assignment_36, assignment_301, assignment_302, assignment_303, v303, ha0, ha1, ha2]
  have hc1616 : ClauseSat (assignment c) [121,609] := by
    by_cases hs : c.a3.val = 0
    · simp [ClauseSat, litVal, assignment_60, assignment_304, v304, v60, hs]
    · simp [ClauseSat, litVal, assignment_60, assignment_304, v60, hs]
  have hc1617 : ClauseSat (assignment c) [123,609] := by
    by_cases hs : c.a3.val = 1
    · simp [ClauseSat, litVal, assignment_61, assignment_304, v304, v61, hs]
    · simp [ClauseSat, litVal, assignment_61, assignment_304, v61, hs]
  have hc1618 : ClauseSat (assignment c) [125,608] := by
    by_cases hs : c.a3.val = 2
    · simp [ClauseSat, litVal, assignment_62, assignment_304, v304, v62, hs]
    · simp [ClauseSat, litVal, assignment_62, assignment_304, v62, hs]
  have hc1619 : ClauseSat (assignment c) [127,608] := by
    by_cases hs : c.a3.val = 3
    · simp [ClauseSat, litVal, assignment_63, assignment_304, v304, v63, hs]
    · simp [ClauseSat, litVal, assignment_63, assignment_304, v63, hs]
  have hc1620 : ClauseSat (assignment c) [129,609,594] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_297, assignment_304, v304, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_297, assignment_304, v64, hs]
  have hc1621 : ClauseSat (assignment c) [129,608,595] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_297, assignment_304, v304, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_297, assignment_304, v64, hs]
  have hc1622 : ClauseSat (assignment c) [131,609,600] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_300, assignment_304, v304, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_300, assignment_304, v65, hs]
  have hc1623 : ClauseSat (assignment c) [131,608,601] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_300, assignment_304, v304, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_300, assignment_304, v65, hs]
  have hc1624 : ClauseSat (assignment c) [133,609,606] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_303, assignment_304, v304, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_303, assignment_304, v66, hs]
  have hc1625 : ClauseSat (assignment c) [133,608,607] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_303, assignment_304, v304, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_303, assignment_304, v66, hs]
  have hc1626 : ClauseSat (assignment c) [135,611] := by
    by_cases hs : c.b3.val = 0
    · simp [ClauseSat, litVal, assignment_67, assignment_305, v305, v67, hs]
    · simp [ClauseSat, litVal, assignment_67, assignment_305, v67, hs]
  have hc1627 : ClauseSat (assignment c) [137,611] := by
    by_cases hs : c.b3.val = 1
    · simp [ClauseSat, litVal, assignment_68, assignment_305, v305, v68, hs]
    · simp [ClauseSat, litVal, assignment_68, assignment_305, v68, hs]
  have hc1628 : ClauseSat (assignment c) [139,610] := by
    by_cases hs : c.b3.val = 2
    · simp [ClauseSat, litVal, assignment_69, assignment_305, v305, v69, hs]
    · simp [ClauseSat, litVal, assignment_69, assignment_305, v69, hs]
  have hc1629 : ClauseSat (assignment c) [141,610] := by
    by_cases hs : c.b3.val = 3
    · simp [ClauseSat, litVal, assignment_70, assignment_305, v305, v70, hs]
    · simp [ClauseSat, litVal, assignment_70, assignment_305, v70, hs]
  have hc1630 : ClauseSat (assignment c) [143,611,594] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_297, assignment_305, v305, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_297, assignment_305, v71, hs]
  have hc1631 : ClauseSat (assignment c) [143,610,595] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_297, assignment_305, v305, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_297, assignment_305, v71, hs]
  have hc1632 : ClauseSat (assignment c) [145,611,600] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_300, assignment_305, v305, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_300, assignment_305, v72, hs]
  have hc1633 : ClauseSat (assignment c) [145,610,601] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_300, assignment_305, v305, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_300, assignment_305, v72, hs]
  have hc1634 : ClauseSat (assignment c) [147,611,606] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_303, assignment_305, v305, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_303, assignment_305, v73, hs]
  have hc1635 : ClauseSat (assignment c) [147,610,607] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_303, assignment_305, v305, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_303, assignment_305, v73, hs]
  have hc1636 : ClauseSat (assignment c) [119,613,608] := by
    cases ha0 : v59 c <;> cases ha1 : v304 c <;> cases ha2 : v305 c <;> simp [ClauseSat, litVal, assignment_59, assignment_304, assignment_306, v306, ha0, ha1, ha2]
  have hc1637 : ClauseSat (assignment c) [119,613,610] := by
    cases ha0 : v59 c <;> cases ha1 : v304 c <;> cases ha2 : v305 c <;> simp [ClauseSat, litVal, assignment_59, assignment_305, assignment_306, v306, ha0, ha1, ha2]
  have hc1638 : ClauseSat (assignment c) [119,612,609,611] := by
    cases ha0 : v59 c <;> cases ha1 : v304 c <;> cases ha2 : v305 c <;> simp [ClauseSat, litVal, assignment_59, assignment_304, assignment_305, assignment_306, v306, ha0, ha1, ha2]
  have hc1639 : ClauseSat (assignment c) [118,612,609] := by
    cases ha0 : v59 c <;> cases ha1 : v304 c <;> cases ha2 : v305 c <;> simp [ClauseSat, litVal, assignment_59, assignment_304, assignment_306, v306, ha0, ha1, ha2]
  have hc1640 : ClauseSat (assignment c) [118,612,611] := by
    cases ha0 : v59 c <;> cases ha1 : v304 c <;> cases ha2 : v305 c <;> simp [ClauseSat, litVal, assignment_59, assignment_305, assignment_306, v306, ha0, ha1, ha2]
  have hc1641 : ClauseSat (assignment c) [118,613,608,610] := by
    cases ha0 : v59 c <;> cases ha1 : v304 c <;> cases ha2 : v305 c <;> simp [ClauseSat, litVal, assignment_59, assignment_304, assignment_305, assignment_306, v306, ha0, ha1, ha2]
  have hc1642 : ClauseSat (assignment c) [175,615] := by
    by_cases hs : c.a4.val = 0
    · simp [ClauseSat, litVal, assignment_87, assignment_307, v307, v87, hs]
    · simp [ClauseSat, litVal, assignment_87, assignment_307, v87, hs]
  have hc1643 : ClauseSat (assignment c) [177,615] := by
    by_cases hs : c.a4.val = 1
    · simp [ClauseSat, litVal, assignment_88, assignment_307, v307, v88, hs]
    · simp [ClauseSat, litVal, assignment_88, assignment_307, v88, hs]
  have hc1644 : ClauseSat (assignment c) [179,614] := by
    by_cases hs : c.a4.val = 2
    · simp [ClauseSat, litVal, assignment_89, assignment_307, v307, v89, hs]
    · simp [ClauseSat, litVal, assignment_89, assignment_307, v89, hs]
  have hc1645 : ClauseSat (assignment c) [181,614] := by
    by_cases hs : c.a4.val = 3
    · simp [ClauseSat, litVal, assignment_90, assignment_307, v307, v90, hs]
    · simp [ClauseSat, litVal, assignment_90, assignment_307, v90, hs]
  have hc1646 : ClauseSat (assignment c) [183,615,594] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_297, assignment_307, v307, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_297, assignment_307, v91, hs]
  have hc1647 : ClauseSat (assignment c) [183,614,595] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_297, assignment_307, v307, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_297, assignment_307, v91, hs]
  have hc1648 : ClauseSat (assignment c) [185,615,600] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_300, assignment_307, v307, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_300, assignment_307, v92, hs]
  have hc1649 : ClauseSat (assignment c) [185,614,601] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_300, assignment_307, v307, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_300, assignment_307, v92, hs]
  have hc1650 : ClauseSat (assignment c) [187,615,606] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_303, assignment_307, v307, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_303, assignment_307, v93, hs]
  have hc1651 : ClauseSat (assignment c) [187,614,607] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_303, assignment_307, v307, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_303, assignment_307, v93, hs]
  have hc1652 : ClauseSat (assignment c) [189,615,612] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_306, assignment_307, v307, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_306, assignment_307, v94, hs]
  have hc1653 : ClauseSat (assignment c) [189,614,613] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_306, assignment_307, v307, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_306, assignment_307, v94, hs]
  have hc1654 : ClauseSat (assignment c) [191,617] := by
    by_cases hs : c.b4.val = 0
    · simp [ClauseSat, litVal, assignment_95, assignment_308, v308, v95, hs]
    · simp [ClauseSat, litVal, assignment_95, assignment_308, v95, hs]
  have hc1655 : ClauseSat (assignment c) [193,617] := by
    by_cases hs : c.b4.val = 1
    · simp [ClauseSat, litVal, assignment_96, assignment_308, v308, v96, hs]
    · simp [ClauseSat, litVal, assignment_96, assignment_308, v96, hs]
  have hc1656 : ClauseSat (assignment c) [195,616] := by
    by_cases hs : c.b4.val = 2
    · simp [ClauseSat, litVal, assignment_97, assignment_308, v308, v97, hs]
    · simp [ClauseSat, litVal, assignment_97, assignment_308, v97, hs]
  have hc1657 : ClauseSat (assignment c) [197,616] := by
    by_cases hs : c.b4.val = 3
    · simp [ClauseSat, litVal, assignment_98, assignment_308, v308, v98, hs]
    · simp [ClauseSat, litVal, assignment_98, assignment_308, v98, hs]
  have hc1658 : ClauseSat (assignment c) [199,617,594] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_297, assignment_308, v308, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_297, assignment_308, v99, hs]
  have hc1659 : ClauseSat (assignment c) [199,616,595] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_297, assignment_308, v308, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_297, assignment_308, v99, hs]
  have hc1660 : ClauseSat (assignment c) [201,617,600] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_300, assignment_308, v308, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_300, assignment_308, v100, hs]
  have hc1661 : ClauseSat (assignment c) [201,616,601] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_300, assignment_308, v308, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_300, assignment_308, v100, hs]
  have hc1662 : ClauseSat (assignment c) [203,617,606] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_303, assignment_308, v308, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_303, assignment_308, v101, hs]
  have hc1663 : ClauseSat (assignment c) [203,616,607] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_303, assignment_308, v308, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_303, assignment_308, v101, hs]
  have hc1664 : ClauseSat (assignment c) [205,617,612] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_306, assignment_308, v308, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_306, assignment_308, v102, hs]
  have hc1665 : ClauseSat (assignment c) [205,616,613] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_306, assignment_308, v308, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_306, assignment_308, v102, hs]
  have hc1666 : ClauseSat (assignment c) [173,619,614] := by
    cases ha0 : v86 c <;> cases ha1 : v307 c <;> cases ha2 : v308 c <;> simp [ClauseSat, litVal, assignment_86, assignment_307, assignment_309, v309, ha0, ha1, ha2]
  have hc1667 : ClauseSat (assignment c) [173,619,616] := by
    cases ha0 : v86 c <;> cases ha1 : v307 c <;> cases ha2 : v308 c <;> simp [ClauseSat, litVal, assignment_86, assignment_308, assignment_309, v309, ha0, ha1, ha2]
  have hc1668 : ClauseSat (assignment c) [173,618,615,617] := by
    cases ha0 : v86 c <;> cases ha1 : v307 c <;> cases ha2 : v308 c <;> simp [ClauseSat, litVal, assignment_86, assignment_307, assignment_308, assignment_309, v309, ha0, ha1, ha2]
  have hc1669 : ClauseSat (assignment c) [172,618,615] := by
    cases ha0 : v86 c <;> cases ha1 : v307 c <;> cases ha2 : v308 c <;> simp [ClauseSat, litVal, assignment_86, assignment_307, assignment_309, v309, ha0, ha1, ha2]
  have hc1670 : ClauseSat (assignment c) [172,618,617] := by
    cases ha0 : v86 c <;> cases ha1 : v307 c <;> cases ha2 : v308 c <;> simp [ClauseSat, litVal, assignment_86, assignment_308, assignment_309, v309, ha0, ha1, ha2]
  have hc1671 : ClauseSat (assignment c) [172,619,614,616] := by
    cases ha0 : v86 c <;> cases ha1 : v307 c <;> cases ha2 : v308 c <;> simp [ClauseSat, litVal, assignment_86, assignment_307, assignment_308, assignment_309, v309, ha0, ha1, ha2]
  have hc1672 : ClauseSat (assignment c) [619] := by
    have hh := hr ⟨12, by decide⟩
    have ht : target ⟨12, by decide⟩ = false := by decide
    rw [ht] at hh
    simpa [ClauseSat, litVal, assignment_309, output] using hh
  have hc1673 : ClauseSat (assignment c) [7,620] := by
    by_cases hs : c.a0.val = 0
    · simp [ClauseSat, litVal, assignment_3, assignment_310, v310, v3, hs]
    · simp [ClauseSat, litVal, assignment_3, assignment_310, v3, hs]
  have hc1674 : ClauseSat (assignment c) [9,621] := by
    by_cases hs : c.a0.val = 1
    · simp [ClauseSat, litVal, assignment_4, assignment_310, v310, v4, hs]
    · simp [ClauseSat, litVal, assignment_4, assignment_310, v4, hs]
  have hc1675 : ClauseSat (assignment c) [11,620] := by
    by_cases hs : c.a0.val = 2
    · simp [ClauseSat, litVal, assignment_5, assignment_310, v310, v5, hs]
    · simp [ClauseSat, litVal, assignment_5, assignment_310, v5, hs]
  have hc1676 : ClauseSat (assignment c) [13,620] := by
    by_cases hs : c.a0.val = 3
    · simp [ClauseSat, litVal, assignment_6, assignment_310, v310, v6, hs]
    · simp [ClauseSat, litVal, assignment_6, assignment_310, v6, hs]
  have hc1677 : ClauseSat (assignment c) [15,622] := by
    by_cases hs : c.b0.val = 0
    · simp [ClauseSat, litVal, assignment_7, assignment_311, v311, v7, hs]
    · simp [ClauseSat, litVal, assignment_7, assignment_311, v7, hs]
  have hc1678 : ClauseSat (assignment c) [17,623] := by
    by_cases hs : c.b0.val = 1
    · simp [ClauseSat, litVal, assignment_8, assignment_311, v311, v8, hs]
    · simp [ClauseSat, litVal, assignment_8, assignment_311, v8, hs]
  have hc1679 : ClauseSat (assignment c) [19,622] := by
    by_cases hs : c.b0.val = 2
    · simp [ClauseSat, litVal, assignment_9, assignment_311, v311, v9, hs]
    · simp [ClauseSat, litVal, assignment_9, assignment_311, v9, hs]
  have hc1680 : ClauseSat (assignment c) [21,622] := by
    by_cases hs : c.b0.val = 3
    · simp [ClauseSat, litVal, assignment_10, assignment_311, v311, v10, hs]
    · simp [ClauseSat, litVal, assignment_10, assignment_311, v10, hs]
  have hc1681 : ClauseSat (assignment c) [5,625,620] := by
    cases ha0 : v2 c <;> cases ha1 : v310 c <;> cases ha2 : v311 c <;> simp [ClauseSat, litVal, assignment_2, assignment_310, assignment_312, v312, ha0, ha1, ha2]
  have hc1682 : ClauseSat (assignment c) [5,625,622] := by
    cases ha0 : v2 c <;> cases ha1 : v310 c <;> cases ha2 : v311 c <;> simp [ClauseSat, litVal, assignment_2, assignment_311, assignment_312, v312, ha0, ha1, ha2]
  have hc1683 : ClauseSat (assignment c) [5,624,621,623] := by
    cases ha0 : v2 c <;> cases ha1 : v310 c <;> cases ha2 : v311 c <;> simp [ClauseSat, litVal, assignment_2, assignment_310, assignment_311, assignment_312, v312, ha0, ha1, ha2]
  have hc1684 : ClauseSat (assignment c) [4,624,621] := by
    cases ha0 : v2 c <;> cases ha1 : v310 c <;> cases ha2 : v311 c <;> simp [ClauseSat, litVal, assignment_2, assignment_310, assignment_312, v312, ha0, ha1, ha2]
  have hc1685 : ClauseSat (assignment c) [4,624,623] := by
    cases ha0 : v2 c <;> cases ha1 : v310 c <;> cases ha2 : v311 c <;> simp [ClauseSat, litVal, assignment_2, assignment_311, assignment_312, v312, ha0, ha1, ha2]
  have hc1686 : ClauseSat (assignment c) [4,625,620,622] := by
    cases ha0 : v2 c <;> cases ha1 : v310 c <;> cases ha2 : v311 c <;> simp [ClauseSat, litVal, assignment_2, assignment_310, assignment_311, assignment_312, v312, ha0, ha1, ha2]
  have hc1687 : ClauseSat (assignment c) [37,626] := by
    by_cases hs : c.a1.val = 0
    · simp [ClauseSat, litVal, assignment_18, assignment_313, v313, v18, hs]
    · simp [ClauseSat, litVal, assignment_18, assignment_313, v18, hs]
  have hc1688 : ClauseSat (assignment c) [39,627] := by
    by_cases hs : c.a1.val = 1
    · simp [ClauseSat, litVal, assignment_19, assignment_313, v313, v19, hs]
    · simp [ClauseSat, litVal, assignment_19, assignment_313, v19, hs]
  have hc1689 : ClauseSat (assignment c) [41,626] := by
    by_cases hs : c.a1.val = 2
    · simp [ClauseSat, litVal, assignment_20, assignment_313, v313, v20, hs]
    · simp [ClauseSat, litVal, assignment_20, assignment_313, v20, hs]
  have hc1690 : ClauseSat (assignment c) [43,626] := by
    by_cases hs : c.a1.val = 3
    · simp [ClauseSat, litVal, assignment_21, assignment_313, v313, v21, hs]
    · simp [ClauseSat, litVal, assignment_21, assignment_313, v21, hs]
  have hc1691 : ClauseSat (assignment c) [45,627,624] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_312, assignment_313, v313, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_312, assignment_313, v22, hs]
  have hc1692 : ClauseSat (assignment c) [45,626,625] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_312, assignment_313, v313, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_312, assignment_313, v22, hs]
  have hc1693 : ClauseSat (assignment c) [47,628] := by
    by_cases hs : c.b1.val = 0
    · simp [ClauseSat, litVal, assignment_23, assignment_314, v314, v23, hs]
    · simp [ClauseSat, litVal, assignment_23, assignment_314, v23, hs]
  have hc1694 : ClauseSat (assignment c) [49,629] := by
    by_cases hs : c.b1.val = 1
    · simp [ClauseSat, litVal, assignment_24, assignment_314, v314, v24, hs]
    · simp [ClauseSat, litVal, assignment_24, assignment_314, v24, hs]
  have hc1695 : ClauseSat (assignment c) [51,628] := by
    by_cases hs : c.b1.val = 2
    · simp [ClauseSat, litVal, assignment_25, assignment_314, v314, v25, hs]
    · simp [ClauseSat, litVal, assignment_25, assignment_314, v25, hs]
  have hc1696 : ClauseSat (assignment c) [53,628] := by
    by_cases hs : c.b1.val = 3
    · simp [ClauseSat, litVal, assignment_26, assignment_314, v314, v26, hs]
    · simp [ClauseSat, litVal, assignment_26, assignment_314, v26, hs]
  have hc1697 : ClauseSat (assignment c) [55,629,624] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_312, assignment_314, v314, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_312, assignment_314, v27, hs]
  have hc1698 : ClauseSat (assignment c) [55,628,625] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_312, assignment_314, v314, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_312, assignment_314, v27, hs]
  have hc1699 : ClauseSat (assignment c) [35,631,626] := by
    cases ha0 : v17 c <;> cases ha1 : v313 c <;> cases ha2 : v314 c <;> simp [ClauseSat, litVal, assignment_17, assignment_313, assignment_315, v315, ha0, ha1, ha2]
  simp only [chunk16, List.forall_mem_cons]
  exact ⟨hc1600, hc1601, hc1602, hc1603, hc1604, hc1605, hc1606, hc1607, hc1608, hc1609, hc1610, hc1611, hc1612, hc1613, hc1614, hc1615, hc1616, hc1617, hc1618, hc1619, hc1620, hc1621, hc1622, hc1623, hc1624, hc1625, hc1626, hc1627, hc1628, hc1629, hc1630, hc1631, hc1632, hc1633, hc1634, hc1635, hc1636, hc1637, hc1638, hc1639, hc1640, hc1641, hc1642, hc1643, hc1644, hc1645, hc1646, hc1647, hc1648, hc1649, hc1650, hc1651, hc1652, hc1653, hc1654, hc1655, hc1656, hc1657, hc1658, hc1659, hc1660, hc1661, hc1662, hc1663, hc1664, hc1665, hc1666, hc1667, hc1668, hc1669, hc1670, hc1671, hc1672, hc1673, hc1674, hc1675, hc1676, hc1677, hc1678, hc1679, hc1680, hc1681, hc1682, hc1683, hc1684, hc1685, hc1686, hc1687, hc1688, hc1689, hc1690, hc1691, hc1692, hc1693, hc1694, hc1695, hc1696, hc1697, hc1698, hc1699, by simp⟩
#check satChunk16

def chunk17 : List (List Nat) := [[35, 631, 628], [35, 630, 627, 629], [34, 630, 627], [34, 630, 629], [34, 631, 626, 628], [75, 632], [77, 633], [79, 632], [81, 632], [83, 633, 624], [83, 632, 625], [85, 633, 630], [85, 632, 631], [87, 634], [89, 635], [91, 634], [93, 634], [95, 635, 624], [95, 634, 625], [97, 635, 630], [97, 634, 631], [73, 637, 632], [73, 637, 634], [73, 636, 633, 635], [72, 636, 633], [72, 636, 635], [72, 637, 632, 634], [121, 638], [123, 639], [125, 638], [127, 638], [129, 639, 624], [129, 638, 625], [131, 639, 630], [131, 638, 631], [133, 639, 636], [133, 638, 637], [135, 640], [137, 641], [139, 640], [141, 640], [143, 641, 624], [143, 640, 625], [145, 641, 630], [145, 640, 631], [147, 641, 636], [147, 640, 637], [119, 643, 638], [119, 643, 640], [119, 642, 639, 641], [118, 642, 639], [118, 642, 641], [118, 643, 638, 640], [175, 644], [177, 645], [179, 644], [181, 644], [183, 645, 624], [183, 644, 625], [185, 645, 630], [185, 644, 631], [187, 645, 636], [187, 644, 637], [189, 645, 642], [189, 644, 643], [191, 646], [193, 647], [195, 646], [197, 646], [199, 647, 624], [199, 646, 625], [201, 647, 630], [201, 646, 631], [203, 647, 636], [203, 646, 637], [205, 647, 642], [205, 646, 643], [173, 649, 644], [173, 649, 646], [173, 648, 645, 647], [172, 648, 645], [172, 648, 647], [172, 649, 644, 646], [648], [7, 651], [9, 650], [11, 650], [13, 650], [15, 653], [17, 652], [19, 652], [21, 652], [5, 655, 650], [5, 655, 652], [5, 654, 651, 653], [4, 654, 651], [4, 654, 653], [4, 655, 650, 652], [37, 657], [39, 656]]
theorem satChunk17 (c : Candidate) (hv : valid c)
    (hr : ∀ r : Fin 16, output c r = target r)
    (hl : derivativeLeft c = false) (hd : derivativeRight c = false) :
    ∀ cl ∈ chunk17, ClauseSat (assignment c) cl := by
  rcases hv with ⟨h0, h1, h2, h3, h4⟩
  have hc1700 : ClauseSat (assignment c) [35,631,628] := by
    cases ha0 : v17 c <;> cases ha1 : v313 c <;> cases ha2 : v314 c <;> simp [ClauseSat, litVal, assignment_17, assignment_314, assignment_315, v315, ha0, ha1, ha2]
  have hc1701 : ClauseSat (assignment c) [35,630,627,629] := by
    cases ha0 : v17 c <;> cases ha1 : v313 c <;> cases ha2 : v314 c <;> simp [ClauseSat, litVal, assignment_17, assignment_313, assignment_314, assignment_315, v315, ha0, ha1, ha2]
  have hc1702 : ClauseSat (assignment c) [34,630,627] := by
    cases ha0 : v17 c <;> cases ha1 : v313 c <;> cases ha2 : v314 c <;> simp [ClauseSat, litVal, assignment_17, assignment_313, assignment_315, v315, ha0, ha1, ha2]
  have hc1703 : ClauseSat (assignment c) [34,630,629] := by
    cases ha0 : v17 c <;> cases ha1 : v313 c <;> cases ha2 : v314 c <;> simp [ClauseSat, litVal, assignment_17, assignment_314, assignment_315, v315, ha0, ha1, ha2]
  have hc1704 : ClauseSat (assignment c) [34,631,626,628] := by
    cases ha0 : v17 c <;> cases ha1 : v313 c <;> cases ha2 : v314 c <;> simp [ClauseSat, litVal, assignment_17, assignment_313, assignment_314, assignment_315, v315, ha0, ha1, ha2]
  have hc1705 : ClauseSat (assignment c) [75,632] := by
    by_cases hs : c.a2.val = 0
    · simp [ClauseSat, litVal, assignment_37, assignment_316, v316, v37, hs]
    · simp [ClauseSat, litVal, assignment_37, assignment_316, v37, hs]
  have hc1706 : ClauseSat (assignment c) [77,633] := by
    by_cases hs : c.a2.val = 1
    · simp [ClauseSat, litVal, assignment_38, assignment_316, v316, v38, hs]
    · simp [ClauseSat, litVal, assignment_38, assignment_316, v38, hs]
  have hc1707 : ClauseSat (assignment c) [79,632] := by
    by_cases hs : c.a2.val = 2
    · simp [ClauseSat, litVal, assignment_39, assignment_316, v316, v39, hs]
    · simp [ClauseSat, litVal, assignment_39, assignment_316, v39, hs]
  have hc1708 : ClauseSat (assignment c) [81,632] := by
    by_cases hs : c.a2.val = 3
    · simp [ClauseSat, litVal, assignment_40, assignment_316, v316, v40, hs]
    · simp [ClauseSat, litVal, assignment_40, assignment_316, v40, hs]
  have hc1709 : ClauseSat (assignment c) [83,633,624] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_312, assignment_316, v316, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_312, assignment_316, v41, hs]
  have hc1710 : ClauseSat (assignment c) [83,632,625] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_312, assignment_316, v316, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_312, assignment_316, v41, hs]
  have hc1711 : ClauseSat (assignment c) [85,633,630] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_315, assignment_316, v316, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_315, assignment_316, v42, hs]
  have hc1712 : ClauseSat (assignment c) [85,632,631] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_315, assignment_316, v316, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_315, assignment_316, v42, hs]
  have hc1713 : ClauseSat (assignment c) [87,634] := by
    by_cases hs : c.b2.val = 0
    · simp [ClauseSat, litVal, assignment_43, assignment_317, v317, v43, hs]
    · simp [ClauseSat, litVal, assignment_43, assignment_317, v43, hs]
  have hc1714 : ClauseSat (assignment c) [89,635] := by
    by_cases hs : c.b2.val = 1
    · simp [ClauseSat, litVal, assignment_44, assignment_317, v317, v44, hs]
    · simp [ClauseSat, litVal, assignment_44, assignment_317, v44, hs]
  have hc1715 : ClauseSat (assignment c) [91,634] := by
    by_cases hs : c.b2.val = 2
    · simp [ClauseSat, litVal, assignment_45, assignment_317, v317, v45, hs]
    · simp [ClauseSat, litVal, assignment_45, assignment_317, v45, hs]
  have hc1716 : ClauseSat (assignment c) [93,634] := by
    by_cases hs : c.b2.val = 3
    · simp [ClauseSat, litVal, assignment_46, assignment_317, v317, v46, hs]
    · simp [ClauseSat, litVal, assignment_46, assignment_317, v46, hs]
  have hc1717 : ClauseSat (assignment c) [95,635,624] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_312, assignment_317, v317, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_312, assignment_317, v47, hs]
  have hc1718 : ClauseSat (assignment c) [95,634,625] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_312, assignment_317, v317, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_312, assignment_317, v47, hs]
  have hc1719 : ClauseSat (assignment c) [97,635,630] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_315, assignment_317, v317, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_315, assignment_317, v48, hs]
  have hc1720 : ClauseSat (assignment c) [97,634,631] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_315, assignment_317, v317, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_315, assignment_317, v48, hs]
  have hc1721 : ClauseSat (assignment c) [73,637,632] := by
    cases ha0 : v36 c <;> cases ha1 : v316 c <;> cases ha2 : v317 c <;> simp [ClauseSat, litVal, assignment_36, assignment_316, assignment_318, v318, ha0, ha1, ha2]
  have hc1722 : ClauseSat (assignment c) [73,637,634] := by
    cases ha0 : v36 c <;> cases ha1 : v316 c <;> cases ha2 : v317 c <;> simp [ClauseSat, litVal, assignment_36, assignment_317, assignment_318, v318, ha0, ha1, ha2]
  have hc1723 : ClauseSat (assignment c) [73,636,633,635] := by
    cases ha0 : v36 c <;> cases ha1 : v316 c <;> cases ha2 : v317 c <;> simp [ClauseSat, litVal, assignment_36, assignment_316, assignment_317, assignment_318, v318, ha0, ha1, ha2]
  have hc1724 : ClauseSat (assignment c) [72,636,633] := by
    cases ha0 : v36 c <;> cases ha1 : v316 c <;> cases ha2 : v317 c <;> simp [ClauseSat, litVal, assignment_36, assignment_316, assignment_318, v318, ha0, ha1, ha2]
  have hc1725 : ClauseSat (assignment c) [72,636,635] := by
    cases ha0 : v36 c <;> cases ha1 : v316 c <;> cases ha2 : v317 c <;> simp [ClauseSat, litVal, assignment_36, assignment_317, assignment_318, v318, ha0, ha1, ha2]
  have hc1726 : ClauseSat (assignment c) [72,637,632,634] := by
    cases ha0 : v36 c <;> cases ha1 : v316 c <;> cases ha2 : v317 c <;> simp [ClauseSat, litVal, assignment_36, assignment_316, assignment_317, assignment_318, v318, ha0, ha1, ha2]
  have hc1727 : ClauseSat (assignment c) [121,638] := by
    by_cases hs : c.a3.val = 0
    · simp [ClauseSat, litVal, assignment_60, assignment_319, v319, v60, hs]
    · simp [ClauseSat, litVal, assignment_60, assignment_319, v60, hs]
  have hc1728 : ClauseSat (assignment c) [123,639] := by
    by_cases hs : c.a3.val = 1
    · simp [ClauseSat, litVal, assignment_61, assignment_319, v319, v61, hs]
    · simp [ClauseSat, litVal, assignment_61, assignment_319, v61, hs]
  have hc1729 : ClauseSat (assignment c) [125,638] := by
    by_cases hs : c.a3.val = 2
    · simp [ClauseSat, litVal, assignment_62, assignment_319, v319, v62, hs]
    · simp [ClauseSat, litVal, assignment_62, assignment_319, v62, hs]
  have hc1730 : ClauseSat (assignment c) [127,638] := by
    by_cases hs : c.a3.val = 3
    · simp [ClauseSat, litVal, assignment_63, assignment_319, v319, v63, hs]
    · simp [ClauseSat, litVal, assignment_63, assignment_319, v63, hs]
  have hc1731 : ClauseSat (assignment c) [129,639,624] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_312, assignment_319, v319, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_312, assignment_319, v64, hs]
  have hc1732 : ClauseSat (assignment c) [129,638,625] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_312, assignment_319, v319, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_312, assignment_319, v64, hs]
  have hc1733 : ClauseSat (assignment c) [131,639,630] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_315, assignment_319, v319, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_315, assignment_319, v65, hs]
  have hc1734 : ClauseSat (assignment c) [131,638,631] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_315, assignment_319, v319, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_315, assignment_319, v65, hs]
  have hc1735 : ClauseSat (assignment c) [133,639,636] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_318, assignment_319, v319, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_318, assignment_319, v66, hs]
  have hc1736 : ClauseSat (assignment c) [133,638,637] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_318, assignment_319, v319, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_318, assignment_319, v66, hs]
  have hc1737 : ClauseSat (assignment c) [135,640] := by
    by_cases hs : c.b3.val = 0
    · simp [ClauseSat, litVal, assignment_67, assignment_320, v320, v67, hs]
    · simp [ClauseSat, litVal, assignment_67, assignment_320, v67, hs]
  have hc1738 : ClauseSat (assignment c) [137,641] := by
    by_cases hs : c.b3.val = 1
    · simp [ClauseSat, litVal, assignment_68, assignment_320, v320, v68, hs]
    · simp [ClauseSat, litVal, assignment_68, assignment_320, v68, hs]
  have hc1739 : ClauseSat (assignment c) [139,640] := by
    by_cases hs : c.b3.val = 2
    · simp [ClauseSat, litVal, assignment_69, assignment_320, v320, v69, hs]
    · simp [ClauseSat, litVal, assignment_69, assignment_320, v69, hs]
  have hc1740 : ClauseSat (assignment c) [141,640] := by
    by_cases hs : c.b3.val = 3
    · simp [ClauseSat, litVal, assignment_70, assignment_320, v320, v70, hs]
    · simp [ClauseSat, litVal, assignment_70, assignment_320, v70, hs]
  have hc1741 : ClauseSat (assignment c) [143,641,624] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_312, assignment_320, v320, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_312, assignment_320, v71, hs]
  have hc1742 : ClauseSat (assignment c) [143,640,625] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_312, assignment_320, v320, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_312, assignment_320, v71, hs]
  have hc1743 : ClauseSat (assignment c) [145,641,630] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_315, assignment_320, v320, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_315, assignment_320, v72, hs]
  have hc1744 : ClauseSat (assignment c) [145,640,631] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_315, assignment_320, v320, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_315, assignment_320, v72, hs]
  have hc1745 : ClauseSat (assignment c) [147,641,636] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_318, assignment_320, v320, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_318, assignment_320, v73, hs]
  have hc1746 : ClauseSat (assignment c) [147,640,637] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_318, assignment_320, v320, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_318, assignment_320, v73, hs]
  have hc1747 : ClauseSat (assignment c) [119,643,638] := by
    cases ha0 : v59 c <;> cases ha1 : v319 c <;> cases ha2 : v320 c <;> simp [ClauseSat, litVal, assignment_59, assignment_319, assignment_321, v321, ha0, ha1, ha2]
  have hc1748 : ClauseSat (assignment c) [119,643,640] := by
    cases ha0 : v59 c <;> cases ha1 : v319 c <;> cases ha2 : v320 c <;> simp [ClauseSat, litVal, assignment_59, assignment_320, assignment_321, v321, ha0, ha1, ha2]
  have hc1749 : ClauseSat (assignment c) [119,642,639,641] := by
    cases ha0 : v59 c <;> cases ha1 : v319 c <;> cases ha2 : v320 c <;> simp [ClauseSat, litVal, assignment_59, assignment_319, assignment_320, assignment_321, v321, ha0, ha1, ha2]
  have hc1750 : ClauseSat (assignment c) [118,642,639] := by
    cases ha0 : v59 c <;> cases ha1 : v319 c <;> cases ha2 : v320 c <;> simp [ClauseSat, litVal, assignment_59, assignment_319, assignment_321, v321, ha0, ha1, ha2]
  have hc1751 : ClauseSat (assignment c) [118,642,641] := by
    cases ha0 : v59 c <;> cases ha1 : v319 c <;> cases ha2 : v320 c <;> simp [ClauseSat, litVal, assignment_59, assignment_320, assignment_321, v321, ha0, ha1, ha2]
  have hc1752 : ClauseSat (assignment c) [118,643,638,640] := by
    cases ha0 : v59 c <;> cases ha1 : v319 c <;> cases ha2 : v320 c <;> simp [ClauseSat, litVal, assignment_59, assignment_319, assignment_320, assignment_321, v321, ha0, ha1, ha2]
  have hc1753 : ClauseSat (assignment c) [175,644] := by
    by_cases hs : c.a4.val = 0
    · simp [ClauseSat, litVal, assignment_87, assignment_322, v322, v87, hs]
    · simp [ClauseSat, litVal, assignment_87, assignment_322, v87, hs]
  have hc1754 : ClauseSat (assignment c) [177,645] := by
    by_cases hs : c.a4.val = 1
    · simp [ClauseSat, litVal, assignment_88, assignment_322, v322, v88, hs]
    · simp [ClauseSat, litVal, assignment_88, assignment_322, v88, hs]
  have hc1755 : ClauseSat (assignment c) [179,644] := by
    by_cases hs : c.a4.val = 2
    · simp [ClauseSat, litVal, assignment_89, assignment_322, v322, v89, hs]
    · simp [ClauseSat, litVal, assignment_89, assignment_322, v89, hs]
  have hc1756 : ClauseSat (assignment c) [181,644] := by
    by_cases hs : c.a4.val = 3
    · simp [ClauseSat, litVal, assignment_90, assignment_322, v322, v90, hs]
    · simp [ClauseSat, litVal, assignment_90, assignment_322, v90, hs]
  have hc1757 : ClauseSat (assignment c) [183,645,624] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_312, assignment_322, v322, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_312, assignment_322, v91, hs]
  have hc1758 : ClauseSat (assignment c) [183,644,625] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_312, assignment_322, v322, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_312, assignment_322, v91, hs]
  have hc1759 : ClauseSat (assignment c) [185,645,630] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_315, assignment_322, v322, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_315, assignment_322, v92, hs]
  have hc1760 : ClauseSat (assignment c) [185,644,631] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_315, assignment_322, v322, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_315, assignment_322, v92, hs]
  have hc1761 : ClauseSat (assignment c) [187,645,636] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_318, assignment_322, v322, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_318, assignment_322, v93, hs]
  have hc1762 : ClauseSat (assignment c) [187,644,637] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_318, assignment_322, v322, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_318, assignment_322, v93, hs]
  have hc1763 : ClauseSat (assignment c) [189,645,642] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_321, assignment_322, v322, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_321, assignment_322, v94, hs]
  have hc1764 : ClauseSat (assignment c) [189,644,643] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_321, assignment_322, v322, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_321, assignment_322, v94, hs]
  have hc1765 : ClauseSat (assignment c) [191,646] := by
    by_cases hs : c.b4.val = 0
    · simp [ClauseSat, litVal, assignment_95, assignment_323, v323, v95, hs]
    · simp [ClauseSat, litVal, assignment_95, assignment_323, v95, hs]
  have hc1766 : ClauseSat (assignment c) [193,647] := by
    by_cases hs : c.b4.val = 1
    · simp [ClauseSat, litVal, assignment_96, assignment_323, v323, v96, hs]
    · simp [ClauseSat, litVal, assignment_96, assignment_323, v96, hs]
  have hc1767 : ClauseSat (assignment c) [195,646] := by
    by_cases hs : c.b4.val = 2
    · simp [ClauseSat, litVal, assignment_97, assignment_323, v323, v97, hs]
    · simp [ClauseSat, litVal, assignment_97, assignment_323, v97, hs]
  have hc1768 : ClauseSat (assignment c) [197,646] := by
    by_cases hs : c.b4.val = 3
    · simp [ClauseSat, litVal, assignment_98, assignment_323, v323, v98, hs]
    · simp [ClauseSat, litVal, assignment_98, assignment_323, v98, hs]
  have hc1769 : ClauseSat (assignment c) [199,647,624] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_312, assignment_323, v323, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_312, assignment_323, v99, hs]
  have hc1770 : ClauseSat (assignment c) [199,646,625] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_312, assignment_323, v323, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_312, assignment_323, v99, hs]
  have hc1771 : ClauseSat (assignment c) [201,647,630] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_315, assignment_323, v323, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_315, assignment_323, v100, hs]
  have hc1772 : ClauseSat (assignment c) [201,646,631] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_315, assignment_323, v323, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_315, assignment_323, v100, hs]
  have hc1773 : ClauseSat (assignment c) [203,647,636] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_318, assignment_323, v323, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_318, assignment_323, v101, hs]
  have hc1774 : ClauseSat (assignment c) [203,646,637] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_318, assignment_323, v323, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_318, assignment_323, v101, hs]
  have hc1775 : ClauseSat (assignment c) [205,647,642] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_321, assignment_323, v323, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_321, assignment_323, v102, hs]
  have hc1776 : ClauseSat (assignment c) [205,646,643] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_321, assignment_323, v323, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_321, assignment_323, v102, hs]
  have hc1777 : ClauseSat (assignment c) [173,649,644] := by
    cases ha0 : v86 c <;> cases ha1 : v322 c <;> cases ha2 : v323 c <;> simp [ClauseSat, litVal, assignment_86, assignment_322, assignment_324, v324, ha0, ha1, ha2]
  have hc1778 : ClauseSat (assignment c) [173,649,646] := by
    cases ha0 : v86 c <;> cases ha1 : v322 c <;> cases ha2 : v323 c <;> simp [ClauseSat, litVal, assignment_86, assignment_323, assignment_324, v324, ha0, ha1, ha2]
  have hc1779 : ClauseSat (assignment c) [173,648,645,647] := by
    cases ha0 : v86 c <;> cases ha1 : v322 c <;> cases ha2 : v323 c <;> simp [ClauseSat, litVal, assignment_86, assignment_322, assignment_323, assignment_324, v324, ha0, ha1, ha2]
  have hc1780 : ClauseSat (assignment c) [172,648,645] := by
    cases ha0 : v86 c <;> cases ha1 : v322 c <;> cases ha2 : v323 c <;> simp [ClauseSat, litVal, assignment_86, assignment_322, assignment_324, v324, ha0, ha1, ha2]
  have hc1781 : ClauseSat (assignment c) [172,648,647] := by
    cases ha0 : v86 c <;> cases ha1 : v322 c <;> cases ha2 : v323 c <;> simp [ClauseSat, litVal, assignment_86, assignment_323, assignment_324, v324, ha0, ha1, ha2]
  have hc1782 : ClauseSat (assignment c) [172,649,644,646] := by
    cases ha0 : v86 c <;> cases ha1 : v322 c <;> cases ha2 : v323 c <;> simp [ClauseSat, litVal, assignment_86, assignment_322, assignment_323, assignment_324, v324, ha0, ha1, ha2]
  have hc1783 : ClauseSat (assignment c) [648] := by
    have hh := hr ⟨13, by decide⟩
    have ht : target ⟨13, by decide⟩ = true := by decide
    rw [ht] at hh
    simpa [ClauseSat, litVal, assignment_324, output] using hh
  have hc1784 : ClauseSat (assignment c) [7,651] := by
    by_cases hs : c.a0.val = 0
    · simp [ClauseSat, litVal, assignment_3, assignment_325, v325, v3, hs]
    · simp [ClauseSat, litVal, assignment_3, assignment_325, v3, hs]
  have hc1785 : ClauseSat (assignment c) [9,650] := by
    by_cases hs : c.a0.val = 1
    · simp [ClauseSat, litVal, assignment_4, assignment_325, v325, v4, hs]
    · simp [ClauseSat, litVal, assignment_4, assignment_325, v4, hs]
  have hc1786 : ClauseSat (assignment c) [11,650] := by
    by_cases hs : c.a0.val = 2
    · simp [ClauseSat, litVal, assignment_5, assignment_325, v325, v5, hs]
    · simp [ClauseSat, litVal, assignment_5, assignment_325, v5, hs]
  have hc1787 : ClauseSat (assignment c) [13,650] := by
    by_cases hs : c.a0.val = 3
    · simp [ClauseSat, litVal, assignment_6, assignment_325, v325, v6, hs]
    · simp [ClauseSat, litVal, assignment_6, assignment_325, v6, hs]
  have hc1788 : ClauseSat (assignment c) [15,653] := by
    by_cases hs : c.b0.val = 0
    · simp [ClauseSat, litVal, assignment_7, assignment_326, v326, v7, hs]
    · simp [ClauseSat, litVal, assignment_7, assignment_326, v7, hs]
  have hc1789 : ClauseSat (assignment c) [17,652] := by
    by_cases hs : c.b0.val = 1
    · simp [ClauseSat, litVal, assignment_8, assignment_326, v326, v8, hs]
    · simp [ClauseSat, litVal, assignment_8, assignment_326, v8, hs]
  have hc1790 : ClauseSat (assignment c) [19,652] := by
    by_cases hs : c.b0.val = 2
    · simp [ClauseSat, litVal, assignment_9, assignment_326, v326, v9, hs]
    · simp [ClauseSat, litVal, assignment_9, assignment_326, v9, hs]
  have hc1791 : ClauseSat (assignment c) [21,652] := by
    by_cases hs : c.b0.val = 3
    · simp [ClauseSat, litVal, assignment_10, assignment_326, v326, v10, hs]
    · simp [ClauseSat, litVal, assignment_10, assignment_326, v10, hs]
  have hc1792 : ClauseSat (assignment c) [5,655,650] := by
    cases ha0 : v2 c <;> cases ha1 : v325 c <;> cases ha2 : v326 c <;> simp [ClauseSat, litVal, assignment_2, assignment_325, assignment_327, v327, ha0, ha1, ha2]
  have hc1793 : ClauseSat (assignment c) [5,655,652] := by
    cases ha0 : v2 c <;> cases ha1 : v325 c <;> cases ha2 : v326 c <;> simp [ClauseSat, litVal, assignment_2, assignment_326, assignment_327, v327, ha0, ha1, ha2]
  have hc1794 : ClauseSat (assignment c) [5,654,651,653] := by
    cases ha0 : v2 c <;> cases ha1 : v325 c <;> cases ha2 : v326 c <;> simp [ClauseSat, litVal, assignment_2, assignment_325, assignment_326, assignment_327, v327, ha0, ha1, ha2]
  have hc1795 : ClauseSat (assignment c) [4,654,651] := by
    cases ha0 : v2 c <;> cases ha1 : v325 c <;> cases ha2 : v326 c <;> simp [ClauseSat, litVal, assignment_2, assignment_325, assignment_327, v327, ha0, ha1, ha2]
  have hc1796 : ClauseSat (assignment c) [4,654,653] := by
    cases ha0 : v2 c <;> cases ha1 : v325 c <;> cases ha2 : v326 c <;> simp [ClauseSat, litVal, assignment_2, assignment_326, assignment_327, v327, ha0, ha1, ha2]
  have hc1797 : ClauseSat (assignment c) [4,655,650,652] := by
    cases ha0 : v2 c <;> cases ha1 : v325 c <;> cases ha2 : v326 c <;> simp [ClauseSat, litVal, assignment_2, assignment_325, assignment_326, assignment_327, v327, ha0, ha1, ha2]
  have hc1798 : ClauseSat (assignment c) [37,657] := by
    by_cases hs : c.a1.val = 0
    · simp [ClauseSat, litVal, assignment_18, assignment_328, v328, v18, hs]
    · simp [ClauseSat, litVal, assignment_18, assignment_328, v18, hs]
  have hc1799 : ClauseSat (assignment c) [39,656] := by
    by_cases hs : c.a1.val = 1
    · simp [ClauseSat, litVal, assignment_19, assignment_328, v328, v19, hs]
    · simp [ClauseSat, litVal, assignment_19, assignment_328, v19, hs]
  simp only [chunk17, List.forall_mem_cons]
  exact ⟨hc1700, hc1701, hc1702, hc1703, hc1704, hc1705, hc1706, hc1707, hc1708, hc1709, hc1710, hc1711, hc1712, hc1713, hc1714, hc1715, hc1716, hc1717, hc1718, hc1719, hc1720, hc1721, hc1722, hc1723, hc1724, hc1725, hc1726, hc1727, hc1728, hc1729, hc1730, hc1731, hc1732, hc1733, hc1734, hc1735, hc1736, hc1737, hc1738, hc1739, hc1740, hc1741, hc1742, hc1743, hc1744, hc1745, hc1746, hc1747, hc1748, hc1749, hc1750, hc1751, hc1752, hc1753, hc1754, hc1755, hc1756, hc1757, hc1758, hc1759, hc1760, hc1761, hc1762, hc1763, hc1764, hc1765, hc1766, hc1767, hc1768, hc1769, hc1770, hc1771, hc1772, hc1773, hc1774, hc1775, hc1776, hc1777, hc1778, hc1779, hc1780, hc1781, hc1782, hc1783, hc1784, hc1785, hc1786, hc1787, hc1788, hc1789, hc1790, hc1791, hc1792, hc1793, hc1794, hc1795, hc1796, hc1797, hc1798, hc1799, by simp⟩
#check satChunk17

def chunk18 : List (List Nat) := [[41, 656], [43, 656], [45, 657, 654], [45, 656, 655], [47, 659], [49, 658], [51, 658], [53, 658], [55, 659, 654], [55, 658, 655], [35, 661, 656], [35, 661, 658], [35, 660, 657, 659], [34, 660, 657], [34, 660, 659], [34, 661, 656, 658], [75, 663], [77, 662], [79, 662], [81, 662], [83, 663, 654], [83, 662, 655], [85, 663, 660], [85, 662, 661], [87, 665], [89, 664], [91, 664], [93, 664], [95, 665, 654], [95, 664, 655], [97, 665, 660], [97, 664, 661], [73, 667, 662], [73, 667, 664], [73, 666, 663, 665], [72, 666, 663], [72, 666, 665], [72, 667, 662, 664], [121, 669], [123, 668], [125, 668], [127, 668], [129, 669, 654], [129, 668, 655], [131, 669, 660], [131, 668, 661], [133, 669, 666], [133, 668, 667], [135, 671], [137, 670], [139, 670], [141, 670], [143, 671, 654], [143, 670, 655], [145, 671, 660], [145, 670, 661], [147, 671, 666], [147, 670, 667], [119, 673, 668], [119, 673, 670], [119, 672, 669, 671], [118, 672, 669], [118, 672, 671], [118, 673, 668, 670], [175, 675], [177, 674], [179, 674], [181, 674], [183, 675, 654], [183, 674, 655], [185, 675, 660], [185, 674, 661], [187, 675, 666], [187, 674, 667], [189, 675, 672], [189, 674, 673], [191, 677], [193, 676], [195, 676], [197, 676], [199, 677, 654], [199, 676, 655], [201, 677, 660], [201, 676, 661], [203, 677, 666], [203, 676, 667], [205, 677, 672], [205, 676, 673], [173, 679, 674], [173, 679, 676], [173, 678, 675, 677], [172, 678, 675], [172, 678, 677], [172, 679, 674, 676], [678], [5, 680], [4, 680], [4, 680], [37, 682], [39, 682]]
theorem satChunk18 (c : Candidate) (hv : valid c)
    (hr : ∀ r : Fin 16, output c r = target r)
    (hl : derivativeLeft c = false) (hd : derivativeRight c = false) :
    ∀ cl ∈ chunk18, ClauseSat (assignment c) cl := by
  rcases hv with ⟨h0, h1, h2, h3, h4⟩
  have hc1800 : ClauseSat (assignment c) [41,656] := by
    by_cases hs : c.a1.val = 2
    · simp [ClauseSat, litVal, assignment_20, assignment_328, v328, v20, hs]
    · simp [ClauseSat, litVal, assignment_20, assignment_328, v20, hs]
  have hc1801 : ClauseSat (assignment c) [43,656] := by
    by_cases hs : c.a1.val = 3
    · simp [ClauseSat, litVal, assignment_21, assignment_328, v328, v21, hs]
    · simp [ClauseSat, litVal, assignment_21, assignment_328, v21, hs]
  have hc1802 : ClauseSat (assignment c) [45,657,654] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_327, assignment_328, v328, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_327, assignment_328, v22, hs]
  have hc1803 : ClauseSat (assignment c) [45,656,655] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_327, assignment_328, v328, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_327, assignment_328, v22, hs]
  have hc1804 : ClauseSat (assignment c) [47,659] := by
    by_cases hs : c.b1.val = 0
    · simp [ClauseSat, litVal, assignment_23, assignment_329, v329, v23, hs]
    · simp [ClauseSat, litVal, assignment_23, assignment_329, v23, hs]
  have hc1805 : ClauseSat (assignment c) [49,658] := by
    by_cases hs : c.b1.val = 1
    · simp [ClauseSat, litVal, assignment_24, assignment_329, v329, v24, hs]
    · simp [ClauseSat, litVal, assignment_24, assignment_329, v24, hs]
  have hc1806 : ClauseSat (assignment c) [51,658] := by
    by_cases hs : c.b1.val = 2
    · simp [ClauseSat, litVal, assignment_25, assignment_329, v329, v25, hs]
    · simp [ClauseSat, litVal, assignment_25, assignment_329, v25, hs]
  have hc1807 : ClauseSat (assignment c) [53,658] := by
    by_cases hs : c.b1.val = 3
    · simp [ClauseSat, litVal, assignment_26, assignment_329, v329, v26, hs]
    · simp [ClauseSat, litVal, assignment_26, assignment_329, v26, hs]
  have hc1808 : ClauseSat (assignment c) [55,659,654] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_327, assignment_329, v329, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_327, assignment_329, v27, hs]
  have hc1809 : ClauseSat (assignment c) [55,658,655] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_327, assignment_329, v329, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_327, assignment_329, v27, hs]
  have hc1810 : ClauseSat (assignment c) [35,661,656] := by
    cases ha0 : v17 c <;> cases ha1 : v328 c <;> cases ha2 : v329 c <;> simp [ClauseSat, litVal, assignment_17, assignment_328, assignment_330, v330, ha0, ha1, ha2]
  have hc1811 : ClauseSat (assignment c) [35,661,658] := by
    cases ha0 : v17 c <;> cases ha1 : v328 c <;> cases ha2 : v329 c <;> simp [ClauseSat, litVal, assignment_17, assignment_329, assignment_330, v330, ha0, ha1, ha2]
  have hc1812 : ClauseSat (assignment c) [35,660,657,659] := by
    cases ha0 : v17 c <;> cases ha1 : v328 c <;> cases ha2 : v329 c <;> simp [ClauseSat, litVal, assignment_17, assignment_328, assignment_329, assignment_330, v330, ha0, ha1, ha2]
  have hc1813 : ClauseSat (assignment c) [34,660,657] := by
    cases ha0 : v17 c <;> cases ha1 : v328 c <;> cases ha2 : v329 c <;> simp [ClauseSat, litVal, assignment_17, assignment_328, assignment_330, v330, ha0, ha1, ha2]
  have hc1814 : ClauseSat (assignment c) [34,660,659] := by
    cases ha0 : v17 c <;> cases ha1 : v328 c <;> cases ha2 : v329 c <;> simp [ClauseSat, litVal, assignment_17, assignment_329, assignment_330, v330, ha0, ha1, ha2]
  have hc1815 : ClauseSat (assignment c) [34,661,656,658] := by
    cases ha0 : v17 c <;> cases ha1 : v328 c <;> cases ha2 : v329 c <;> simp [ClauseSat, litVal, assignment_17, assignment_328, assignment_329, assignment_330, v330, ha0, ha1, ha2]
  have hc1816 : ClauseSat (assignment c) [75,663] := by
    by_cases hs : c.a2.val = 0
    · simp [ClauseSat, litVal, assignment_37, assignment_331, v331, v37, hs]
    · simp [ClauseSat, litVal, assignment_37, assignment_331, v37, hs]
  have hc1817 : ClauseSat (assignment c) [77,662] := by
    by_cases hs : c.a2.val = 1
    · simp [ClauseSat, litVal, assignment_38, assignment_331, v331, v38, hs]
    · simp [ClauseSat, litVal, assignment_38, assignment_331, v38, hs]
  have hc1818 : ClauseSat (assignment c) [79,662] := by
    by_cases hs : c.a2.val = 2
    · simp [ClauseSat, litVal, assignment_39, assignment_331, v331, v39, hs]
    · simp [ClauseSat, litVal, assignment_39, assignment_331, v39, hs]
  have hc1819 : ClauseSat (assignment c) [81,662] := by
    by_cases hs : c.a2.val = 3
    · simp [ClauseSat, litVal, assignment_40, assignment_331, v331, v40, hs]
    · simp [ClauseSat, litVal, assignment_40, assignment_331, v40, hs]
  have hc1820 : ClauseSat (assignment c) [83,663,654] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_327, assignment_331, v331, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_327, assignment_331, v41, hs]
  have hc1821 : ClauseSat (assignment c) [83,662,655] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_327, assignment_331, v331, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_327, assignment_331, v41, hs]
  have hc1822 : ClauseSat (assignment c) [85,663,660] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_330, assignment_331, v331, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_330, assignment_331, v42, hs]
  have hc1823 : ClauseSat (assignment c) [85,662,661] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_330, assignment_331, v331, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_330, assignment_331, v42, hs]
  have hc1824 : ClauseSat (assignment c) [87,665] := by
    by_cases hs : c.b2.val = 0
    · simp [ClauseSat, litVal, assignment_43, assignment_332, v332, v43, hs]
    · simp [ClauseSat, litVal, assignment_43, assignment_332, v43, hs]
  have hc1825 : ClauseSat (assignment c) [89,664] := by
    by_cases hs : c.b2.val = 1
    · simp [ClauseSat, litVal, assignment_44, assignment_332, v332, v44, hs]
    · simp [ClauseSat, litVal, assignment_44, assignment_332, v44, hs]
  have hc1826 : ClauseSat (assignment c) [91,664] := by
    by_cases hs : c.b2.val = 2
    · simp [ClauseSat, litVal, assignment_45, assignment_332, v332, v45, hs]
    · simp [ClauseSat, litVal, assignment_45, assignment_332, v45, hs]
  have hc1827 : ClauseSat (assignment c) [93,664] := by
    by_cases hs : c.b2.val = 3
    · simp [ClauseSat, litVal, assignment_46, assignment_332, v332, v46, hs]
    · simp [ClauseSat, litVal, assignment_46, assignment_332, v46, hs]
  have hc1828 : ClauseSat (assignment c) [95,665,654] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_327, assignment_332, v332, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_327, assignment_332, v47, hs]
  have hc1829 : ClauseSat (assignment c) [95,664,655] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_327, assignment_332, v332, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_327, assignment_332, v47, hs]
  have hc1830 : ClauseSat (assignment c) [97,665,660] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_330, assignment_332, v332, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_330, assignment_332, v48, hs]
  have hc1831 : ClauseSat (assignment c) [97,664,661] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_330, assignment_332, v332, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_330, assignment_332, v48, hs]
  have hc1832 : ClauseSat (assignment c) [73,667,662] := by
    cases ha0 : v36 c <;> cases ha1 : v331 c <;> cases ha2 : v332 c <;> simp [ClauseSat, litVal, assignment_36, assignment_331, assignment_333, v333, ha0, ha1, ha2]
  have hc1833 : ClauseSat (assignment c) [73,667,664] := by
    cases ha0 : v36 c <;> cases ha1 : v331 c <;> cases ha2 : v332 c <;> simp [ClauseSat, litVal, assignment_36, assignment_332, assignment_333, v333, ha0, ha1, ha2]
  have hc1834 : ClauseSat (assignment c) [73,666,663,665] := by
    cases ha0 : v36 c <;> cases ha1 : v331 c <;> cases ha2 : v332 c <;> simp [ClauseSat, litVal, assignment_36, assignment_331, assignment_332, assignment_333, v333, ha0, ha1, ha2]
  have hc1835 : ClauseSat (assignment c) [72,666,663] := by
    cases ha0 : v36 c <;> cases ha1 : v331 c <;> cases ha2 : v332 c <;> simp [ClauseSat, litVal, assignment_36, assignment_331, assignment_333, v333, ha0, ha1, ha2]
  have hc1836 : ClauseSat (assignment c) [72,666,665] := by
    cases ha0 : v36 c <;> cases ha1 : v331 c <;> cases ha2 : v332 c <;> simp [ClauseSat, litVal, assignment_36, assignment_332, assignment_333, v333, ha0, ha1, ha2]
  have hc1837 : ClauseSat (assignment c) [72,667,662,664] := by
    cases ha0 : v36 c <;> cases ha1 : v331 c <;> cases ha2 : v332 c <;> simp [ClauseSat, litVal, assignment_36, assignment_331, assignment_332, assignment_333, v333, ha0, ha1, ha2]
  have hc1838 : ClauseSat (assignment c) [121,669] := by
    by_cases hs : c.a3.val = 0
    · simp [ClauseSat, litVal, assignment_60, assignment_334, v334, v60, hs]
    · simp [ClauseSat, litVal, assignment_60, assignment_334, v60, hs]
  have hc1839 : ClauseSat (assignment c) [123,668] := by
    by_cases hs : c.a3.val = 1
    · simp [ClauseSat, litVal, assignment_61, assignment_334, v334, v61, hs]
    · simp [ClauseSat, litVal, assignment_61, assignment_334, v61, hs]
  have hc1840 : ClauseSat (assignment c) [125,668] := by
    by_cases hs : c.a3.val = 2
    · simp [ClauseSat, litVal, assignment_62, assignment_334, v334, v62, hs]
    · simp [ClauseSat, litVal, assignment_62, assignment_334, v62, hs]
  have hc1841 : ClauseSat (assignment c) [127,668] := by
    by_cases hs : c.a3.val = 3
    · simp [ClauseSat, litVal, assignment_63, assignment_334, v334, v63, hs]
    · simp [ClauseSat, litVal, assignment_63, assignment_334, v63, hs]
  have hc1842 : ClauseSat (assignment c) [129,669,654] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_327, assignment_334, v334, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_327, assignment_334, v64, hs]
  have hc1843 : ClauseSat (assignment c) [129,668,655] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_327, assignment_334, v334, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_327, assignment_334, v64, hs]
  have hc1844 : ClauseSat (assignment c) [131,669,660] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_330, assignment_334, v334, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_330, assignment_334, v65, hs]
  have hc1845 : ClauseSat (assignment c) [131,668,661] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_330, assignment_334, v334, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_330, assignment_334, v65, hs]
  have hc1846 : ClauseSat (assignment c) [133,669,666] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_333, assignment_334, v334, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_333, assignment_334, v66, hs]
  have hc1847 : ClauseSat (assignment c) [133,668,667] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_333, assignment_334, v334, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_333, assignment_334, v66, hs]
  have hc1848 : ClauseSat (assignment c) [135,671] := by
    by_cases hs : c.b3.val = 0
    · simp [ClauseSat, litVal, assignment_67, assignment_335, v335, v67, hs]
    · simp [ClauseSat, litVal, assignment_67, assignment_335, v67, hs]
  have hc1849 : ClauseSat (assignment c) [137,670] := by
    by_cases hs : c.b3.val = 1
    · simp [ClauseSat, litVal, assignment_68, assignment_335, v335, v68, hs]
    · simp [ClauseSat, litVal, assignment_68, assignment_335, v68, hs]
  have hc1850 : ClauseSat (assignment c) [139,670] := by
    by_cases hs : c.b3.val = 2
    · simp [ClauseSat, litVal, assignment_69, assignment_335, v335, v69, hs]
    · simp [ClauseSat, litVal, assignment_69, assignment_335, v69, hs]
  have hc1851 : ClauseSat (assignment c) [141,670] := by
    by_cases hs : c.b3.val = 3
    · simp [ClauseSat, litVal, assignment_70, assignment_335, v335, v70, hs]
    · simp [ClauseSat, litVal, assignment_70, assignment_335, v70, hs]
  have hc1852 : ClauseSat (assignment c) [143,671,654] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_327, assignment_335, v335, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_327, assignment_335, v71, hs]
  have hc1853 : ClauseSat (assignment c) [143,670,655] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_327, assignment_335, v335, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_327, assignment_335, v71, hs]
  have hc1854 : ClauseSat (assignment c) [145,671,660] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_330, assignment_335, v335, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_330, assignment_335, v72, hs]
  have hc1855 : ClauseSat (assignment c) [145,670,661] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_330, assignment_335, v335, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_330, assignment_335, v72, hs]
  have hc1856 : ClauseSat (assignment c) [147,671,666] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_333, assignment_335, v335, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_333, assignment_335, v73, hs]
  have hc1857 : ClauseSat (assignment c) [147,670,667] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_333, assignment_335, v335, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_333, assignment_335, v73, hs]
  have hc1858 : ClauseSat (assignment c) [119,673,668] := by
    cases ha0 : v59 c <;> cases ha1 : v334 c <;> cases ha2 : v335 c <;> simp [ClauseSat, litVal, assignment_59, assignment_334, assignment_336, v336, ha0, ha1, ha2]
  have hc1859 : ClauseSat (assignment c) [119,673,670] := by
    cases ha0 : v59 c <;> cases ha1 : v334 c <;> cases ha2 : v335 c <;> simp [ClauseSat, litVal, assignment_59, assignment_335, assignment_336, v336, ha0, ha1, ha2]
  have hc1860 : ClauseSat (assignment c) [119,672,669,671] := by
    cases ha0 : v59 c <;> cases ha1 : v334 c <;> cases ha2 : v335 c <;> simp [ClauseSat, litVal, assignment_59, assignment_334, assignment_335, assignment_336, v336, ha0, ha1, ha2]
  have hc1861 : ClauseSat (assignment c) [118,672,669] := by
    cases ha0 : v59 c <;> cases ha1 : v334 c <;> cases ha2 : v335 c <;> simp [ClauseSat, litVal, assignment_59, assignment_334, assignment_336, v336, ha0, ha1, ha2]
  have hc1862 : ClauseSat (assignment c) [118,672,671] := by
    cases ha0 : v59 c <;> cases ha1 : v334 c <;> cases ha2 : v335 c <;> simp [ClauseSat, litVal, assignment_59, assignment_335, assignment_336, v336, ha0, ha1, ha2]
  have hc1863 : ClauseSat (assignment c) [118,673,668,670] := by
    cases ha0 : v59 c <;> cases ha1 : v334 c <;> cases ha2 : v335 c <;> simp [ClauseSat, litVal, assignment_59, assignment_334, assignment_335, assignment_336, v336, ha0, ha1, ha2]
  have hc1864 : ClauseSat (assignment c) [175,675] := by
    by_cases hs : c.a4.val = 0
    · simp [ClauseSat, litVal, assignment_87, assignment_337, v337, v87, hs]
    · simp [ClauseSat, litVal, assignment_87, assignment_337, v87, hs]
  have hc1865 : ClauseSat (assignment c) [177,674] := by
    by_cases hs : c.a4.val = 1
    · simp [ClauseSat, litVal, assignment_88, assignment_337, v337, v88, hs]
    · simp [ClauseSat, litVal, assignment_88, assignment_337, v88, hs]
  have hc1866 : ClauseSat (assignment c) [179,674] := by
    by_cases hs : c.a4.val = 2
    · simp [ClauseSat, litVal, assignment_89, assignment_337, v337, v89, hs]
    · simp [ClauseSat, litVal, assignment_89, assignment_337, v89, hs]
  have hc1867 : ClauseSat (assignment c) [181,674] := by
    by_cases hs : c.a4.val = 3
    · simp [ClauseSat, litVal, assignment_90, assignment_337, v337, v90, hs]
    · simp [ClauseSat, litVal, assignment_90, assignment_337, v90, hs]
  have hc1868 : ClauseSat (assignment c) [183,675,654] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_327, assignment_337, v337, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_327, assignment_337, v91, hs]
  have hc1869 : ClauseSat (assignment c) [183,674,655] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_327, assignment_337, v337, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_327, assignment_337, v91, hs]
  have hc1870 : ClauseSat (assignment c) [185,675,660] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_330, assignment_337, v337, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_330, assignment_337, v92, hs]
  have hc1871 : ClauseSat (assignment c) [185,674,661] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_330, assignment_337, v337, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_330, assignment_337, v92, hs]
  have hc1872 : ClauseSat (assignment c) [187,675,666] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_333, assignment_337, v337, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_333, assignment_337, v93, hs]
  have hc1873 : ClauseSat (assignment c) [187,674,667] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_333, assignment_337, v337, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_333, assignment_337, v93, hs]
  have hc1874 : ClauseSat (assignment c) [189,675,672] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_336, assignment_337, v337, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_336, assignment_337, v94, hs]
  have hc1875 : ClauseSat (assignment c) [189,674,673] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_336, assignment_337, v337, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_336, assignment_337, v94, hs]
  have hc1876 : ClauseSat (assignment c) [191,677] := by
    by_cases hs : c.b4.val = 0
    · simp [ClauseSat, litVal, assignment_95, assignment_338, v338, v95, hs]
    · simp [ClauseSat, litVal, assignment_95, assignment_338, v95, hs]
  have hc1877 : ClauseSat (assignment c) [193,676] := by
    by_cases hs : c.b4.val = 1
    · simp [ClauseSat, litVal, assignment_96, assignment_338, v338, v96, hs]
    · simp [ClauseSat, litVal, assignment_96, assignment_338, v96, hs]
  have hc1878 : ClauseSat (assignment c) [195,676] := by
    by_cases hs : c.b4.val = 2
    · simp [ClauseSat, litVal, assignment_97, assignment_338, v338, v97, hs]
    · simp [ClauseSat, litVal, assignment_97, assignment_338, v97, hs]
  have hc1879 : ClauseSat (assignment c) [197,676] := by
    by_cases hs : c.b4.val = 3
    · simp [ClauseSat, litVal, assignment_98, assignment_338, v338, v98, hs]
    · simp [ClauseSat, litVal, assignment_98, assignment_338, v98, hs]
  have hc1880 : ClauseSat (assignment c) [199,677,654] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_327, assignment_338, v338, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_327, assignment_338, v99, hs]
  have hc1881 : ClauseSat (assignment c) [199,676,655] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_327, assignment_338, v338, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_327, assignment_338, v99, hs]
  have hc1882 : ClauseSat (assignment c) [201,677,660] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_330, assignment_338, v338, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_330, assignment_338, v100, hs]
  have hc1883 : ClauseSat (assignment c) [201,676,661] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_330, assignment_338, v338, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_330, assignment_338, v100, hs]
  have hc1884 : ClauseSat (assignment c) [203,677,666] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_333, assignment_338, v338, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_333, assignment_338, v101, hs]
  have hc1885 : ClauseSat (assignment c) [203,676,667] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_333, assignment_338, v338, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_333, assignment_338, v101, hs]
  have hc1886 : ClauseSat (assignment c) [205,677,672] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_336, assignment_338, v338, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_336, assignment_338, v102, hs]
  have hc1887 : ClauseSat (assignment c) [205,676,673] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_336, assignment_338, v338, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_336, assignment_338, v102, hs]
  have hc1888 : ClauseSat (assignment c) [173,679,674] := by
    cases ha0 : v86 c <;> cases ha1 : v337 c <;> cases ha2 : v338 c <;> simp [ClauseSat, litVal, assignment_86, assignment_337, assignment_339, v339, ha0, ha1, ha2]
  have hc1889 : ClauseSat (assignment c) [173,679,676] := by
    cases ha0 : v86 c <;> cases ha1 : v337 c <;> cases ha2 : v338 c <;> simp [ClauseSat, litVal, assignment_86, assignment_338, assignment_339, v339, ha0, ha1, ha2]
  have hc1890 : ClauseSat (assignment c) [173,678,675,677] := by
    cases ha0 : v86 c <;> cases ha1 : v337 c <;> cases ha2 : v338 c <;> simp [ClauseSat, litVal, assignment_86, assignment_337, assignment_338, assignment_339, v339, ha0, ha1, ha2]
  have hc1891 : ClauseSat (assignment c) [172,678,675] := by
    cases ha0 : v86 c <;> cases ha1 : v337 c <;> cases ha2 : v338 c <;> simp [ClauseSat, litVal, assignment_86, assignment_337, assignment_339, v339, ha0, ha1, ha2]
  have hc1892 : ClauseSat (assignment c) [172,678,677] := by
    cases ha0 : v86 c <;> cases ha1 : v337 c <;> cases ha2 : v338 c <;> simp [ClauseSat, litVal, assignment_86, assignment_338, assignment_339, v339, ha0, ha1, ha2]
  have hc1893 : ClauseSat (assignment c) [172,679,674,676] := by
    cases ha0 : v86 c <;> cases ha1 : v337 c <;> cases ha2 : v338 c <;> simp [ClauseSat, litVal, assignment_86, assignment_337, assignment_338, assignment_339, v339, ha0, ha1, ha2]
  have hc1894 : ClauseSat (assignment c) [678] := by
    have hh := hr ⟨14, by decide⟩
    have ht : target ⟨14, by decide⟩ = true := by decide
    rw [ht] at hh
    simpa [ClauseSat, litVal, assignment_339, output] using hh
  have hc1895 : ClauseSat (assignment c) [5,680] := by
    cases ha0 : v2 c <;> simp [ClauseSat, litVal, assignment_2, assignment_340, v340, ha0]
  have hc1896 : ClauseSat (assignment c) [4,680] := by
    cases ha0 : v2 c <;> simp [ClauseSat, litVal, assignment_2, assignment_340, v340, ha0]
  have hc1897 : ClauseSat (assignment c) [4,680] := by
    cases ha0 : v2 c <;> simp [ClauseSat, litVal, assignment_2, assignment_340, v340, ha0]
  have hc1898 : ClauseSat (assignment c) [37,682] := by
    by_cases hs : c.a1.val = 0
    · simp [ClauseSat, litVal, assignment_18, assignment_341, v341, v18, hs]
    · simp [ClauseSat, litVal, assignment_18, assignment_341, v18, hs]
  have hc1899 : ClauseSat (assignment c) [39,682] := by
    by_cases hs : c.a1.val = 1
    · simp [ClauseSat, litVal, assignment_19, assignment_341, v341, v19, hs]
    · simp [ClauseSat, litVal, assignment_19, assignment_341, v19, hs]
  simp only [chunk18, List.forall_mem_cons]
  exact ⟨hc1800, hc1801, hc1802, hc1803, hc1804, hc1805, hc1806, hc1807, hc1808, hc1809, hc1810, hc1811, hc1812, hc1813, hc1814, hc1815, hc1816, hc1817, hc1818, hc1819, hc1820, hc1821, hc1822, hc1823, hc1824, hc1825, hc1826, hc1827, hc1828, hc1829, hc1830, hc1831, hc1832, hc1833, hc1834, hc1835, hc1836, hc1837, hc1838, hc1839, hc1840, hc1841, hc1842, hc1843, hc1844, hc1845, hc1846, hc1847, hc1848, hc1849, hc1850, hc1851, hc1852, hc1853, hc1854, hc1855, hc1856, hc1857, hc1858, hc1859, hc1860, hc1861, hc1862, hc1863, hc1864, hc1865, hc1866, hc1867, hc1868, hc1869, hc1870, hc1871, hc1872, hc1873, hc1874, hc1875, hc1876, hc1877, hc1878, hc1879, hc1880, hc1881, hc1882, hc1883, hc1884, hc1885, hc1886, hc1887, hc1888, hc1889, hc1890, hc1891, hc1892, hc1893, hc1894, hc1895, hc1896, hc1897, hc1898, hc1899, by simp⟩
#check satChunk18

def chunk19 : List (List Nat) := [[41, 682], [43, 682], [45, 683, 680], [45, 682, 681], [47, 684], [49, 684], [51, 684], [53, 684], [55, 685, 680], [55, 684, 681], [35, 687, 682], [35, 687, 684], [35, 686, 683, 685], [34, 686, 683], [34, 686, 685], [34, 687, 682, 684], [75, 688], [77, 688], [79, 688], [81, 688], [83, 689, 680], [83, 688, 681], [85, 689, 686], [85, 688, 687], [87, 690], [89, 690], [91, 690], [93, 690], [95, 691, 680], [95, 690, 681], [97, 691, 686], [97, 690, 687], [73, 693, 688], [73, 693, 690], [73, 692, 689, 691], [72, 692, 689], [72, 692, 691], [72, 693, 688, 690], [121, 694], [123, 694], [125, 694], [127, 694], [129, 695, 680], [129, 694, 681], [131, 695, 686], [131, 694, 687], [133, 695, 692], [133, 694, 693], [135, 696], [137, 696], [139, 696], [141, 696], [143, 697, 680], [143, 696, 681], [145, 697, 686], [145, 696, 687], [147, 697, 692], [147, 696, 693], [119, 699, 694], [119, 699, 696], [119, 698, 695, 697], [118, 698, 695], [118, 698, 697], [118, 699, 694, 696], [175, 700], [177, 700], [179, 700], [181, 700], [183, 701, 680], [183, 700, 681], [185, 701, 686], [185, 700, 687], [187, 701, 692], [187, 700, 693], [189, 701, 698], [189, 700, 699], [191, 702], [193, 702], [195, 702], [197, 702], [199, 703, 680], [199, 702, 681], [201, 703, 686], [201, 702, 687], [203, 703, 692], [203, 702, 693], [205, 703, 698], [205, 702, 699], [173, 705, 700], [173, 705, 702], [173, 704, 701, 703], [172, 704, 701], [172, 704, 703], [172, 705, 700, 702], [704], [7, 706], [9, 707], [11, 707], [13, 707], [15, 708]]
theorem satChunk19 (c : Candidate) (hv : valid c)
    (hr : ∀ r : Fin 16, output c r = target r)
    (hl : derivativeLeft c = false) (hd : derivativeRight c = false) :
    ∀ cl ∈ chunk19, ClauseSat (assignment c) cl := by
  rcases hv with ⟨h0, h1, h2, h3, h4⟩
  have hc1900 : ClauseSat (assignment c) [41,682] := by
    by_cases hs : c.a1.val = 2
    · simp [ClauseSat, litVal, assignment_20, assignment_341, v341, v20, hs]
    · simp [ClauseSat, litVal, assignment_20, assignment_341, v20, hs]
  have hc1901 : ClauseSat (assignment c) [43,682] := by
    by_cases hs : c.a1.val = 3
    · simp [ClauseSat, litVal, assignment_21, assignment_341, v341, v21, hs]
    · simp [ClauseSat, litVal, assignment_21, assignment_341, v21, hs]
  have hc1902 : ClauseSat (assignment c) [45,683,680] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_340, assignment_341, v341, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_340, assignment_341, v22, hs]
  have hc1903 : ClauseSat (assignment c) [45,682,681] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_340, assignment_341, v341, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_340, assignment_341, v22, hs]
  have hc1904 : ClauseSat (assignment c) [47,684] := by
    by_cases hs : c.b1.val = 0
    · simp [ClauseSat, litVal, assignment_23, assignment_342, v342, v23, hs]
    · simp [ClauseSat, litVal, assignment_23, assignment_342, v23, hs]
  have hc1905 : ClauseSat (assignment c) [49,684] := by
    by_cases hs : c.b1.val = 1
    · simp [ClauseSat, litVal, assignment_24, assignment_342, v342, v24, hs]
    · simp [ClauseSat, litVal, assignment_24, assignment_342, v24, hs]
  have hc1906 : ClauseSat (assignment c) [51,684] := by
    by_cases hs : c.b1.val = 2
    · simp [ClauseSat, litVal, assignment_25, assignment_342, v342, v25, hs]
    · simp [ClauseSat, litVal, assignment_25, assignment_342, v25, hs]
  have hc1907 : ClauseSat (assignment c) [53,684] := by
    by_cases hs : c.b1.val = 3
    · simp [ClauseSat, litVal, assignment_26, assignment_342, v342, v26, hs]
    · simp [ClauseSat, litVal, assignment_26, assignment_342, v26, hs]
  have hc1908 : ClauseSat (assignment c) [55,685,680] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_340, assignment_342, v342, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_340, assignment_342, v27, hs]
  have hc1909 : ClauseSat (assignment c) [55,684,681] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_340, assignment_342, v342, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_340, assignment_342, v27, hs]
  have hc1910 : ClauseSat (assignment c) [35,687,682] := by
    cases ha0 : v17 c <;> cases ha1 : v341 c <;> cases ha2 : v342 c <;> simp [ClauseSat, litVal, assignment_17, assignment_341, assignment_343, v343, ha0, ha1, ha2]
  have hc1911 : ClauseSat (assignment c) [35,687,684] := by
    cases ha0 : v17 c <;> cases ha1 : v341 c <;> cases ha2 : v342 c <;> simp [ClauseSat, litVal, assignment_17, assignment_342, assignment_343, v343, ha0, ha1, ha2]
  have hc1912 : ClauseSat (assignment c) [35,686,683,685] := by
    cases ha0 : v17 c <;> cases ha1 : v341 c <;> cases ha2 : v342 c <;> simp [ClauseSat, litVal, assignment_17, assignment_341, assignment_342, assignment_343, v343, ha0, ha1, ha2]
  have hc1913 : ClauseSat (assignment c) [34,686,683] := by
    cases ha0 : v17 c <;> cases ha1 : v341 c <;> cases ha2 : v342 c <;> simp [ClauseSat, litVal, assignment_17, assignment_341, assignment_343, v343, ha0, ha1, ha2]
  have hc1914 : ClauseSat (assignment c) [34,686,685] := by
    cases ha0 : v17 c <;> cases ha1 : v341 c <;> cases ha2 : v342 c <;> simp [ClauseSat, litVal, assignment_17, assignment_342, assignment_343, v343, ha0, ha1, ha2]
  have hc1915 : ClauseSat (assignment c) [34,687,682,684] := by
    cases ha0 : v17 c <;> cases ha1 : v341 c <;> cases ha2 : v342 c <;> simp [ClauseSat, litVal, assignment_17, assignment_341, assignment_342, assignment_343, v343, ha0, ha1, ha2]
  have hc1916 : ClauseSat (assignment c) [75,688] := by
    by_cases hs : c.a2.val = 0
    · simp [ClauseSat, litVal, assignment_37, assignment_344, v344, v37, hs]
    · simp [ClauseSat, litVal, assignment_37, assignment_344, v37, hs]
  have hc1917 : ClauseSat (assignment c) [77,688] := by
    by_cases hs : c.a2.val = 1
    · simp [ClauseSat, litVal, assignment_38, assignment_344, v344, v38, hs]
    · simp [ClauseSat, litVal, assignment_38, assignment_344, v38, hs]
  have hc1918 : ClauseSat (assignment c) [79,688] := by
    by_cases hs : c.a2.val = 2
    · simp [ClauseSat, litVal, assignment_39, assignment_344, v344, v39, hs]
    · simp [ClauseSat, litVal, assignment_39, assignment_344, v39, hs]
  have hc1919 : ClauseSat (assignment c) [81,688] := by
    by_cases hs : c.a2.val = 3
    · simp [ClauseSat, litVal, assignment_40, assignment_344, v344, v40, hs]
    · simp [ClauseSat, litVal, assignment_40, assignment_344, v40, hs]
  have hc1920 : ClauseSat (assignment c) [83,689,680] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_340, assignment_344, v344, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_340, assignment_344, v41, hs]
  have hc1921 : ClauseSat (assignment c) [83,688,681] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_340, assignment_344, v344, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_340, assignment_344, v41, hs]
  have hc1922 : ClauseSat (assignment c) [85,689,686] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_343, assignment_344, v344, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_343, assignment_344, v42, hs]
  have hc1923 : ClauseSat (assignment c) [85,688,687] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_343, assignment_344, v344, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_343, assignment_344, v42, hs]
  have hc1924 : ClauseSat (assignment c) [87,690] := by
    by_cases hs : c.b2.val = 0
    · simp [ClauseSat, litVal, assignment_43, assignment_345, v345, v43, hs]
    · simp [ClauseSat, litVal, assignment_43, assignment_345, v43, hs]
  have hc1925 : ClauseSat (assignment c) [89,690] := by
    by_cases hs : c.b2.val = 1
    · simp [ClauseSat, litVal, assignment_44, assignment_345, v345, v44, hs]
    · simp [ClauseSat, litVal, assignment_44, assignment_345, v44, hs]
  have hc1926 : ClauseSat (assignment c) [91,690] := by
    by_cases hs : c.b2.val = 2
    · simp [ClauseSat, litVal, assignment_45, assignment_345, v345, v45, hs]
    · simp [ClauseSat, litVal, assignment_45, assignment_345, v45, hs]
  have hc1927 : ClauseSat (assignment c) [93,690] := by
    by_cases hs : c.b2.val = 3
    · simp [ClauseSat, litVal, assignment_46, assignment_345, v345, v46, hs]
    · simp [ClauseSat, litVal, assignment_46, assignment_345, v46, hs]
  have hc1928 : ClauseSat (assignment c) [95,691,680] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_340, assignment_345, v345, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_340, assignment_345, v47, hs]
  have hc1929 : ClauseSat (assignment c) [95,690,681] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_340, assignment_345, v345, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_340, assignment_345, v47, hs]
  have hc1930 : ClauseSat (assignment c) [97,691,686] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_343, assignment_345, v345, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_343, assignment_345, v48, hs]
  have hc1931 : ClauseSat (assignment c) [97,690,687] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_343, assignment_345, v345, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_343, assignment_345, v48, hs]
  have hc1932 : ClauseSat (assignment c) [73,693,688] := by
    cases ha0 : v36 c <;> cases ha1 : v344 c <;> cases ha2 : v345 c <;> simp [ClauseSat, litVal, assignment_36, assignment_344, assignment_346, v346, ha0, ha1, ha2]
  have hc1933 : ClauseSat (assignment c) [73,693,690] := by
    cases ha0 : v36 c <;> cases ha1 : v344 c <;> cases ha2 : v345 c <;> simp [ClauseSat, litVal, assignment_36, assignment_345, assignment_346, v346, ha0, ha1, ha2]
  have hc1934 : ClauseSat (assignment c) [73,692,689,691] := by
    cases ha0 : v36 c <;> cases ha1 : v344 c <;> cases ha2 : v345 c <;> simp [ClauseSat, litVal, assignment_36, assignment_344, assignment_345, assignment_346, v346, ha0, ha1, ha2]
  have hc1935 : ClauseSat (assignment c) [72,692,689] := by
    cases ha0 : v36 c <;> cases ha1 : v344 c <;> cases ha2 : v345 c <;> simp [ClauseSat, litVal, assignment_36, assignment_344, assignment_346, v346, ha0, ha1, ha2]
  have hc1936 : ClauseSat (assignment c) [72,692,691] := by
    cases ha0 : v36 c <;> cases ha1 : v344 c <;> cases ha2 : v345 c <;> simp [ClauseSat, litVal, assignment_36, assignment_345, assignment_346, v346, ha0, ha1, ha2]
  have hc1937 : ClauseSat (assignment c) [72,693,688,690] := by
    cases ha0 : v36 c <;> cases ha1 : v344 c <;> cases ha2 : v345 c <;> simp [ClauseSat, litVal, assignment_36, assignment_344, assignment_345, assignment_346, v346, ha0, ha1, ha2]
  have hc1938 : ClauseSat (assignment c) [121,694] := by
    by_cases hs : c.a3.val = 0
    · simp [ClauseSat, litVal, assignment_60, assignment_347, v347, v60, hs]
    · simp [ClauseSat, litVal, assignment_60, assignment_347, v60, hs]
  have hc1939 : ClauseSat (assignment c) [123,694] := by
    by_cases hs : c.a3.val = 1
    · simp [ClauseSat, litVal, assignment_61, assignment_347, v347, v61, hs]
    · simp [ClauseSat, litVal, assignment_61, assignment_347, v61, hs]
  have hc1940 : ClauseSat (assignment c) [125,694] := by
    by_cases hs : c.a3.val = 2
    · simp [ClauseSat, litVal, assignment_62, assignment_347, v347, v62, hs]
    · simp [ClauseSat, litVal, assignment_62, assignment_347, v62, hs]
  have hc1941 : ClauseSat (assignment c) [127,694] := by
    by_cases hs : c.a3.val = 3
    · simp [ClauseSat, litVal, assignment_63, assignment_347, v347, v63, hs]
    · simp [ClauseSat, litVal, assignment_63, assignment_347, v63, hs]
  have hc1942 : ClauseSat (assignment c) [129,695,680] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_340, assignment_347, v347, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_340, assignment_347, v64, hs]
  have hc1943 : ClauseSat (assignment c) [129,694,681] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_340, assignment_347, v347, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_340, assignment_347, v64, hs]
  have hc1944 : ClauseSat (assignment c) [131,695,686] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_343, assignment_347, v347, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_343, assignment_347, v65, hs]
  have hc1945 : ClauseSat (assignment c) [131,694,687] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_343, assignment_347, v347, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_343, assignment_347, v65, hs]
  have hc1946 : ClauseSat (assignment c) [133,695,692] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_346, assignment_347, v347, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_346, assignment_347, v66, hs]
  have hc1947 : ClauseSat (assignment c) [133,694,693] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_346, assignment_347, v347, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_346, assignment_347, v66, hs]
  have hc1948 : ClauseSat (assignment c) [135,696] := by
    by_cases hs : c.b3.val = 0
    · simp [ClauseSat, litVal, assignment_67, assignment_348, v348, v67, hs]
    · simp [ClauseSat, litVal, assignment_67, assignment_348, v67, hs]
  have hc1949 : ClauseSat (assignment c) [137,696] := by
    by_cases hs : c.b3.val = 1
    · simp [ClauseSat, litVal, assignment_68, assignment_348, v348, v68, hs]
    · simp [ClauseSat, litVal, assignment_68, assignment_348, v68, hs]
  have hc1950 : ClauseSat (assignment c) [139,696] := by
    by_cases hs : c.b3.val = 2
    · simp [ClauseSat, litVal, assignment_69, assignment_348, v348, v69, hs]
    · simp [ClauseSat, litVal, assignment_69, assignment_348, v69, hs]
  have hc1951 : ClauseSat (assignment c) [141,696] := by
    by_cases hs : c.b3.val = 3
    · simp [ClauseSat, litVal, assignment_70, assignment_348, v348, v70, hs]
    · simp [ClauseSat, litVal, assignment_70, assignment_348, v70, hs]
  have hc1952 : ClauseSat (assignment c) [143,697,680] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_340, assignment_348, v348, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_340, assignment_348, v71, hs]
  have hc1953 : ClauseSat (assignment c) [143,696,681] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_340, assignment_348, v348, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_340, assignment_348, v71, hs]
  have hc1954 : ClauseSat (assignment c) [145,697,686] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_343, assignment_348, v348, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_343, assignment_348, v72, hs]
  have hc1955 : ClauseSat (assignment c) [145,696,687] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_343, assignment_348, v348, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_343, assignment_348, v72, hs]
  have hc1956 : ClauseSat (assignment c) [147,697,692] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_346, assignment_348, v348, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_346, assignment_348, v73, hs]
  have hc1957 : ClauseSat (assignment c) [147,696,693] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_346, assignment_348, v348, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_346, assignment_348, v73, hs]
  have hc1958 : ClauseSat (assignment c) [119,699,694] := by
    cases ha0 : v59 c <;> cases ha1 : v347 c <;> cases ha2 : v348 c <;> simp [ClauseSat, litVal, assignment_59, assignment_347, assignment_349, v349, ha0, ha1, ha2]
  have hc1959 : ClauseSat (assignment c) [119,699,696] := by
    cases ha0 : v59 c <;> cases ha1 : v347 c <;> cases ha2 : v348 c <;> simp [ClauseSat, litVal, assignment_59, assignment_348, assignment_349, v349, ha0, ha1, ha2]
  have hc1960 : ClauseSat (assignment c) [119,698,695,697] := by
    cases ha0 : v59 c <;> cases ha1 : v347 c <;> cases ha2 : v348 c <;> simp [ClauseSat, litVal, assignment_59, assignment_347, assignment_348, assignment_349, v349, ha0, ha1, ha2]
  have hc1961 : ClauseSat (assignment c) [118,698,695] := by
    cases ha0 : v59 c <;> cases ha1 : v347 c <;> cases ha2 : v348 c <;> simp [ClauseSat, litVal, assignment_59, assignment_347, assignment_349, v349, ha0, ha1, ha2]
  have hc1962 : ClauseSat (assignment c) [118,698,697] := by
    cases ha0 : v59 c <;> cases ha1 : v347 c <;> cases ha2 : v348 c <;> simp [ClauseSat, litVal, assignment_59, assignment_348, assignment_349, v349, ha0, ha1, ha2]
  have hc1963 : ClauseSat (assignment c) [118,699,694,696] := by
    cases ha0 : v59 c <;> cases ha1 : v347 c <;> cases ha2 : v348 c <;> simp [ClauseSat, litVal, assignment_59, assignment_347, assignment_348, assignment_349, v349, ha0, ha1, ha2]
  have hc1964 : ClauseSat (assignment c) [175,700] := by
    by_cases hs : c.a4.val = 0
    · simp [ClauseSat, litVal, assignment_87, assignment_350, v350, v87, hs]
    · simp [ClauseSat, litVal, assignment_87, assignment_350, v87, hs]
  have hc1965 : ClauseSat (assignment c) [177,700] := by
    by_cases hs : c.a4.val = 1
    · simp [ClauseSat, litVal, assignment_88, assignment_350, v350, v88, hs]
    · simp [ClauseSat, litVal, assignment_88, assignment_350, v88, hs]
  have hc1966 : ClauseSat (assignment c) [179,700] := by
    by_cases hs : c.a4.val = 2
    · simp [ClauseSat, litVal, assignment_89, assignment_350, v350, v89, hs]
    · simp [ClauseSat, litVal, assignment_89, assignment_350, v89, hs]
  have hc1967 : ClauseSat (assignment c) [181,700] := by
    by_cases hs : c.a4.val = 3
    · simp [ClauseSat, litVal, assignment_90, assignment_350, v350, v90, hs]
    · simp [ClauseSat, litVal, assignment_90, assignment_350, v90, hs]
  have hc1968 : ClauseSat (assignment c) [183,701,680] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_340, assignment_350, v350, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_340, assignment_350, v91, hs]
  have hc1969 : ClauseSat (assignment c) [183,700,681] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_340, assignment_350, v350, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_340, assignment_350, v91, hs]
  have hc1970 : ClauseSat (assignment c) [185,701,686] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_343, assignment_350, v350, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_343, assignment_350, v92, hs]
  have hc1971 : ClauseSat (assignment c) [185,700,687] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_343, assignment_350, v350, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_343, assignment_350, v92, hs]
  have hc1972 : ClauseSat (assignment c) [187,701,692] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_346, assignment_350, v350, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_346, assignment_350, v93, hs]
  have hc1973 : ClauseSat (assignment c) [187,700,693] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_346, assignment_350, v350, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_346, assignment_350, v93, hs]
  have hc1974 : ClauseSat (assignment c) [189,701,698] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_349, assignment_350, v350, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_349, assignment_350, v94, hs]
  have hc1975 : ClauseSat (assignment c) [189,700,699] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_349, assignment_350, v350, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_349, assignment_350, v94, hs]
  have hc1976 : ClauseSat (assignment c) [191,702] := by
    by_cases hs : c.b4.val = 0
    · simp [ClauseSat, litVal, assignment_95, assignment_351, v351, v95, hs]
    · simp [ClauseSat, litVal, assignment_95, assignment_351, v95, hs]
  have hc1977 : ClauseSat (assignment c) [193,702] := by
    by_cases hs : c.b4.val = 1
    · simp [ClauseSat, litVal, assignment_96, assignment_351, v351, v96, hs]
    · simp [ClauseSat, litVal, assignment_96, assignment_351, v96, hs]
  have hc1978 : ClauseSat (assignment c) [195,702] := by
    by_cases hs : c.b4.val = 2
    · simp [ClauseSat, litVal, assignment_97, assignment_351, v351, v97, hs]
    · simp [ClauseSat, litVal, assignment_97, assignment_351, v97, hs]
  have hc1979 : ClauseSat (assignment c) [197,702] := by
    by_cases hs : c.b4.val = 3
    · simp [ClauseSat, litVal, assignment_98, assignment_351, v351, v98, hs]
    · simp [ClauseSat, litVal, assignment_98, assignment_351, v98, hs]
  have hc1980 : ClauseSat (assignment c) [199,703,680] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_340, assignment_351, v351, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_340, assignment_351, v99, hs]
  have hc1981 : ClauseSat (assignment c) [199,702,681] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_340, assignment_351, v351, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_340, assignment_351, v99, hs]
  have hc1982 : ClauseSat (assignment c) [201,703,686] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_343, assignment_351, v351, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_343, assignment_351, v100, hs]
  have hc1983 : ClauseSat (assignment c) [201,702,687] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_343, assignment_351, v351, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_343, assignment_351, v100, hs]
  have hc1984 : ClauseSat (assignment c) [203,703,692] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_346, assignment_351, v351, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_346, assignment_351, v101, hs]
  have hc1985 : ClauseSat (assignment c) [203,702,693] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_346, assignment_351, v351, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_346, assignment_351, v101, hs]
  have hc1986 : ClauseSat (assignment c) [205,703,698] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_349, assignment_351, v351, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_349, assignment_351, v102, hs]
  have hc1987 : ClauseSat (assignment c) [205,702,699] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_349, assignment_351, v351, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_349, assignment_351, v102, hs]
  have hc1988 : ClauseSat (assignment c) [173,705,700] := by
    cases ha0 : v86 c <;> cases ha1 : v350 c <;> cases ha2 : v351 c <;> simp [ClauseSat, litVal, assignment_86, assignment_350, assignment_352, v352, ha0, ha1, ha2]
  have hc1989 : ClauseSat (assignment c) [173,705,702] := by
    cases ha0 : v86 c <;> cases ha1 : v350 c <;> cases ha2 : v351 c <;> simp [ClauseSat, litVal, assignment_86, assignment_351, assignment_352, v352, ha0, ha1, ha2]
  have hc1990 : ClauseSat (assignment c) [173,704,701,703] := by
    cases ha0 : v86 c <;> cases ha1 : v350 c <;> cases ha2 : v351 c <;> simp [ClauseSat, litVal, assignment_86, assignment_350, assignment_351, assignment_352, v352, ha0, ha1, ha2]
  have hc1991 : ClauseSat (assignment c) [172,704,701] := by
    cases ha0 : v86 c <;> cases ha1 : v350 c <;> cases ha2 : v351 c <;> simp [ClauseSat, litVal, assignment_86, assignment_350, assignment_352, v352, ha0, ha1, ha2]
  have hc1992 : ClauseSat (assignment c) [172,704,703] := by
    cases ha0 : v86 c <;> cases ha1 : v350 c <;> cases ha2 : v351 c <;> simp [ClauseSat, litVal, assignment_86, assignment_351, assignment_352, v352, ha0, ha1, ha2]
  have hc1993 : ClauseSat (assignment c) [172,705,700,702] := by
    cases ha0 : v86 c <;> cases ha1 : v350 c <;> cases ha2 : v351 c <;> simp [ClauseSat, litVal, assignment_86, assignment_350, assignment_351, assignment_352, v352, ha0, ha1, ha2]
  have hc1994 : ClauseSat (assignment c) [704] := by
    have hh := hr ⟨15, by decide⟩
    have ht : target ⟨15, by decide⟩ = true := by decide
    rw [ht] at hh
    simpa [ClauseSat, litVal, assignment_352, output] using hh
  have hc1995 : ClauseSat (assignment c) [7,706] := by
    by_cases hs : c.a0.val = 0
    · simp [ClauseSat, litVal, assignment_3, assignment_353, v353, v3, hs]
    · simp [ClauseSat, litVal, assignment_3, assignment_353, v3, hs]
  have hc1996 : ClauseSat (assignment c) [9,707] := by
    by_cases hs : c.a0.val = 1
    · simp [ClauseSat, litVal, assignment_4, assignment_353, v353, v4, hs]
    · simp [ClauseSat, litVal, assignment_4, assignment_353, v4, hs]
  have hc1997 : ClauseSat (assignment c) [11,707] := by
    by_cases hs : c.a0.val = 2
    · simp [ClauseSat, litVal, assignment_5, assignment_353, v353, v5, hs]
    · simp [ClauseSat, litVal, assignment_5, assignment_353, v5, hs]
  have hc1998 : ClauseSat (assignment c) [13,707] := by
    by_cases hs : c.a0.val = 3
    · simp [ClauseSat, litVal, assignment_6, assignment_353, v353, v6, hs]
    · simp [ClauseSat, litVal, assignment_6, assignment_353, v6, hs]
  have hc1999 : ClauseSat (assignment c) [15,708] := by
    by_cases hs : c.b0.val = 0
    · simp [ClauseSat, litVal, assignment_7, assignment_354, v354, v7, hs]
    · simp [ClauseSat, litVal, assignment_7, assignment_354, v7, hs]
  simp only [chunk19, List.forall_mem_cons]
  exact ⟨hc1900, hc1901, hc1902, hc1903, hc1904, hc1905, hc1906, hc1907, hc1908, hc1909, hc1910, hc1911, hc1912, hc1913, hc1914, hc1915, hc1916, hc1917, hc1918, hc1919, hc1920, hc1921, hc1922, hc1923, hc1924, hc1925, hc1926, hc1927, hc1928, hc1929, hc1930, hc1931, hc1932, hc1933, hc1934, hc1935, hc1936, hc1937, hc1938, hc1939, hc1940, hc1941, hc1942, hc1943, hc1944, hc1945, hc1946, hc1947, hc1948, hc1949, hc1950, hc1951, hc1952, hc1953, hc1954, hc1955, hc1956, hc1957, hc1958, hc1959, hc1960, hc1961, hc1962, hc1963, hc1964, hc1965, hc1966, hc1967, hc1968, hc1969, hc1970, hc1971, hc1972, hc1973, hc1974, hc1975, hc1976, hc1977, hc1978, hc1979, hc1980, hc1981, hc1982, hc1983, hc1984, hc1985, hc1986, hc1987, hc1988, hc1989, hc1990, hc1991, hc1992, hc1993, hc1994, hc1995, hc1996, hc1997, hc1998, hc1999, by simp⟩
#check satChunk19

def chunk20 : List (List Nat) := [[17, 709], [19, 709], [21, 709], [5, 711, 706], [5, 711, 708], [5, 710, 707, 709], [4, 710, 707], [4, 710, 709], [4, 711, 706, 708], [37, 712], [39, 713], [41, 713], [43, 713], [45, 713, 710], [45, 712, 711], [47, 714], [49, 715], [51, 715], [53, 715], [55, 715, 710], [55, 714, 711], [35, 717, 712], [35, 717, 714], [35, 716, 713, 715], [34, 716, 713], [34, 716, 715], [34, 717, 712, 714], [75, 718], [77, 719], [79, 719], [81, 719], [83, 719, 710], [83, 718, 711], [85, 719, 716], [85, 718, 717], [87, 720], [89, 721], [91, 721], [93, 721], [95, 721, 710], [95, 720, 711], [97, 721, 716], [97, 720, 717], [73, 723, 718], [73, 723, 720], [73, 722, 719, 721], [72, 722, 719], [72, 722, 721], [72, 723, 718, 720], [121, 724], [123, 725], [125, 725], [127, 725], [129, 725, 710], [129, 724, 711], [131, 725, 716], [131, 724, 717], [133, 725, 722], [133, 724, 723], [135, 726], [137, 727], [139, 727], [141, 727], [143, 727, 710], [143, 726, 711], [145, 727, 716], [145, 726, 717], [147, 727, 722], [147, 726, 723], [119, 729, 724], [119, 729, 726], [119, 728, 725, 727], [118, 728, 725], [118, 728, 727], [118, 729, 724, 726], [175, 730], [177, 731], [179, 731], [181, 731], [183, 731, 710], [183, 730, 711], [185, 731, 716], [185, 730, 717], [187, 731, 722], [187, 730, 723], [189, 731, 728], [189, 730, 729], [191, 732], [193, 733], [195, 733], [197, 733], [199, 733, 710], [199, 732, 711], [201, 733, 716], [201, 732, 717], [203, 733, 722], [203, 732, 723], [205, 733, 728], [205, 732, 729], [173, 735, 730]]
theorem satChunk20 (c : Candidate) (hv : valid c)
    (hr : ∀ r : Fin 16, output c r = target r)
    (hl : derivativeLeft c = false) (hd : derivativeRight c = false) :
    ∀ cl ∈ chunk20, ClauseSat (assignment c) cl := by
  rcases hv with ⟨h0, h1, h2, h3, h4⟩
  have hc2000 : ClauseSat (assignment c) [17,709] := by
    by_cases hs : c.b0.val = 1
    · simp [ClauseSat, litVal, assignment_8, assignment_354, v354, v8, hs]
    · simp [ClauseSat, litVal, assignment_8, assignment_354, v8, hs]
  have hc2001 : ClauseSat (assignment c) [19,709] := by
    by_cases hs : c.b0.val = 2
    · simp [ClauseSat, litVal, assignment_9, assignment_354, v354, v9, hs]
    · simp [ClauseSat, litVal, assignment_9, assignment_354, v9, hs]
  have hc2002 : ClauseSat (assignment c) [21,709] := by
    by_cases hs : c.b0.val = 3
    · simp [ClauseSat, litVal, assignment_10, assignment_354, v354, v10, hs]
    · simp [ClauseSat, litVal, assignment_10, assignment_354, v10, hs]
  have hc2003 : ClauseSat (assignment c) [5,711,706] := by
    cases ha0 : v2 c <;> cases ha1 : v353 c <;> cases ha2 : v354 c <;> simp [ClauseSat, litVal, assignment_2, assignment_353, assignment_355, v355, ha0, ha1, ha2]
  have hc2004 : ClauseSat (assignment c) [5,711,708] := by
    cases ha0 : v2 c <;> cases ha1 : v353 c <;> cases ha2 : v354 c <;> simp [ClauseSat, litVal, assignment_2, assignment_354, assignment_355, v355, ha0, ha1, ha2]
  have hc2005 : ClauseSat (assignment c) [5,710,707,709] := by
    cases ha0 : v2 c <;> cases ha1 : v353 c <;> cases ha2 : v354 c <;> simp [ClauseSat, litVal, assignment_2, assignment_353, assignment_354, assignment_355, v355, ha0, ha1, ha2]
  have hc2006 : ClauseSat (assignment c) [4,710,707] := by
    cases ha0 : v2 c <;> cases ha1 : v353 c <;> cases ha2 : v354 c <;> simp [ClauseSat, litVal, assignment_2, assignment_353, assignment_355, v355, ha0, ha1, ha2]
  have hc2007 : ClauseSat (assignment c) [4,710,709] := by
    cases ha0 : v2 c <;> cases ha1 : v353 c <;> cases ha2 : v354 c <;> simp [ClauseSat, litVal, assignment_2, assignment_354, assignment_355, v355, ha0, ha1, ha2]
  have hc2008 : ClauseSat (assignment c) [4,711,706,708] := by
    cases ha0 : v2 c <;> cases ha1 : v353 c <;> cases ha2 : v354 c <;> simp [ClauseSat, litVal, assignment_2, assignment_353, assignment_354, assignment_355, v355, ha0, ha1, ha2]
  have hc2009 : ClauseSat (assignment c) [37,712] := by
    by_cases hs : c.a1.val = 0
    · simp [ClauseSat, litVal, assignment_18, assignment_356, v356, v18, hs]
    · simp [ClauseSat, litVal, assignment_18, assignment_356, v18, hs]
  have hc2010 : ClauseSat (assignment c) [39,713] := by
    by_cases hs : c.a1.val = 1
    · simp [ClauseSat, litVal, assignment_19, assignment_356, v356, v19, hs]
    · simp [ClauseSat, litVal, assignment_19, assignment_356, v19, hs]
  have hc2011 : ClauseSat (assignment c) [41,713] := by
    by_cases hs : c.a1.val = 2
    · simp [ClauseSat, litVal, assignment_20, assignment_356, v356, v20, hs]
    · simp [ClauseSat, litVal, assignment_20, assignment_356, v20, hs]
  have hc2012 : ClauseSat (assignment c) [43,713] := by
    by_cases hs : c.a1.val = 3
    · simp [ClauseSat, litVal, assignment_21, assignment_356, v356, v21, hs]
    · simp [ClauseSat, litVal, assignment_21, assignment_356, v21, hs]
  have hc2013 : ClauseSat (assignment c) [45,713,710] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_355, assignment_356, v356, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_355, assignment_356, v22, hs]
  have hc2014 : ClauseSat (assignment c) [45,712,711] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_355, assignment_356, v356, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_355, assignment_356, v22, hs]
  have hc2015 : ClauseSat (assignment c) [47,714] := by
    by_cases hs : c.b1.val = 0
    · simp [ClauseSat, litVal, assignment_23, assignment_357, v357, v23, hs]
    · simp [ClauseSat, litVal, assignment_23, assignment_357, v23, hs]
  have hc2016 : ClauseSat (assignment c) [49,715] := by
    by_cases hs : c.b1.val = 1
    · simp [ClauseSat, litVal, assignment_24, assignment_357, v357, v24, hs]
    · simp [ClauseSat, litVal, assignment_24, assignment_357, v24, hs]
  have hc2017 : ClauseSat (assignment c) [51,715] := by
    by_cases hs : c.b1.val = 2
    · simp [ClauseSat, litVal, assignment_25, assignment_357, v357, v25, hs]
    · simp [ClauseSat, litVal, assignment_25, assignment_357, v25, hs]
  have hc2018 : ClauseSat (assignment c) [53,715] := by
    by_cases hs : c.b1.val = 3
    · simp [ClauseSat, litVal, assignment_26, assignment_357, v357, v26, hs]
    · simp [ClauseSat, litVal, assignment_26, assignment_357, v26, hs]
  have hc2019 : ClauseSat (assignment c) [55,715,710] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_355, assignment_357, v357, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_355, assignment_357, v27, hs]
  have hc2020 : ClauseSat (assignment c) [55,714,711] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_355, assignment_357, v357, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_355, assignment_357, v27, hs]
  have hc2021 : ClauseSat (assignment c) [35,717,712] := by
    cases ha0 : v17 c <;> cases ha1 : v356 c <;> cases ha2 : v357 c <;> simp [ClauseSat, litVal, assignment_17, assignment_356, assignment_358, v358, ha0, ha1, ha2]
  have hc2022 : ClauseSat (assignment c) [35,717,714] := by
    cases ha0 : v17 c <;> cases ha1 : v356 c <;> cases ha2 : v357 c <;> simp [ClauseSat, litVal, assignment_17, assignment_357, assignment_358, v358, ha0, ha1, ha2]
  have hc2023 : ClauseSat (assignment c) [35,716,713,715] := by
    cases ha0 : v17 c <;> cases ha1 : v356 c <;> cases ha2 : v357 c <;> simp [ClauseSat, litVal, assignment_17, assignment_356, assignment_357, assignment_358, v358, ha0, ha1, ha2]
  have hc2024 : ClauseSat (assignment c) [34,716,713] := by
    cases ha0 : v17 c <;> cases ha1 : v356 c <;> cases ha2 : v357 c <;> simp [ClauseSat, litVal, assignment_17, assignment_356, assignment_358, v358, ha0, ha1, ha2]
  have hc2025 : ClauseSat (assignment c) [34,716,715] := by
    cases ha0 : v17 c <;> cases ha1 : v356 c <;> cases ha2 : v357 c <;> simp [ClauseSat, litVal, assignment_17, assignment_357, assignment_358, v358, ha0, ha1, ha2]
  have hc2026 : ClauseSat (assignment c) [34,717,712,714] := by
    cases ha0 : v17 c <;> cases ha1 : v356 c <;> cases ha2 : v357 c <;> simp [ClauseSat, litVal, assignment_17, assignment_356, assignment_357, assignment_358, v358, ha0, ha1, ha2]
  have hc2027 : ClauseSat (assignment c) [75,718] := by
    by_cases hs : c.a2.val = 0
    · simp [ClauseSat, litVal, assignment_37, assignment_359, v359, v37, hs]
    · simp [ClauseSat, litVal, assignment_37, assignment_359, v37, hs]
  have hc2028 : ClauseSat (assignment c) [77,719] := by
    by_cases hs : c.a2.val = 1
    · simp [ClauseSat, litVal, assignment_38, assignment_359, v359, v38, hs]
    · simp [ClauseSat, litVal, assignment_38, assignment_359, v38, hs]
  have hc2029 : ClauseSat (assignment c) [79,719] := by
    by_cases hs : c.a2.val = 2
    · simp [ClauseSat, litVal, assignment_39, assignment_359, v359, v39, hs]
    · simp [ClauseSat, litVal, assignment_39, assignment_359, v39, hs]
  have hc2030 : ClauseSat (assignment c) [81,719] := by
    by_cases hs : c.a2.val = 3
    · simp [ClauseSat, litVal, assignment_40, assignment_359, v359, v40, hs]
    · simp [ClauseSat, litVal, assignment_40, assignment_359, v40, hs]
  have hc2031 : ClauseSat (assignment c) [83,719,710] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_355, assignment_359, v359, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_355, assignment_359, v41, hs]
  have hc2032 : ClauseSat (assignment c) [83,718,711] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_355, assignment_359, v359, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_355, assignment_359, v41, hs]
  have hc2033 : ClauseSat (assignment c) [85,719,716] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_358, assignment_359, v359, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_358, assignment_359, v42, hs]
  have hc2034 : ClauseSat (assignment c) [85,718,717] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_358, assignment_359, v359, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_358, assignment_359, v42, hs]
  have hc2035 : ClauseSat (assignment c) [87,720] := by
    by_cases hs : c.b2.val = 0
    · simp [ClauseSat, litVal, assignment_43, assignment_360, v360, v43, hs]
    · simp [ClauseSat, litVal, assignment_43, assignment_360, v43, hs]
  have hc2036 : ClauseSat (assignment c) [89,721] := by
    by_cases hs : c.b2.val = 1
    · simp [ClauseSat, litVal, assignment_44, assignment_360, v360, v44, hs]
    · simp [ClauseSat, litVal, assignment_44, assignment_360, v44, hs]
  have hc2037 : ClauseSat (assignment c) [91,721] := by
    by_cases hs : c.b2.val = 2
    · simp [ClauseSat, litVal, assignment_45, assignment_360, v360, v45, hs]
    · simp [ClauseSat, litVal, assignment_45, assignment_360, v45, hs]
  have hc2038 : ClauseSat (assignment c) [93,721] := by
    by_cases hs : c.b2.val = 3
    · simp [ClauseSat, litVal, assignment_46, assignment_360, v360, v46, hs]
    · simp [ClauseSat, litVal, assignment_46, assignment_360, v46, hs]
  have hc2039 : ClauseSat (assignment c) [95,721,710] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_355, assignment_360, v360, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_355, assignment_360, v47, hs]
  have hc2040 : ClauseSat (assignment c) [95,720,711] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_355, assignment_360, v360, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_355, assignment_360, v47, hs]
  have hc2041 : ClauseSat (assignment c) [97,721,716] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_358, assignment_360, v360, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_358, assignment_360, v48, hs]
  have hc2042 : ClauseSat (assignment c) [97,720,717] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_358, assignment_360, v360, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_358, assignment_360, v48, hs]
  have hc2043 : ClauseSat (assignment c) [73,723,718] := by
    cases ha0 : v36 c <;> cases ha1 : v359 c <;> cases ha2 : v360 c <;> simp [ClauseSat, litVal, assignment_36, assignment_359, assignment_361, v361, ha0, ha1, ha2]
  have hc2044 : ClauseSat (assignment c) [73,723,720] := by
    cases ha0 : v36 c <;> cases ha1 : v359 c <;> cases ha2 : v360 c <;> simp [ClauseSat, litVal, assignment_36, assignment_360, assignment_361, v361, ha0, ha1, ha2]
  have hc2045 : ClauseSat (assignment c) [73,722,719,721] := by
    cases ha0 : v36 c <;> cases ha1 : v359 c <;> cases ha2 : v360 c <;> simp [ClauseSat, litVal, assignment_36, assignment_359, assignment_360, assignment_361, v361, ha0, ha1, ha2]
  have hc2046 : ClauseSat (assignment c) [72,722,719] := by
    cases ha0 : v36 c <;> cases ha1 : v359 c <;> cases ha2 : v360 c <;> simp [ClauseSat, litVal, assignment_36, assignment_359, assignment_361, v361, ha0, ha1, ha2]
  have hc2047 : ClauseSat (assignment c) [72,722,721] := by
    cases ha0 : v36 c <;> cases ha1 : v359 c <;> cases ha2 : v360 c <;> simp [ClauseSat, litVal, assignment_36, assignment_360, assignment_361, v361, ha0, ha1, ha2]
  have hc2048 : ClauseSat (assignment c) [72,723,718,720] := by
    cases ha0 : v36 c <;> cases ha1 : v359 c <;> cases ha2 : v360 c <;> simp [ClauseSat, litVal, assignment_36, assignment_359, assignment_360, assignment_361, v361, ha0, ha1, ha2]
  have hc2049 : ClauseSat (assignment c) [121,724] := by
    by_cases hs : c.a3.val = 0
    · simp [ClauseSat, litVal, assignment_60, assignment_362, v362, v60, hs]
    · simp [ClauseSat, litVal, assignment_60, assignment_362, v60, hs]
  have hc2050 : ClauseSat (assignment c) [123,725] := by
    by_cases hs : c.a3.val = 1
    · simp [ClauseSat, litVal, assignment_61, assignment_362, v362, v61, hs]
    · simp [ClauseSat, litVal, assignment_61, assignment_362, v61, hs]
  have hc2051 : ClauseSat (assignment c) [125,725] := by
    by_cases hs : c.a3.val = 2
    · simp [ClauseSat, litVal, assignment_62, assignment_362, v362, v62, hs]
    · simp [ClauseSat, litVal, assignment_62, assignment_362, v62, hs]
  have hc2052 : ClauseSat (assignment c) [127,725] := by
    by_cases hs : c.a3.val = 3
    · simp [ClauseSat, litVal, assignment_63, assignment_362, v362, v63, hs]
    · simp [ClauseSat, litVal, assignment_63, assignment_362, v63, hs]
  have hc2053 : ClauseSat (assignment c) [129,725,710] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_355, assignment_362, v362, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_355, assignment_362, v64, hs]
  have hc2054 : ClauseSat (assignment c) [129,724,711] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_355, assignment_362, v362, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_355, assignment_362, v64, hs]
  have hc2055 : ClauseSat (assignment c) [131,725,716] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_358, assignment_362, v362, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_358, assignment_362, v65, hs]
  have hc2056 : ClauseSat (assignment c) [131,724,717] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_358, assignment_362, v362, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_358, assignment_362, v65, hs]
  have hc2057 : ClauseSat (assignment c) [133,725,722] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_361, assignment_362, v362, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_361, assignment_362, v66, hs]
  have hc2058 : ClauseSat (assignment c) [133,724,723] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_361, assignment_362, v362, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_361, assignment_362, v66, hs]
  have hc2059 : ClauseSat (assignment c) [135,726] := by
    by_cases hs : c.b3.val = 0
    · simp [ClauseSat, litVal, assignment_67, assignment_363, v363, v67, hs]
    · simp [ClauseSat, litVal, assignment_67, assignment_363, v67, hs]
  have hc2060 : ClauseSat (assignment c) [137,727] := by
    by_cases hs : c.b3.val = 1
    · simp [ClauseSat, litVal, assignment_68, assignment_363, v363, v68, hs]
    · simp [ClauseSat, litVal, assignment_68, assignment_363, v68, hs]
  have hc2061 : ClauseSat (assignment c) [139,727] := by
    by_cases hs : c.b3.val = 2
    · simp [ClauseSat, litVal, assignment_69, assignment_363, v363, v69, hs]
    · simp [ClauseSat, litVal, assignment_69, assignment_363, v69, hs]
  have hc2062 : ClauseSat (assignment c) [141,727] := by
    by_cases hs : c.b3.val = 3
    · simp [ClauseSat, litVal, assignment_70, assignment_363, v363, v70, hs]
    · simp [ClauseSat, litVal, assignment_70, assignment_363, v70, hs]
  have hc2063 : ClauseSat (assignment c) [143,727,710] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_355, assignment_363, v363, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_355, assignment_363, v71, hs]
  have hc2064 : ClauseSat (assignment c) [143,726,711] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_355, assignment_363, v363, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_355, assignment_363, v71, hs]
  have hc2065 : ClauseSat (assignment c) [145,727,716] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_358, assignment_363, v363, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_358, assignment_363, v72, hs]
  have hc2066 : ClauseSat (assignment c) [145,726,717] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_358, assignment_363, v363, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_358, assignment_363, v72, hs]
  have hc2067 : ClauseSat (assignment c) [147,727,722] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_361, assignment_363, v363, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_361, assignment_363, v73, hs]
  have hc2068 : ClauseSat (assignment c) [147,726,723] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_361, assignment_363, v363, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_361, assignment_363, v73, hs]
  have hc2069 : ClauseSat (assignment c) [119,729,724] := by
    cases ha0 : v59 c <;> cases ha1 : v362 c <;> cases ha2 : v363 c <;> simp [ClauseSat, litVal, assignment_59, assignment_362, assignment_364, v364, ha0, ha1, ha2]
  have hc2070 : ClauseSat (assignment c) [119,729,726] := by
    cases ha0 : v59 c <;> cases ha1 : v362 c <;> cases ha2 : v363 c <;> simp [ClauseSat, litVal, assignment_59, assignment_363, assignment_364, v364, ha0, ha1, ha2]
  have hc2071 : ClauseSat (assignment c) [119,728,725,727] := by
    cases ha0 : v59 c <;> cases ha1 : v362 c <;> cases ha2 : v363 c <;> simp [ClauseSat, litVal, assignment_59, assignment_362, assignment_363, assignment_364, v364, ha0, ha1, ha2]
  have hc2072 : ClauseSat (assignment c) [118,728,725] := by
    cases ha0 : v59 c <;> cases ha1 : v362 c <;> cases ha2 : v363 c <;> simp [ClauseSat, litVal, assignment_59, assignment_362, assignment_364, v364, ha0, ha1, ha2]
  have hc2073 : ClauseSat (assignment c) [118,728,727] := by
    cases ha0 : v59 c <;> cases ha1 : v362 c <;> cases ha2 : v363 c <;> simp [ClauseSat, litVal, assignment_59, assignment_363, assignment_364, v364, ha0, ha1, ha2]
  have hc2074 : ClauseSat (assignment c) [118,729,724,726] := by
    cases ha0 : v59 c <;> cases ha1 : v362 c <;> cases ha2 : v363 c <;> simp [ClauseSat, litVal, assignment_59, assignment_362, assignment_363, assignment_364, v364, ha0, ha1, ha2]
  have hc2075 : ClauseSat (assignment c) [175,730] := by
    by_cases hs : c.a4.val = 0
    · simp [ClauseSat, litVal, assignment_87, assignment_365, v365, v87, hs]
    · simp [ClauseSat, litVal, assignment_87, assignment_365, v87, hs]
  have hc2076 : ClauseSat (assignment c) [177,731] := by
    by_cases hs : c.a4.val = 1
    · simp [ClauseSat, litVal, assignment_88, assignment_365, v365, v88, hs]
    · simp [ClauseSat, litVal, assignment_88, assignment_365, v88, hs]
  have hc2077 : ClauseSat (assignment c) [179,731] := by
    by_cases hs : c.a4.val = 2
    · simp [ClauseSat, litVal, assignment_89, assignment_365, v365, v89, hs]
    · simp [ClauseSat, litVal, assignment_89, assignment_365, v89, hs]
  have hc2078 : ClauseSat (assignment c) [181,731] := by
    by_cases hs : c.a4.val = 3
    · simp [ClauseSat, litVal, assignment_90, assignment_365, v365, v90, hs]
    · simp [ClauseSat, litVal, assignment_90, assignment_365, v90, hs]
  have hc2079 : ClauseSat (assignment c) [183,731,710] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_355, assignment_365, v365, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_355, assignment_365, v91, hs]
  have hc2080 : ClauseSat (assignment c) [183,730,711] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_355, assignment_365, v365, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_355, assignment_365, v91, hs]
  have hc2081 : ClauseSat (assignment c) [185,731,716] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_358, assignment_365, v365, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_358, assignment_365, v92, hs]
  have hc2082 : ClauseSat (assignment c) [185,730,717] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_358, assignment_365, v365, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_358, assignment_365, v92, hs]
  have hc2083 : ClauseSat (assignment c) [187,731,722] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_361, assignment_365, v365, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_361, assignment_365, v93, hs]
  have hc2084 : ClauseSat (assignment c) [187,730,723] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_361, assignment_365, v365, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_361, assignment_365, v93, hs]
  have hc2085 : ClauseSat (assignment c) [189,731,728] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_364, assignment_365, v365, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_364, assignment_365, v94, hs]
  have hc2086 : ClauseSat (assignment c) [189,730,729] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_364, assignment_365, v365, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_364, assignment_365, v94, hs]
  have hc2087 : ClauseSat (assignment c) [191,732] := by
    by_cases hs : c.b4.val = 0
    · simp [ClauseSat, litVal, assignment_95, assignment_366, v366, v95, hs]
    · simp [ClauseSat, litVal, assignment_95, assignment_366, v95, hs]
  have hc2088 : ClauseSat (assignment c) [193,733] := by
    by_cases hs : c.b4.val = 1
    · simp [ClauseSat, litVal, assignment_96, assignment_366, v366, v96, hs]
    · simp [ClauseSat, litVal, assignment_96, assignment_366, v96, hs]
  have hc2089 : ClauseSat (assignment c) [195,733] := by
    by_cases hs : c.b4.val = 2
    · simp [ClauseSat, litVal, assignment_97, assignment_366, v366, v97, hs]
    · simp [ClauseSat, litVal, assignment_97, assignment_366, v97, hs]
  have hc2090 : ClauseSat (assignment c) [197,733] := by
    by_cases hs : c.b4.val = 3
    · simp [ClauseSat, litVal, assignment_98, assignment_366, v366, v98, hs]
    · simp [ClauseSat, litVal, assignment_98, assignment_366, v98, hs]
  have hc2091 : ClauseSat (assignment c) [199,733,710] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_355, assignment_366, v366, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_355, assignment_366, v99, hs]
  have hc2092 : ClauseSat (assignment c) [199,732,711] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_355, assignment_366, v366, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_355, assignment_366, v99, hs]
  have hc2093 : ClauseSat (assignment c) [201,733,716] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_358, assignment_366, v366, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_358, assignment_366, v100, hs]
  have hc2094 : ClauseSat (assignment c) [201,732,717] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_358, assignment_366, v366, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_358, assignment_366, v100, hs]
  have hc2095 : ClauseSat (assignment c) [203,733,722] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_361, assignment_366, v366, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_361, assignment_366, v101, hs]
  have hc2096 : ClauseSat (assignment c) [203,732,723] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_361, assignment_366, v366, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_361, assignment_366, v101, hs]
  have hc2097 : ClauseSat (assignment c) [205,733,728] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_364, assignment_366, v366, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_364, assignment_366, v102, hs]
  have hc2098 : ClauseSat (assignment c) [205,732,729] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_364, assignment_366, v366, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_364, assignment_366, v102, hs]
  have hc2099 : ClauseSat (assignment c) [173,735,730] := by
    cases ha0 : v86 c <;> cases ha1 : v365 c <;> cases ha2 : v366 c <;> simp [ClauseSat, litVal, assignment_86, assignment_365, assignment_367, v367, ha0, ha1, ha2]
  simp only [chunk20, List.forall_mem_cons]
  exact ⟨hc2000, hc2001, hc2002, hc2003, hc2004, hc2005, hc2006, hc2007, hc2008, hc2009, hc2010, hc2011, hc2012, hc2013, hc2014, hc2015, hc2016, hc2017, hc2018, hc2019, hc2020, hc2021, hc2022, hc2023, hc2024, hc2025, hc2026, hc2027, hc2028, hc2029, hc2030, hc2031, hc2032, hc2033, hc2034, hc2035, hc2036, hc2037, hc2038, hc2039, hc2040, hc2041, hc2042, hc2043, hc2044, hc2045, hc2046, hc2047, hc2048, hc2049, hc2050, hc2051, hc2052, hc2053, hc2054, hc2055, hc2056, hc2057, hc2058, hc2059, hc2060, hc2061, hc2062, hc2063, hc2064, hc2065, hc2066, hc2067, hc2068, hc2069, hc2070, hc2071, hc2072, hc2073, hc2074, hc2075, hc2076, hc2077, hc2078, hc2079, hc2080, hc2081, hc2082, hc2083, hc2084, hc2085, hc2086, hc2087, hc2088, hc2089, hc2090, hc2091, hc2092, hc2093, hc2094, hc2095, hc2096, hc2097, hc2098, hc2099, by simp⟩
#check satChunk20

def chunk21 : List (List Nat) := [[173, 735, 732], [173, 734, 731, 733], [172, 734, 731], [172, 734, 733], [172, 735, 730, 732], [7, 737], [9, 736], [11, 737], [13, 737], [15, 739], [17, 738], [19, 739], [21, 739], [741, 706], [741, 738], [740, 707, 739], [743, 736], [743, 708], [742, 737, 709], [745, 741], [745, 743], [744, 740, 742], [747, 737], [747, 739], [746, 736, 738], [5, 749, 745], [5, 748, 744], [4, 749, 747], [4, 748, 746], [37, 751], [39, 750], [41, 751], [43, 751], [45, 751, 748], [45, 750, 749], [47, 753], [49, 752], [51, 753], [53, 753], [55, 753, 748], [55, 752, 749], [755, 712], [755, 752], [754, 713, 753], [757, 750], [757, 714], [756, 751, 715], [759, 755], [759, 757], [758, 754, 756], [761, 751], [761, 753], [760, 750, 752], [35, 763, 759], [35, 762, 758], [34, 763, 761], [34, 762, 760], [75, 765], [77, 764], [79, 765], [81, 765], [83, 765, 748], [83, 764, 749], [85, 765, 762], [85, 764, 763], [87, 767], [89, 766], [91, 767], [93, 767], [95, 767, 748], [95, 766, 749], [97, 767, 762], [97, 766, 763], [769, 718], [769, 766], [768, 719, 767], [771, 764], [771, 720], [770, 765, 721], [773, 769], [773, 771], [772, 768, 770], [775, 765], [775, 767], [774, 764, 766], [73, 777, 773], [73, 776, 772], [72, 777, 775], [72, 776, 774], [121, 779], [123, 778], [125, 779], [127, 779], [129, 779, 748], [129, 778, 749], [131, 779, 762], [131, 778, 763], [133, 779, 776], [133, 778, 777], [135, 781]]
theorem satChunk21 (c : Candidate) (hv : valid c)
    (hr : ∀ r : Fin 16, output c r = target r)
    (hl : derivativeLeft c = false) (hd : derivativeRight c = false) :
    ∀ cl ∈ chunk21, ClauseSat (assignment c) cl := by
  rcases hv with ⟨h0, h1, h2, h3, h4⟩
  have hc2100 : ClauseSat (assignment c) [173,735,732] := by
    cases ha0 : v86 c <;> cases ha1 : v365 c <;> cases ha2 : v366 c <;> simp [ClauseSat, litVal, assignment_86, assignment_366, assignment_367, v367, ha0, ha1, ha2]
  have hc2101 : ClauseSat (assignment c) [173,734,731,733] := by
    cases ha0 : v86 c <;> cases ha1 : v365 c <;> cases ha2 : v366 c <;> simp [ClauseSat, litVal, assignment_86, assignment_365, assignment_366, assignment_367, v367, ha0, ha1, ha2]
  have hc2102 : ClauseSat (assignment c) [172,734,731] := by
    cases ha0 : v86 c <;> cases ha1 : v365 c <;> cases ha2 : v366 c <;> simp [ClauseSat, litVal, assignment_86, assignment_365, assignment_367, v367, ha0, ha1, ha2]
  have hc2103 : ClauseSat (assignment c) [172,734,733] := by
    cases ha0 : v86 c <;> cases ha1 : v365 c <;> cases ha2 : v366 c <;> simp [ClauseSat, litVal, assignment_86, assignment_366, assignment_367, v367, ha0, ha1, ha2]
  have hc2104 : ClauseSat (assignment c) [172,735,730,732] := by
    cases ha0 : v86 c <;> cases ha1 : v365 c <;> cases ha2 : v366 c <;> simp [ClauseSat, litVal, assignment_86, assignment_365, assignment_366, assignment_367, v367, ha0, ha1, ha2]
  have hc2105 : ClauseSat (assignment c) [7,737] := by
    by_cases hs : c.a0.val = 0
    · simp [ClauseSat, litVal, assignment_3, assignment_368, v368, v3, hs]
    · simp [ClauseSat, litVal, assignment_3, assignment_368, v3, hs]
  have hc2106 : ClauseSat (assignment c) [9,736] := by
    by_cases hs : c.a0.val = 1
    · simp [ClauseSat, litVal, assignment_4, assignment_368, v368, v4, hs]
    · simp [ClauseSat, litVal, assignment_4, assignment_368, v4, hs]
  have hc2107 : ClauseSat (assignment c) [11,737] := by
    by_cases hs : c.a0.val = 2
    · simp [ClauseSat, litVal, assignment_5, assignment_368, v368, v5, hs]
    · simp [ClauseSat, litVal, assignment_5, assignment_368, v5, hs]
  have hc2108 : ClauseSat (assignment c) [13,737] := by
    by_cases hs : c.a0.val = 3
    · simp [ClauseSat, litVal, assignment_6, assignment_368, v368, v6, hs]
    · simp [ClauseSat, litVal, assignment_6, assignment_368, v6, hs]
  have hc2109 : ClauseSat (assignment c) [15,739] := by
    by_cases hs : c.b0.val = 0
    · simp [ClauseSat, litVal, assignment_7, assignment_369, v369, v7, hs]
    · simp [ClauseSat, litVal, assignment_7, assignment_369, v7, hs]
  have hc2110 : ClauseSat (assignment c) [17,738] := by
    by_cases hs : c.b0.val = 1
    · simp [ClauseSat, litVal, assignment_8, assignment_369, v369, v8, hs]
    · simp [ClauseSat, litVal, assignment_8, assignment_369, v8, hs]
  have hc2111 : ClauseSat (assignment c) [19,739] := by
    by_cases hs : c.b0.val = 2
    · simp [ClauseSat, litVal, assignment_9, assignment_369, v369, v9, hs]
    · simp [ClauseSat, litVal, assignment_9, assignment_369, v9, hs]
  have hc2112 : ClauseSat (assignment c) [21,739] := by
    by_cases hs : c.b0.val = 3
    · simp [ClauseSat, litVal, assignment_10, assignment_369, v369, v10, hs]
    · simp [ClauseSat, litVal, assignment_10, assignment_369, v10, hs]
  have hc2113 : ClauseSat (assignment c) [741,706] := by
    cases ha0 : v353 c <;> cases ha1 : v369 c <;> simp [ClauseSat, litVal, assignment_353, assignment_370, v370, ha0, ha1]
  have hc2114 : ClauseSat (assignment c) [741,738] := by
    cases ha0 : v353 c <;> cases ha1 : v369 c <;> simp [ClauseSat, litVal, assignment_369, assignment_370, v370, ha0, ha1]
  have hc2115 : ClauseSat (assignment c) [740,707,739] := by
    cases ha0 : v353 c <;> cases ha1 : v369 c <;> simp [ClauseSat, litVal, assignment_353, assignment_369, assignment_370, v370, ha0, ha1]
  have hc2116 : ClauseSat (assignment c) [743,736] := by
    cases ha0 : v354 c <;> cases ha1 : v368 c <;> simp [ClauseSat, litVal, assignment_368, assignment_371, v371, ha0, ha1]
  have hc2117 : ClauseSat (assignment c) [743,708] := by
    cases ha0 : v354 c <;> cases ha1 : v368 c <;> simp [ClauseSat, litVal, assignment_354, assignment_371, v371, ha0, ha1]
  have hc2118 : ClauseSat (assignment c) [742,737,709] := by
    cases ha0 : v354 c <;> cases ha1 : v368 c <;> simp [ClauseSat, litVal, assignment_354, assignment_368, assignment_371, v371, ha0, ha1]
  have hc2119 : ClauseSat (assignment c) [745,741] := by
    cases ha0 : v370 c <;> cases ha1 : v371 c <;> simp [ClauseSat, litVal, assignment_370, assignment_372, v372, ha0, ha1]
  have hc2120 : ClauseSat (assignment c) [745,743] := by
    cases ha0 : v370 c <;> cases ha1 : v371 c <;> simp [ClauseSat, litVal, assignment_371, assignment_372, v372, ha0, ha1]
  have hc2121 : ClauseSat (assignment c) [744,740,742] := by
    cases ha0 : v370 c <;> cases ha1 : v371 c <;> simp [ClauseSat, litVal, assignment_370, assignment_371, assignment_372, v372, ha0, ha1]
  have hc2122 : ClauseSat (assignment c) [747,737] := by
    cases ha0 : v368 c <;> cases ha1 : v369 c <;> simp [ClauseSat, litVal, assignment_368, assignment_373, v373, ha0, ha1]
  have hc2123 : ClauseSat (assignment c) [747,739] := by
    cases ha0 : v368 c <;> cases ha1 : v369 c <;> simp [ClauseSat, litVal, assignment_369, assignment_373, v373, ha0, ha1]
  have hc2124 : ClauseSat (assignment c) [746,736,738] := by
    cases ha0 : v368 c <;> cases ha1 : v369 c <;> simp [ClauseSat, litVal, assignment_368, assignment_369, assignment_373, v373, ha0, ha1]
  have hc2125 : ClauseSat (assignment c) [5,749,745] := by
    cases ha0 : v2 c <;> cases ha1 : v372 c <;> cases ha2 : v373 c <;> simp [ClauseSat, litVal, assignment_2, assignment_372, assignment_374, v374, ha0, ha1, ha2]
  have hc2126 : ClauseSat (assignment c) [5,748,744] := by
    cases ha0 : v2 c <;> cases ha1 : v372 c <;> cases ha2 : v373 c <;> simp [ClauseSat, litVal, assignment_2, assignment_372, assignment_374, v374, ha0, ha1, ha2]
  have hc2127 : ClauseSat (assignment c) [4,749,747] := by
    cases ha0 : v2 c <;> cases ha1 : v372 c <;> cases ha2 : v373 c <;> simp [ClauseSat, litVal, assignment_2, assignment_373, assignment_374, v374, ha0, ha1, ha2]
  have hc2128 : ClauseSat (assignment c) [4,748,746] := by
    cases ha0 : v2 c <;> cases ha1 : v372 c <;> cases ha2 : v373 c <;> simp [ClauseSat, litVal, assignment_2, assignment_373, assignment_374, v374, ha0, ha1, ha2]
  have hc2129 : ClauseSat (assignment c) [37,751] := by
    by_cases hs : c.a1.val = 0
    · simp [ClauseSat, litVal, assignment_18, assignment_375, v375, v18, hs]
    · simp [ClauseSat, litVal, assignment_18, assignment_375, v18, hs]
  have hc2130 : ClauseSat (assignment c) [39,750] := by
    by_cases hs : c.a1.val = 1
    · simp [ClauseSat, litVal, assignment_19, assignment_375, v375, v19, hs]
    · simp [ClauseSat, litVal, assignment_19, assignment_375, v19, hs]
  have hc2131 : ClauseSat (assignment c) [41,751] := by
    by_cases hs : c.a1.val = 2
    · simp [ClauseSat, litVal, assignment_20, assignment_375, v375, v20, hs]
    · simp [ClauseSat, litVal, assignment_20, assignment_375, v20, hs]
  have hc2132 : ClauseSat (assignment c) [43,751] := by
    by_cases hs : c.a1.val = 3
    · simp [ClauseSat, litVal, assignment_21, assignment_375, v375, v21, hs]
    · simp [ClauseSat, litVal, assignment_21, assignment_375, v21, hs]
  have hc2133 : ClauseSat (assignment c) [45,751,748] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_374, assignment_375, v375, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_374, assignment_375, v22, hs]
  have hc2134 : ClauseSat (assignment c) [45,750,749] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_374, assignment_375, v375, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_374, assignment_375, v22, hs]
  have hc2135 : ClauseSat (assignment c) [47,753] := by
    by_cases hs : c.b1.val = 0
    · simp [ClauseSat, litVal, assignment_23, assignment_376, v376, v23, hs]
    · simp [ClauseSat, litVal, assignment_23, assignment_376, v23, hs]
  have hc2136 : ClauseSat (assignment c) [49,752] := by
    by_cases hs : c.b1.val = 1
    · simp [ClauseSat, litVal, assignment_24, assignment_376, v376, v24, hs]
    · simp [ClauseSat, litVal, assignment_24, assignment_376, v24, hs]
  have hc2137 : ClauseSat (assignment c) [51,753] := by
    by_cases hs : c.b1.val = 2
    · simp [ClauseSat, litVal, assignment_25, assignment_376, v376, v25, hs]
    · simp [ClauseSat, litVal, assignment_25, assignment_376, v25, hs]
  have hc2138 : ClauseSat (assignment c) [53,753] := by
    by_cases hs : c.b1.val = 3
    · simp [ClauseSat, litVal, assignment_26, assignment_376, v376, v26, hs]
    · simp [ClauseSat, litVal, assignment_26, assignment_376, v26, hs]
  have hc2139 : ClauseSat (assignment c) [55,753,748] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_374, assignment_376, v376, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_374, assignment_376, v27, hs]
  have hc2140 : ClauseSat (assignment c) [55,752,749] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_374, assignment_376, v376, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_374, assignment_376, v27, hs]
  have hc2141 : ClauseSat (assignment c) [755,712] := by
    cases ha0 : v356 c <;> cases ha1 : v376 c <;> simp [ClauseSat, litVal, assignment_356, assignment_377, v377, ha0, ha1]
  have hc2142 : ClauseSat (assignment c) [755,752] := by
    cases ha0 : v356 c <;> cases ha1 : v376 c <;> simp [ClauseSat, litVal, assignment_376, assignment_377, v377, ha0, ha1]
  have hc2143 : ClauseSat (assignment c) [754,713,753] := by
    cases ha0 : v356 c <;> cases ha1 : v376 c <;> simp [ClauseSat, litVal, assignment_356, assignment_376, assignment_377, v377, ha0, ha1]
  have hc2144 : ClauseSat (assignment c) [757,750] := by
    cases ha0 : v357 c <;> cases ha1 : v375 c <;> simp [ClauseSat, litVal, assignment_375, assignment_378, v378, ha0, ha1]
  have hc2145 : ClauseSat (assignment c) [757,714] := by
    cases ha0 : v357 c <;> cases ha1 : v375 c <;> simp [ClauseSat, litVal, assignment_357, assignment_378, v378, ha0, ha1]
  have hc2146 : ClauseSat (assignment c) [756,751,715] := by
    cases ha0 : v357 c <;> cases ha1 : v375 c <;> simp [ClauseSat, litVal, assignment_357, assignment_375, assignment_378, v378, ha0, ha1]
  have hc2147 : ClauseSat (assignment c) [759,755] := by
    cases ha0 : v377 c <;> cases ha1 : v378 c <;> simp [ClauseSat, litVal, assignment_377, assignment_379, v379, ha0, ha1]
  have hc2148 : ClauseSat (assignment c) [759,757] := by
    cases ha0 : v377 c <;> cases ha1 : v378 c <;> simp [ClauseSat, litVal, assignment_378, assignment_379, v379, ha0, ha1]
  have hc2149 : ClauseSat (assignment c) [758,754,756] := by
    cases ha0 : v377 c <;> cases ha1 : v378 c <;> simp [ClauseSat, litVal, assignment_377, assignment_378, assignment_379, v379, ha0, ha1]
  have hc2150 : ClauseSat (assignment c) [761,751] := by
    cases ha0 : v375 c <;> cases ha1 : v376 c <;> simp [ClauseSat, litVal, assignment_375, assignment_380, v380, ha0, ha1]
  have hc2151 : ClauseSat (assignment c) [761,753] := by
    cases ha0 : v375 c <;> cases ha1 : v376 c <;> simp [ClauseSat, litVal, assignment_376, assignment_380, v380, ha0, ha1]
  have hc2152 : ClauseSat (assignment c) [760,750,752] := by
    cases ha0 : v375 c <;> cases ha1 : v376 c <;> simp [ClauseSat, litVal, assignment_375, assignment_376, assignment_380, v380, ha0, ha1]
  have hc2153 : ClauseSat (assignment c) [35,763,759] := by
    cases ha0 : v17 c <;> cases ha1 : v379 c <;> cases ha2 : v380 c <;> simp [ClauseSat, litVal, assignment_17, assignment_379, assignment_381, v381, ha0, ha1, ha2]
  have hc2154 : ClauseSat (assignment c) [35,762,758] := by
    cases ha0 : v17 c <;> cases ha1 : v379 c <;> cases ha2 : v380 c <;> simp [ClauseSat, litVal, assignment_17, assignment_379, assignment_381, v381, ha0, ha1, ha2]
  have hc2155 : ClauseSat (assignment c) [34,763,761] := by
    cases ha0 : v17 c <;> cases ha1 : v379 c <;> cases ha2 : v380 c <;> simp [ClauseSat, litVal, assignment_17, assignment_380, assignment_381, v381, ha0, ha1, ha2]
  have hc2156 : ClauseSat (assignment c) [34,762,760] := by
    cases ha0 : v17 c <;> cases ha1 : v379 c <;> cases ha2 : v380 c <;> simp [ClauseSat, litVal, assignment_17, assignment_380, assignment_381, v381, ha0, ha1, ha2]
  have hc2157 : ClauseSat (assignment c) [75,765] := by
    by_cases hs : c.a2.val = 0
    · simp [ClauseSat, litVal, assignment_37, assignment_382, v382, v37, hs]
    · simp [ClauseSat, litVal, assignment_37, assignment_382, v37, hs]
  have hc2158 : ClauseSat (assignment c) [77,764] := by
    by_cases hs : c.a2.val = 1
    · simp [ClauseSat, litVal, assignment_38, assignment_382, v382, v38, hs]
    · simp [ClauseSat, litVal, assignment_38, assignment_382, v38, hs]
  have hc2159 : ClauseSat (assignment c) [79,765] := by
    by_cases hs : c.a2.val = 2
    · simp [ClauseSat, litVal, assignment_39, assignment_382, v382, v39, hs]
    · simp [ClauseSat, litVal, assignment_39, assignment_382, v39, hs]
  have hc2160 : ClauseSat (assignment c) [81,765] := by
    by_cases hs : c.a2.val = 3
    · simp [ClauseSat, litVal, assignment_40, assignment_382, v382, v40, hs]
    · simp [ClauseSat, litVal, assignment_40, assignment_382, v40, hs]
  have hc2161 : ClauseSat (assignment c) [83,765,748] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_374, assignment_382, v382, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_374, assignment_382, v41, hs]
  have hc2162 : ClauseSat (assignment c) [83,764,749] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_374, assignment_382, v382, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_374, assignment_382, v41, hs]
  have hc2163 : ClauseSat (assignment c) [85,765,762] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_381, assignment_382, v382, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_381, assignment_382, v42, hs]
  have hc2164 : ClauseSat (assignment c) [85,764,763] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_381, assignment_382, v382, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_381, assignment_382, v42, hs]
  have hc2165 : ClauseSat (assignment c) [87,767] := by
    by_cases hs : c.b2.val = 0
    · simp [ClauseSat, litVal, assignment_43, assignment_383, v383, v43, hs]
    · simp [ClauseSat, litVal, assignment_43, assignment_383, v43, hs]
  have hc2166 : ClauseSat (assignment c) [89,766] := by
    by_cases hs : c.b2.val = 1
    · simp [ClauseSat, litVal, assignment_44, assignment_383, v383, v44, hs]
    · simp [ClauseSat, litVal, assignment_44, assignment_383, v44, hs]
  have hc2167 : ClauseSat (assignment c) [91,767] := by
    by_cases hs : c.b2.val = 2
    · simp [ClauseSat, litVal, assignment_45, assignment_383, v383, v45, hs]
    · simp [ClauseSat, litVal, assignment_45, assignment_383, v45, hs]
  have hc2168 : ClauseSat (assignment c) [93,767] := by
    by_cases hs : c.b2.val = 3
    · simp [ClauseSat, litVal, assignment_46, assignment_383, v383, v46, hs]
    · simp [ClauseSat, litVal, assignment_46, assignment_383, v46, hs]
  have hc2169 : ClauseSat (assignment c) [95,767,748] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_374, assignment_383, v383, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_374, assignment_383, v47, hs]
  have hc2170 : ClauseSat (assignment c) [95,766,749] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_374, assignment_383, v383, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_374, assignment_383, v47, hs]
  have hc2171 : ClauseSat (assignment c) [97,767,762] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_381, assignment_383, v383, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_381, assignment_383, v48, hs]
  have hc2172 : ClauseSat (assignment c) [97,766,763] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_381, assignment_383, v383, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_381, assignment_383, v48, hs]
  have hc2173 : ClauseSat (assignment c) [769,718] := by
    cases ha0 : v359 c <;> cases ha1 : v383 c <;> simp [ClauseSat, litVal, assignment_359, assignment_384, v384, ha0, ha1]
  have hc2174 : ClauseSat (assignment c) [769,766] := by
    cases ha0 : v359 c <;> cases ha1 : v383 c <;> simp [ClauseSat, litVal, assignment_383, assignment_384, v384, ha0, ha1]
  have hc2175 : ClauseSat (assignment c) [768,719,767] := by
    cases ha0 : v359 c <;> cases ha1 : v383 c <;> simp [ClauseSat, litVal, assignment_359, assignment_383, assignment_384, v384, ha0, ha1]
  have hc2176 : ClauseSat (assignment c) [771,764] := by
    cases ha0 : v360 c <;> cases ha1 : v382 c <;> simp [ClauseSat, litVal, assignment_382, assignment_385, v385, ha0, ha1]
  have hc2177 : ClauseSat (assignment c) [771,720] := by
    cases ha0 : v360 c <;> cases ha1 : v382 c <;> simp [ClauseSat, litVal, assignment_360, assignment_385, v385, ha0, ha1]
  have hc2178 : ClauseSat (assignment c) [770,765,721] := by
    cases ha0 : v360 c <;> cases ha1 : v382 c <;> simp [ClauseSat, litVal, assignment_360, assignment_382, assignment_385, v385, ha0, ha1]
  have hc2179 : ClauseSat (assignment c) [773,769] := by
    cases ha0 : v384 c <;> cases ha1 : v385 c <;> simp [ClauseSat, litVal, assignment_384, assignment_386, v386, ha0, ha1]
  have hc2180 : ClauseSat (assignment c) [773,771] := by
    cases ha0 : v384 c <;> cases ha1 : v385 c <;> simp [ClauseSat, litVal, assignment_385, assignment_386, v386, ha0, ha1]
  have hc2181 : ClauseSat (assignment c) [772,768,770] := by
    cases ha0 : v384 c <;> cases ha1 : v385 c <;> simp [ClauseSat, litVal, assignment_384, assignment_385, assignment_386, v386, ha0, ha1]
  have hc2182 : ClauseSat (assignment c) [775,765] := by
    cases ha0 : v382 c <;> cases ha1 : v383 c <;> simp [ClauseSat, litVal, assignment_382, assignment_387, v387, ha0, ha1]
  have hc2183 : ClauseSat (assignment c) [775,767] := by
    cases ha0 : v382 c <;> cases ha1 : v383 c <;> simp [ClauseSat, litVal, assignment_383, assignment_387, v387, ha0, ha1]
  have hc2184 : ClauseSat (assignment c) [774,764,766] := by
    cases ha0 : v382 c <;> cases ha1 : v383 c <;> simp [ClauseSat, litVal, assignment_382, assignment_383, assignment_387, v387, ha0, ha1]
  have hc2185 : ClauseSat (assignment c) [73,777,773] := by
    cases ha0 : v36 c <;> cases ha1 : v386 c <;> cases ha2 : v387 c <;> simp [ClauseSat, litVal, assignment_36, assignment_386, assignment_388, v388, ha0, ha1, ha2]
  have hc2186 : ClauseSat (assignment c) [73,776,772] := by
    cases ha0 : v36 c <;> cases ha1 : v386 c <;> cases ha2 : v387 c <;> simp [ClauseSat, litVal, assignment_36, assignment_386, assignment_388, v388, ha0, ha1, ha2]
  have hc2187 : ClauseSat (assignment c) [72,777,775] := by
    cases ha0 : v36 c <;> cases ha1 : v386 c <;> cases ha2 : v387 c <;> simp [ClauseSat, litVal, assignment_36, assignment_387, assignment_388, v388, ha0, ha1, ha2]
  have hc2188 : ClauseSat (assignment c) [72,776,774] := by
    cases ha0 : v36 c <;> cases ha1 : v386 c <;> cases ha2 : v387 c <;> simp [ClauseSat, litVal, assignment_36, assignment_387, assignment_388, v388, ha0, ha1, ha2]
  have hc2189 : ClauseSat (assignment c) [121,779] := by
    by_cases hs : c.a3.val = 0
    · simp [ClauseSat, litVal, assignment_60, assignment_389, v389, v60, hs]
    · simp [ClauseSat, litVal, assignment_60, assignment_389, v60, hs]
  have hc2190 : ClauseSat (assignment c) [123,778] := by
    by_cases hs : c.a3.val = 1
    · simp [ClauseSat, litVal, assignment_61, assignment_389, v389, v61, hs]
    · simp [ClauseSat, litVal, assignment_61, assignment_389, v61, hs]
  have hc2191 : ClauseSat (assignment c) [125,779] := by
    by_cases hs : c.a3.val = 2
    · simp [ClauseSat, litVal, assignment_62, assignment_389, v389, v62, hs]
    · simp [ClauseSat, litVal, assignment_62, assignment_389, v62, hs]
  have hc2192 : ClauseSat (assignment c) [127,779] := by
    by_cases hs : c.a3.val = 3
    · simp [ClauseSat, litVal, assignment_63, assignment_389, v389, v63, hs]
    · simp [ClauseSat, litVal, assignment_63, assignment_389, v63, hs]
  have hc2193 : ClauseSat (assignment c) [129,779,748] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_374, assignment_389, v389, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_374, assignment_389, v64, hs]
  have hc2194 : ClauseSat (assignment c) [129,778,749] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_374, assignment_389, v389, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_374, assignment_389, v64, hs]
  have hc2195 : ClauseSat (assignment c) [131,779,762] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_381, assignment_389, v389, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_381, assignment_389, v65, hs]
  have hc2196 : ClauseSat (assignment c) [131,778,763] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_381, assignment_389, v389, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_381, assignment_389, v65, hs]
  have hc2197 : ClauseSat (assignment c) [133,779,776] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_388, assignment_389, v389, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_388, assignment_389, v66, hs]
  have hc2198 : ClauseSat (assignment c) [133,778,777] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_388, assignment_389, v389, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_388, assignment_389, v66, hs]
  have hc2199 : ClauseSat (assignment c) [135,781] := by
    by_cases hs : c.b3.val = 0
    · simp [ClauseSat, litVal, assignment_67, assignment_390, v390, v67, hs]
    · simp [ClauseSat, litVal, assignment_67, assignment_390, v67, hs]
  simp only [chunk21, List.forall_mem_cons]
  exact ⟨hc2100, hc2101, hc2102, hc2103, hc2104, hc2105, hc2106, hc2107, hc2108, hc2109, hc2110, hc2111, hc2112, hc2113, hc2114, hc2115, hc2116, hc2117, hc2118, hc2119, hc2120, hc2121, hc2122, hc2123, hc2124, hc2125, hc2126, hc2127, hc2128, hc2129, hc2130, hc2131, hc2132, hc2133, hc2134, hc2135, hc2136, hc2137, hc2138, hc2139, hc2140, hc2141, hc2142, hc2143, hc2144, hc2145, hc2146, hc2147, hc2148, hc2149, hc2150, hc2151, hc2152, hc2153, hc2154, hc2155, hc2156, hc2157, hc2158, hc2159, hc2160, hc2161, hc2162, hc2163, hc2164, hc2165, hc2166, hc2167, hc2168, hc2169, hc2170, hc2171, hc2172, hc2173, hc2174, hc2175, hc2176, hc2177, hc2178, hc2179, hc2180, hc2181, hc2182, hc2183, hc2184, hc2185, hc2186, hc2187, hc2188, hc2189, hc2190, hc2191, hc2192, hc2193, hc2194, hc2195, hc2196, hc2197, hc2198, hc2199, by simp⟩
#check satChunk21

def chunk22 : List (List Nat) := [[137, 780], [139, 781], [141, 781], [143, 781, 748], [143, 780, 749], [145, 781, 762], [145, 780, 763], [147, 781, 776], [147, 780, 777], [783, 724], [783, 780], [782, 725, 781], [785, 778], [785, 726], [784, 779, 727], [787, 783], [787, 785], [786, 782, 784], [789, 779], [789, 781], [788, 778, 780], [119, 791, 787], [119, 790, 786], [118, 791, 789], [118, 790, 788], [175, 793], [177, 792], [179, 793], [181, 793], [183, 793, 748], [183, 792, 749], [185, 793, 762], [185, 792, 763], [187, 793, 776], [187, 792, 777], [189, 793, 790], [189, 792, 791], [191, 795], [193, 794], [195, 795], [197, 795], [199, 795, 748], [199, 794, 749], [201, 795, 762], [201, 794, 763], [203, 795, 776], [203, 794, 777], [205, 795, 790], [205, 794, 791], [797, 730], [797, 794], [796, 731, 795], [799, 792], [799, 732], [798, 793, 733], [801, 797], [801, 799], [800, 796, 798], [803, 793], [803, 795], [802, 792, 794], [173, 805, 801], [173, 804, 800], [172, 805, 803], [172, 804, 802], [805], [7, 807], [9, 806], [11, 807], [13, 807], [15, 809], [17, 808], [19, 809], [21, 809], [5, 811, 806], [5, 811, 808], [5, 810, 807, 809], [4, 810, 807], [4, 810, 809], [4, 811, 806, 808], [37, 813], [39, 812], [41, 813], [43, 813], [45, 813, 810], [45, 812, 811], [47, 815], [49, 814], [51, 815], [53, 815], [55, 815, 810], [55, 814, 811], [35, 817, 812], [35, 817, 814], [35, 816, 813, 815], [34, 816, 813], [34, 816, 815], [34, 817, 812, 814], [75, 819], [77, 818]]
theorem satChunk22 (c : Candidate) (hv : valid c)
    (hr : ∀ r : Fin 16, output c r = target r)
    (hl : derivativeLeft c = false) (hd : derivativeRight c = false) :
    ∀ cl ∈ chunk22, ClauseSat (assignment c) cl := by
  rcases hv with ⟨h0, h1, h2, h3, h4⟩
  have hc2200 : ClauseSat (assignment c) [137,780] := by
    by_cases hs : c.b3.val = 1
    · simp [ClauseSat, litVal, assignment_68, assignment_390, v390, v68, hs]
    · simp [ClauseSat, litVal, assignment_68, assignment_390, v68, hs]
  have hc2201 : ClauseSat (assignment c) [139,781] := by
    by_cases hs : c.b3.val = 2
    · simp [ClauseSat, litVal, assignment_69, assignment_390, v390, v69, hs]
    · simp [ClauseSat, litVal, assignment_69, assignment_390, v69, hs]
  have hc2202 : ClauseSat (assignment c) [141,781] := by
    by_cases hs : c.b3.val = 3
    · simp [ClauseSat, litVal, assignment_70, assignment_390, v390, v70, hs]
    · simp [ClauseSat, litVal, assignment_70, assignment_390, v70, hs]
  have hc2203 : ClauseSat (assignment c) [143,781,748] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_374, assignment_390, v390, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_374, assignment_390, v71, hs]
  have hc2204 : ClauseSat (assignment c) [143,780,749] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_374, assignment_390, v390, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_374, assignment_390, v71, hs]
  have hc2205 : ClauseSat (assignment c) [145,781,762] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_381, assignment_390, v390, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_381, assignment_390, v72, hs]
  have hc2206 : ClauseSat (assignment c) [145,780,763] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_381, assignment_390, v390, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_381, assignment_390, v72, hs]
  have hc2207 : ClauseSat (assignment c) [147,781,776] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_388, assignment_390, v390, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_388, assignment_390, v73, hs]
  have hc2208 : ClauseSat (assignment c) [147,780,777] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_388, assignment_390, v390, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_388, assignment_390, v73, hs]
  have hc2209 : ClauseSat (assignment c) [783,724] := by
    cases ha0 : v362 c <;> cases ha1 : v390 c <;> simp [ClauseSat, litVal, assignment_362, assignment_391, v391, ha0, ha1]
  have hc2210 : ClauseSat (assignment c) [783,780] := by
    cases ha0 : v362 c <;> cases ha1 : v390 c <;> simp [ClauseSat, litVal, assignment_390, assignment_391, v391, ha0, ha1]
  have hc2211 : ClauseSat (assignment c) [782,725,781] := by
    cases ha0 : v362 c <;> cases ha1 : v390 c <;> simp [ClauseSat, litVal, assignment_362, assignment_390, assignment_391, v391, ha0, ha1]
  have hc2212 : ClauseSat (assignment c) [785,778] := by
    cases ha0 : v363 c <;> cases ha1 : v389 c <;> simp [ClauseSat, litVal, assignment_389, assignment_392, v392, ha0, ha1]
  have hc2213 : ClauseSat (assignment c) [785,726] := by
    cases ha0 : v363 c <;> cases ha1 : v389 c <;> simp [ClauseSat, litVal, assignment_363, assignment_392, v392, ha0, ha1]
  have hc2214 : ClauseSat (assignment c) [784,779,727] := by
    cases ha0 : v363 c <;> cases ha1 : v389 c <;> simp [ClauseSat, litVal, assignment_363, assignment_389, assignment_392, v392, ha0, ha1]
  have hc2215 : ClauseSat (assignment c) [787,783] := by
    cases ha0 : v391 c <;> cases ha1 : v392 c <;> simp [ClauseSat, litVal, assignment_391, assignment_393, v393, ha0, ha1]
  have hc2216 : ClauseSat (assignment c) [787,785] := by
    cases ha0 : v391 c <;> cases ha1 : v392 c <;> simp [ClauseSat, litVal, assignment_392, assignment_393, v393, ha0, ha1]
  have hc2217 : ClauseSat (assignment c) [786,782,784] := by
    cases ha0 : v391 c <;> cases ha1 : v392 c <;> simp [ClauseSat, litVal, assignment_391, assignment_392, assignment_393, v393, ha0, ha1]
  have hc2218 : ClauseSat (assignment c) [789,779] := by
    cases ha0 : v389 c <;> cases ha1 : v390 c <;> simp [ClauseSat, litVal, assignment_389, assignment_394, v394, ha0, ha1]
  have hc2219 : ClauseSat (assignment c) [789,781] := by
    cases ha0 : v389 c <;> cases ha1 : v390 c <;> simp [ClauseSat, litVal, assignment_390, assignment_394, v394, ha0, ha1]
  have hc2220 : ClauseSat (assignment c) [788,778,780] := by
    cases ha0 : v389 c <;> cases ha1 : v390 c <;> simp [ClauseSat, litVal, assignment_389, assignment_390, assignment_394, v394, ha0, ha1]
  have hc2221 : ClauseSat (assignment c) [119,791,787] := by
    cases ha0 : v59 c <;> cases ha1 : v393 c <;> cases ha2 : v394 c <;> simp [ClauseSat, litVal, assignment_59, assignment_393, assignment_395, v395, ha0, ha1, ha2]
  have hc2222 : ClauseSat (assignment c) [119,790,786] := by
    cases ha0 : v59 c <;> cases ha1 : v393 c <;> cases ha2 : v394 c <;> simp [ClauseSat, litVal, assignment_59, assignment_393, assignment_395, v395, ha0, ha1, ha2]
  have hc2223 : ClauseSat (assignment c) [118,791,789] := by
    cases ha0 : v59 c <;> cases ha1 : v393 c <;> cases ha2 : v394 c <;> simp [ClauseSat, litVal, assignment_59, assignment_394, assignment_395, v395, ha0, ha1, ha2]
  have hc2224 : ClauseSat (assignment c) [118,790,788] := by
    cases ha0 : v59 c <;> cases ha1 : v393 c <;> cases ha2 : v394 c <;> simp [ClauseSat, litVal, assignment_59, assignment_394, assignment_395, v395, ha0, ha1, ha2]
  have hc2225 : ClauseSat (assignment c) [175,793] := by
    by_cases hs : c.a4.val = 0
    · simp [ClauseSat, litVal, assignment_87, assignment_396, v396, v87, hs]
    · simp [ClauseSat, litVal, assignment_87, assignment_396, v87, hs]
  have hc2226 : ClauseSat (assignment c) [177,792] := by
    by_cases hs : c.a4.val = 1
    · simp [ClauseSat, litVal, assignment_88, assignment_396, v396, v88, hs]
    · simp [ClauseSat, litVal, assignment_88, assignment_396, v88, hs]
  have hc2227 : ClauseSat (assignment c) [179,793] := by
    by_cases hs : c.a4.val = 2
    · simp [ClauseSat, litVal, assignment_89, assignment_396, v396, v89, hs]
    · simp [ClauseSat, litVal, assignment_89, assignment_396, v89, hs]
  have hc2228 : ClauseSat (assignment c) [181,793] := by
    by_cases hs : c.a4.val = 3
    · simp [ClauseSat, litVal, assignment_90, assignment_396, v396, v90, hs]
    · simp [ClauseSat, litVal, assignment_90, assignment_396, v90, hs]
  have hc2229 : ClauseSat (assignment c) [183,793,748] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_374, assignment_396, v396, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_374, assignment_396, v91, hs]
  have hc2230 : ClauseSat (assignment c) [183,792,749] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_374, assignment_396, v396, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_374, assignment_396, v91, hs]
  have hc2231 : ClauseSat (assignment c) [185,793,762] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_381, assignment_396, v396, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_381, assignment_396, v92, hs]
  have hc2232 : ClauseSat (assignment c) [185,792,763] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_381, assignment_396, v396, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_381, assignment_396, v92, hs]
  have hc2233 : ClauseSat (assignment c) [187,793,776] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_388, assignment_396, v396, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_388, assignment_396, v93, hs]
  have hc2234 : ClauseSat (assignment c) [187,792,777] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_388, assignment_396, v396, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_388, assignment_396, v93, hs]
  have hc2235 : ClauseSat (assignment c) [189,793,790] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_395, assignment_396, v396, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_395, assignment_396, v94, hs]
  have hc2236 : ClauseSat (assignment c) [189,792,791] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_395, assignment_396, v396, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_395, assignment_396, v94, hs]
  have hc2237 : ClauseSat (assignment c) [191,795] := by
    by_cases hs : c.b4.val = 0
    · simp [ClauseSat, litVal, assignment_95, assignment_397, v397, v95, hs]
    · simp [ClauseSat, litVal, assignment_95, assignment_397, v95, hs]
  have hc2238 : ClauseSat (assignment c) [193,794] := by
    by_cases hs : c.b4.val = 1
    · simp [ClauseSat, litVal, assignment_96, assignment_397, v397, v96, hs]
    · simp [ClauseSat, litVal, assignment_96, assignment_397, v96, hs]
  have hc2239 : ClauseSat (assignment c) [195,795] := by
    by_cases hs : c.b4.val = 2
    · simp [ClauseSat, litVal, assignment_97, assignment_397, v397, v97, hs]
    · simp [ClauseSat, litVal, assignment_97, assignment_397, v97, hs]
  have hc2240 : ClauseSat (assignment c) [197,795] := by
    by_cases hs : c.b4.val = 3
    · simp [ClauseSat, litVal, assignment_98, assignment_397, v397, v98, hs]
    · simp [ClauseSat, litVal, assignment_98, assignment_397, v98, hs]
  have hc2241 : ClauseSat (assignment c) [199,795,748] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_374, assignment_397, v397, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_374, assignment_397, v99, hs]
  have hc2242 : ClauseSat (assignment c) [199,794,749] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_374, assignment_397, v397, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_374, assignment_397, v99, hs]
  have hc2243 : ClauseSat (assignment c) [201,795,762] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_381, assignment_397, v397, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_381, assignment_397, v100, hs]
  have hc2244 : ClauseSat (assignment c) [201,794,763] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_381, assignment_397, v397, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_381, assignment_397, v100, hs]
  have hc2245 : ClauseSat (assignment c) [203,795,776] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_388, assignment_397, v397, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_388, assignment_397, v101, hs]
  have hc2246 : ClauseSat (assignment c) [203,794,777] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_388, assignment_397, v397, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_388, assignment_397, v101, hs]
  have hc2247 : ClauseSat (assignment c) [205,795,790] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_395, assignment_397, v397, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_395, assignment_397, v102, hs]
  have hc2248 : ClauseSat (assignment c) [205,794,791] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_395, assignment_397, v397, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_395, assignment_397, v102, hs]
  have hc2249 : ClauseSat (assignment c) [797,730] := by
    cases ha0 : v365 c <;> cases ha1 : v397 c <;> simp [ClauseSat, litVal, assignment_365, assignment_398, v398, ha0, ha1]
  have hc2250 : ClauseSat (assignment c) [797,794] := by
    cases ha0 : v365 c <;> cases ha1 : v397 c <;> simp [ClauseSat, litVal, assignment_397, assignment_398, v398, ha0, ha1]
  have hc2251 : ClauseSat (assignment c) [796,731,795] := by
    cases ha0 : v365 c <;> cases ha1 : v397 c <;> simp [ClauseSat, litVal, assignment_365, assignment_397, assignment_398, v398, ha0, ha1]
  have hc2252 : ClauseSat (assignment c) [799,792] := by
    cases ha0 : v366 c <;> cases ha1 : v396 c <;> simp [ClauseSat, litVal, assignment_396, assignment_399, v399, ha0, ha1]
  have hc2253 : ClauseSat (assignment c) [799,732] := by
    cases ha0 : v366 c <;> cases ha1 : v396 c <;> simp [ClauseSat, litVal, assignment_366, assignment_399, v399, ha0, ha1]
  have hc2254 : ClauseSat (assignment c) [798,793,733] := by
    cases ha0 : v366 c <;> cases ha1 : v396 c <;> simp [ClauseSat, litVal, assignment_366, assignment_396, assignment_399, v399, ha0, ha1]
  have hc2255 : ClauseSat (assignment c) [801,797] := by
    cases ha0 : v398 c <;> cases ha1 : v399 c <;> simp [ClauseSat, litVal, assignment_398, assignment_400, v400, ha0, ha1]
  have hc2256 : ClauseSat (assignment c) [801,799] := by
    cases ha0 : v398 c <;> cases ha1 : v399 c <;> simp [ClauseSat, litVal, assignment_399, assignment_400, v400, ha0, ha1]
  have hc2257 : ClauseSat (assignment c) [800,796,798] := by
    cases ha0 : v398 c <;> cases ha1 : v399 c <;> simp [ClauseSat, litVal, assignment_398, assignment_399, assignment_400, v400, ha0, ha1]
  have hc2258 : ClauseSat (assignment c) [803,793] := by
    cases ha0 : v396 c <;> cases ha1 : v397 c <;> simp [ClauseSat, litVal, assignment_396, assignment_401, v401, ha0, ha1]
  have hc2259 : ClauseSat (assignment c) [803,795] := by
    cases ha0 : v396 c <;> cases ha1 : v397 c <;> simp [ClauseSat, litVal, assignment_397, assignment_401, v401, ha0, ha1]
  have hc2260 : ClauseSat (assignment c) [802,792,794] := by
    cases ha0 : v396 c <;> cases ha1 : v397 c <;> simp [ClauseSat, litVal, assignment_396, assignment_397, assignment_401, v401, ha0, ha1]
  have hc2261 : ClauseSat (assignment c) [173,805,801] := by
    cases ha0 : v86 c <;> cases ha1 : v400 c <;> cases ha2 : v401 c <;> simp [ClauseSat, litVal, assignment_86, assignment_400, assignment_402, v402, ha0, ha1, ha2]
  have hc2262 : ClauseSat (assignment c) [173,804,800] := by
    cases ha0 : v86 c <;> cases ha1 : v400 c <;> cases ha2 : v401 c <;> simp [ClauseSat, litVal, assignment_86, assignment_400, assignment_402, v402, ha0, ha1, ha2]
  have hc2263 : ClauseSat (assignment c) [172,805,803] := by
    cases ha0 : v86 c <;> cases ha1 : v400 c <;> cases ha2 : v401 c <;> simp [ClauseSat, litVal, assignment_86, assignment_401, assignment_402, v402, ha0, ha1, ha2]
  have hc2264 : ClauseSat (assignment c) [172,804,802] := by
    cases ha0 : v86 c <;> cases ha1 : v400 c <;> cases ha2 : v401 c <;> simp [ClauseSat, litVal, assignment_86, assignment_401, assignment_402, v402, ha0, ha1, ha2]
  have hc2265 : ClauseSat (assignment c) [805] := by
    simpa [ClauseSat, litVal, assignment_402, derivativeLeft] using hl
  have hc2266 : ClauseSat (assignment c) [7,807] := by
    by_cases hs : c.a0.val = 0
    · simp [ClauseSat, litVal, assignment_3, assignment_403, v403, v3, hs]
    · simp [ClauseSat, litVal, assignment_3, assignment_403, v3, hs]
  have hc2267 : ClauseSat (assignment c) [9,806] := by
    by_cases hs : c.a0.val = 1
    · simp [ClauseSat, litVal, assignment_4, assignment_403, v403, v4, hs]
    · simp [ClauseSat, litVal, assignment_4, assignment_403, v4, hs]
  have hc2268 : ClauseSat (assignment c) [11,807] := by
    by_cases hs : c.a0.val = 2
    · simp [ClauseSat, litVal, assignment_5, assignment_403, v403, v5, hs]
    · simp [ClauseSat, litVal, assignment_5, assignment_403, v5, hs]
  have hc2269 : ClauseSat (assignment c) [13,807] := by
    by_cases hs : c.a0.val = 3
    · simp [ClauseSat, litVal, assignment_6, assignment_403, v403, v6, hs]
    · simp [ClauseSat, litVal, assignment_6, assignment_403, v6, hs]
  have hc2270 : ClauseSat (assignment c) [15,809] := by
    by_cases hs : c.b0.val = 0
    · simp [ClauseSat, litVal, assignment_7, assignment_404, v404, v7, hs]
    · simp [ClauseSat, litVal, assignment_7, assignment_404, v7, hs]
  have hc2271 : ClauseSat (assignment c) [17,808] := by
    by_cases hs : c.b0.val = 1
    · simp [ClauseSat, litVal, assignment_8, assignment_404, v404, v8, hs]
    · simp [ClauseSat, litVal, assignment_8, assignment_404, v8, hs]
  have hc2272 : ClauseSat (assignment c) [19,809] := by
    by_cases hs : c.b0.val = 2
    · simp [ClauseSat, litVal, assignment_9, assignment_404, v404, v9, hs]
    · simp [ClauseSat, litVal, assignment_9, assignment_404, v9, hs]
  have hc2273 : ClauseSat (assignment c) [21,809] := by
    by_cases hs : c.b0.val = 3
    · simp [ClauseSat, litVal, assignment_10, assignment_404, v404, v10, hs]
    · simp [ClauseSat, litVal, assignment_10, assignment_404, v10, hs]
  have hc2274 : ClauseSat (assignment c) [5,811,806] := by
    cases ha0 : v2 c <;> cases ha1 : v403 c <;> cases ha2 : v404 c <;> simp [ClauseSat, litVal, assignment_2, assignment_403, assignment_405, v405, ha0, ha1, ha2]
  have hc2275 : ClauseSat (assignment c) [5,811,808] := by
    cases ha0 : v2 c <;> cases ha1 : v403 c <;> cases ha2 : v404 c <;> simp [ClauseSat, litVal, assignment_2, assignment_404, assignment_405, v405, ha0, ha1, ha2]
  have hc2276 : ClauseSat (assignment c) [5,810,807,809] := by
    cases ha0 : v2 c <;> cases ha1 : v403 c <;> cases ha2 : v404 c <;> simp [ClauseSat, litVal, assignment_2, assignment_403, assignment_404, assignment_405, v405, ha0, ha1, ha2]
  have hc2277 : ClauseSat (assignment c) [4,810,807] := by
    cases ha0 : v2 c <;> cases ha1 : v403 c <;> cases ha2 : v404 c <;> simp [ClauseSat, litVal, assignment_2, assignment_403, assignment_405, v405, ha0, ha1, ha2]
  have hc2278 : ClauseSat (assignment c) [4,810,809] := by
    cases ha0 : v2 c <;> cases ha1 : v403 c <;> cases ha2 : v404 c <;> simp [ClauseSat, litVal, assignment_2, assignment_404, assignment_405, v405, ha0, ha1, ha2]
  have hc2279 : ClauseSat (assignment c) [4,811,806,808] := by
    cases ha0 : v2 c <;> cases ha1 : v403 c <;> cases ha2 : v404 c <;> simp [ClauseSat, litVal, assignment_2, assignment_403, assignment_404, assignment_405, v405, ha0, ha1, ha2]
  have hc2280 : ClauseSat (assignment c) [37,813] := by
    by_cases hs : c.a1.val = 0
    · simp [ClauseSat, litVal, assignment_18, assignment_406, v406, v18, hs]
    · simp [ClauseSat, litVal, assignment_18, assignment_406, v18, hs]
  have hc2281 : ClauseSat (assignment c) [39,812] := by
    by_cases hs : c.a1.val = 1
    · simp [ClauseSat, litVal, assignment_19, assignment_406, v406, v19, hs]
    · simp [ClauseSat, litVal, assignment_19, assignment_406, v19, hs]
  have hc2282 : ClauseSat (assignment c) [41,813] := by
    by_cases hs : c.a1.val = 2
    · simp [ClauseSat, litVal, assignment_20, assignment_406, v406, v20, hs]
    · simp [ClauseSat, litVal, assignment_20, assignment_406, v20, hs]
  have hc2283 : ClauseSat (assignment c) [43,813] := by
    by_cases hs : c.a1.val = 3
    · simp [ClauseSat, litVal, assignment_21, assignment_406, v406, v21, hs]
    · simp [ClauseSat, litVal, assignment_21, assignment_406, v21, hs]
  have hc2284 : ClauseSat (assignment c) [45,813,810] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_405, assignment_406, v406, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_405, assignment_406, v22, hs]
  have hc2285 : ClauseSat (assignment c) [45,812,811] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_405, assignment_406, v406, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_405, assignment_406, v22, hs]
  have hc2286 : ClauseSat (assignment c) [47,815] := by
    by_cases hs : c.b1.val = 0
    · simp [ClauseSat, litVal, assignment_23, assignment_407, v407, v23, hs]
    · simp [ClauseSat, litVal, assignment_23, assignment_407, v23, hs]
  have hc2287 : ClauseSat (assignment c) [49,814] := by
    by_cases hs : c.b1.val = 1
    · simp [ClauseSat, litVal, assignment_24, assignment_407, v407, v24, hs]
    · simp [ClauseSat, litVal, assignment_24, assignment_407, v24, hs]
  have hc2288 : ClauseSat (assignment c) [51,815] := by
    by_cases hs : c.b1.val = 2
    · simp [ClauseSat, litVal, assignment_25, assignment_407, v407, v25, hs]
    · simp [ClauseSat, litVal, assignment_25, assignment_407, v25, hs]
  have hc2289 : ClauseSat (assignment c) [53,815] := by
    by_cases hs : c.b1.val = 3
    · simp [ClauseSat, litVal, assignment_26, assignment_407, v407, v26, hs]
    · simp [ClauseSat, litVal, assignment_26, assignment_407, v26, hs]
  have hc2290 : ClauseSat (assignment c) [55,815,810] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_405, assignment_407, v407, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_405, assignment_407, v27, hs]
  have hc2291 : ClauseSat (assignment c) [55,814,811] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_405, assignment_407, v407, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_405, assignment_407, v27, hs]
  have hc2292 : ClauseSat (assignment c) [35,817,812] := by
    cases ha0 : v17 c <;> cases ha1 : v406 c <;> cases ha2 : v407 c <;> simp [ClauseSat, litVal, assignment_17, assignment_406, assignment_408, v408, ha0, ha1, ha2]
  have hc2293 : ClauseSat (assignment c) [35,817,814] := by
    cases ha0 : v17 c <;> cases ha1 : v406 c <;> cases ha2 : v407 c <;> simp [ClauseSat, litVal, assignment_17, assignment_407, assignment_408, v408, ha0, ha1, ha2]
  have hc2294 : ClauseSat (assignment c) [35,816,813,815] := by
    cases ha0 : v17 c <;> cases ha1 : v406 c <;> cases ha2 : v407 c <;> simp [ClauseSat, litVal, assignment_17, assignment_406, assignment_407, assignment_408, v408, ha0, ha1, ha2]
  have hc2295 : ClauseSat (assignment c) [34,816,813] := by
    cases ha0 : v17 c <;> cases ha1 : v406 c <;> cases ha2 : v407 c <;> simp [ClauseSat, litVal, assignment_17, assignment_406, assignment_408, v408, ha0, ha1, ha2]
  have hc2296 : ClauseSat (assignment c) [34,816,815] := by
    cases ha0 : v17 c <;> cases ha1 : v406 c <;> cases ha2 : v407 c <;> simp [ClauseSat, litVal, assignment_17, assignment_407, assignment_408, v408, ha0, ha1, ha2]
  have hc2297 : ClauseSat (assignment c) [34,817,812,814] := by
    cases ha0 : v17 c <;> cases ha1 : v406 c <;> cases ha2 : v407 c <;> simp [ClauseSat, litVal, assignment_17, assignment_406, assignment_407, assignment_408, v408, ha0, ha1, ha2]
  have hc2298 : ClauseSat (assignment c) [75,819] := by
    by_cases hs : c.a2.val = 0
    · simp [ClauseSat, litVal, assignment_37, assignment_409, v409, v37, hs]
    · simp [ClauseSat, litVal, assignment_37, assignment_409, v37, hs]
  have hc2299 : ClauseSat (assignment c) [77,818] := by
    by_cases hs : c.a2.val = 1
    · simp [ClauseSat, litVal, assignment_38, assignment_409, v409, v38, hs]
    · simp [ClauseSat, litVal, assignment_38, assignment_409, v38, hs]
  simp only [chunk22, List.forall_mem_cons]
  exact ⟨hc2200, hc2201, hc2202, hc2203, hc2204, hc2205, hc2206, hc2207, hc2208, hc2209, hc2210, hc2211, hc2212, hc2213, hc2214, hc2215, hc2216, hc2217, hc2218, hc2219, hc2220, hc2221, hc2222, hc2223, hc2224, hc2225, hc2226, hc2227, hc2228, hc2229, hc2230, hc2231, hc2232, hc2233, hc2234, hc2235, hc2236, hc2237, hc2238, hc2239, hc2240, hc2241, hc2242, hc2243, hc2244, hc2245, hc2246, hc2247, hc2248, hc2249, hc2250, hc2251, hc2252, hc2253, hc2254, hc2255, hc2256, hc2257, hc2258, hc2259, hc2260, hc2261, hc2262, hc2263, hc2264, hc2265, hc2266, hc2267, hc2268, hc2269, hc2270, hc2271, hc2272, hc2273, hc2274, hc2275, hc2276, hc2277, hc2278, hc2279, hc2280, hc2281, hc2282, hc2283, hc2284, hc2285, hc2286, hc2287, hc2288, hc2289, hc2290, hc2291, hc2292, hc2293, hc2294, hc2295, hc2296, hc2297, hc2298, hc2299, by simp⟩
#check satChunk22

def chunk23 : List (List Nat) := [[79, 819], [81, 819], [83, 819, 810], [83, 818, 811], [85, 819, 816], [85, 818, 817], [87, 821], [89, 820], [91, 821], [93, 821], [95, 821, 810], [95, 820, 811], [97, 821, 816], [97, 820, 817], [73, 823, 818], [73, 823, 820], [73, 822, 819, 821], [72, 822, 819], [72, 822, 821], [72, 823, 818, 820], [121, 825], [123, 824], [125, 825], [127, 825], [129, 825, 810], [129, 824, 811], [131, 825, 816], [131, 824, 817], [133, 825, 822], [133, 824, 823], [135, 827], [137, 826], [139, 827], [141, 827], [143, 827, 810], [143, 826, 811], [145, 827, 816], [145, 826, 817], [147, 827, 822], [147, 826, 823], [119, 829, 824], [119, 829, 826], [119, 828, 825, 827], [118, 828, 825], [118, 828, 827], [118, 829, 824, 826], [175, 831], [177, 830], [179, 831], [181, 831], [183, 831, 810], [183, 830, 811], [185, 831, 816], [185, 830, 817], [187, 831, 822], [187, 830, 823], [189, 831, 828], [189, 830, 829], [191, 833], [193, 832], [195, 833], [197, 833], [199, 833, 810], [199, 832, 811], [201, 833, 816], [201, 832, 817], [203, 833, 822], [203, 832, 823], [205, 833, 828], [205, 832, 829], [173, 835, 830], [173, 835, 832], [173, 834, 831, 833], [172, 834, 831], [172, 834, 833], [172, 835, 830, 832], [7, 836], [9, 837], [11, 837], [13, 837], [15, 838], [17, 839], [19, 839], [21, 839], [841, 806], [841, 838], [840, 807, 839], [843, 836], [843, 808], [842, 837, 809], [845, 841], [845, 843], [844, 840, 842], [847, 837], [847, 839], [846, 836, 838], [5, 849, 845], [5, 848, 844], [4, 849, 847], [4, 848, 846]]
theorem satChunk23 (c : Candidate) (hv : valid c)
    (hr : ∀ r : Fin 16, output c r = target r)
    (hl : derivativeLeft c = false) (hd : derivativeRight c = false) :
    ∀ cl ∈ chunk23, ClauseSat (assignment c) cl := by
  rcases hv with ⟨h0, h1, h2, h3, h4⟩
  have hc2300 : ClauseSat (assignment c) [79,819] := by
    by_cases hs : c.a2.val = 2
    · simp [ClauseSat, litVal, assignment_39, assignment_409, v409, v39, hs]
    · simp [ClauseSat, litVal, assignment_39, assignment_409, v39, hs]
  have hc2301 : ClauseSat (assignment c) [81,819] := by
    by_cases hs : c.a2.val = 3
    · simp [ClauseSat, litVal, assignment_40, assignment_409, v409, v40, hs]
    · simp [ClauseSat, litVal, assignment_40, assignment_409, v40, hs]
  have hc2302 : ClauseSat (assignment c) [83,819,810] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_405, assignment_409, v409, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_405, assignment_409, v41, hs]
  have hc2303 : ClauseSat (assignment c) [83,818,811] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_405, assignment_409, v409, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_405, assignment_409, v41, hs]
  have hc2304 : ClauseSat (assignment c) [85,819,816] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_408, assignment_409, v409, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_408, assignment_409, v42, hs]
  have hc2305 : ClauseSat (assignment c) [85,818,817] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_408, assignment_409, v409, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_408, assignment_409, v42, hs]
  have hc2306 : ClauseSat (assignment c) [87,821] := by
    by_cases hs : c.b2.val = 0
    · simp [ClauseSat, litVal, assignment_43, assignment_410, v410, v43, hs]
    · simp [ClauseSat, litVal, assignment_43, assignment_410, v43, hs]
  have hc2307 : ClauseSat (assignment c) [89,820] := by
    by_cases hs : c.b2.val = 1
    · simp [ClauseSat, litVal, assignment_44, assignment_410, v410, v44, hs]
    · simp [ClauseSat, litVal, assignment_44, assignment_410, v44, hs]
  have hc2308 : ClauseSat (assignment c) [91,821] := by
    by_cases hs : c.b2.val = 2
    · simp [ClauseSat, litVal, assignment_45, assignment_410, v410, v45, hs]
    · simp [ClauseSat, litVal, assignment_45, assignment_410, v45, hs]
  have hc2309 : ClauseSat (assignment c) [93,821] := by
    by_cases hs : c.b2.val = 3
    · simp [ClauseSat, litVal, assignment_46, assignment_410, v410, v46, hs]
    · simp [ClauseSat, litVal, assignment_46, assignment_410, v46, hs]
  have hc2310 : ClauseSat (assignment c) [95,821,810] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_405, assignment_410, v410, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_405, assignment_410, v47, hs]
  have hc2311 : ClauseSat (assignment c) [95,820,811] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_405, assignment_410, v410, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_405, assignment_410, v47, hs]
  have hc2312 : ClauseSat (assignment c) [97,821,816] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_408, assignment_410, v410, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_408, assignment_410, v48, hs]
  have hc2313 : ClauseSat (assignment c) [97,820,817] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_408, assignment_410, v410, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_408, assignment_410, v48, hs]
  have hc2314 : ClauseSat (assignment c) [73,823,818] := by
    cases ha0 : v36 c <;> cases ha1 : v409 c <;> cases ha2 : v410 c <;> simp [ClauseSat, litVal, assignment_36, assignment_409, assignment_411, v411, ha0, ha1, ha2]
  have hc2315 : ClauseSat (assignment c) [73,823,820] := by
    cases ha0 : v36 c <;> cases ha1 : v409 c <;> cases ha2 : v410 c <;> simp [ClauseSat, litVal, assignment_36, assignment_410, assignment_411, v411, ha0, ha1, ha2]
  have hc2316 : ClauseSat (assignment c) [73,822,819,821] := by
    cases ha0 : v36 c <;> cases ha1 : v409 c <;> cases ha2 : v410 c <;> simp [ClauseSat, litVal, assignment_36, assignment_409, assignment_410, assignment_411, v411, ha0, ha1, ha2]
  have hc2317 : ClauseSat (assignment c) [72,822,819] := by
    cases ha0 : v36 c <;> cases ha1 : v409 c <;> cases ha2 : v410 c <;> simp [ClauseSat, litVal, assignment_36, assignment_409, assignment_411, v411, ha0, ha1, ha2]
  have hc2318 : ClauseSat (assignment c) [72,822,821] := by
    cases ha0 : v36 c <;> cases ha1 : v409 c <;> cases ha2 : v410 c <;> simp [ClauseSat, litVal, assignment_36, assignment_410, assignment_411, v411, ha0, ha1, ha2]
  have hc2319 : ClauseSat (assignment c) [72,823,818,820] := by
    cases ha0 : v36 c <;> cases ha1 : v409 c <;> cases ha2 : v410 c <;> simp [ClauseSat, litVal, assignment_36, assignment_409, assignment_410, assignment_411, v411, ha0, ha1, ha2]
  have hc2320 : ClauseSat (assignment c) [121,825] := by
    by_cases hs : c.a3.val = 0
    · simp [ClauseSat, litVal, assignment_60, assignment_412, v412, v60, hs]
    · simp [ClauseSat, litVal, assignment_60, assignment_412, v60, hs]
  have hc2321 : ClauseSat (assignment c) [123,824] := by
    by_cases hs : c.a3.val = 1
    · simp [ClauseSat, litVal, assignment_61, assignment_412, v412, v61, hs]
    · simp [ClauseSat, litVal, assignment_61, assignment_412, v61, hs]
  have hc2322 : ClauseSat (assignment c) [125,825] := by
    by_cases hs : c.a3.val = 2
    · simp [ClauseSat, litVal, assignment_62, assignment_412, v412, v62, hs]
    · simp [ClauseSat, litVal, assignment_62, assignment_412, v62, hs]
  have hc2323 : ClauseSat (assignment c) [127,825] := by
    by_cases hs : c.a3.val = 3
    · simp [ClauseSat, litVal, assignment_63, assignment_412, v412, v63, hs]
    · simp [ClauseSat, litVal, assignment_63, assignment_412, v63, hs]
  have hc2324 : ClauseSat (assignment c) [129,825,810] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_405, assignment_412, v412, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_405, assignment_412, v64, hs]
  have hc2325 : ClauseSat (assignment c) [129,824,811] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_405, assignment_412, v412, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_405, assignment_412, v64, hs]
  have hc2326 : ClauseSat (assignment c) [131,825,816] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_408, assignment_412, v412, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_408, assignment_412, v65, hs]
  have hc2327 : ClauseSat (assignment c) [131,824,817] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_408, assignment_412, v412, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_408, assignment_412, v65, hs]
  have hc2328 : ClauseSat (assignment c) [133,825,822] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_411, assignment_412, v412, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_411, assignment_412, v66, hs]
  have hc2329 : ClauseSat (assignment c) [133,824,823] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_411, assignment_412, v412, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_411, assignment_412, v66, hs]
  have hc2330 : ClauseSat (assignment c) [135,827] := by
    by_cases hs : c.b3.val = 0
    · simp [ClauseSat, litVal, assignment_67, assignment_413, v413, v67, hs]
    · simp [ClauseSat, litVal, assignment_67, assignment_413, v67, hs]
  have hc2331 : ClauseSat (assignment c) [137,826] := by
    by_cases hs : c.b3.val = 1
    · simp [ClauseSat, litVal, assignment_68, assignment_413, v413, v68, hs]
    · simp [ClauseSat, litVal, assignment_68, assignment_413, v68, hs]
  have hc2332 : ClauseSat (assignment c) [139,827] := by
    by_cases hs : c.b3.val = 2
    · simp [ClauseSat, litVal, assignment_69, assignment_413, v413, v69, hs]
    · simp [ClauseSat, litVal, assignment_69, assignment_413, v69, hs]
  have hc2333 : ClauseSat (assignment c) [141,827] := by
    by_cases hs : c.b3.val = 3
    · simp [ClauseSat, litVal, assignment_70, assignment_413, v413, v70, hs]
    · simp [ClauseSat, litVal, assignment_70, assignment_413, v70, hs]
  have hc2334 : ClauseSat (assignment c) [143,827,810] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_405, assignment_413, v413, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_405, assignment_413, v71, hs]
  have hc2335 : ClauseSat (assignment c) [143,826,811] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_405, assignment_413, v413, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_405, assignment_413, v71, hs]
  have hc2336 : ClauseSat (assignment c) [145,827,816] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_408, assignment_413, v413, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_408, assignment_413, v72, hs]
  have hc2337 : ClauseSat (assignment c) [145,826,817] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_408, assignment_413, v413, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_408, assignment_413, v72, hs]
  have hc2338 : ClauseSat (assignment c) [147,827,822] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_411, assignment_413, v413, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_411, assignment_413, v73, hs]
  have hc2339 : ClauseSat (assignment c) [147,826,823] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_411, assignment_413, v413, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_411, assignment_413, v73, hs]
  have hc2340 : ClauseSat (assignment c) [119,829,824] := by
    cases ha0 : v59 c <;> cases ha1 : v412 c <;> cases ha2 : v413 c <;> simp [ClauseSat, litVal, assignment_59, assignment_412, assignment_414, v414, ha0, ha1, ha2]
  have hc2341 : ClauseSat (assignment c) [119,829,826] := by
    cases ha0 : v59 c <;> cases ha1 : v412 c <;> cases ha2 : v413 c <;> simp [ClauseSat, litVal, assignment_59, assignment_413, assignment_414, v414, ha0, ha1, ha2]
  have hc2342 : ClauseSat (assignment c) [119,828,825,827] := by
    cases ha0 : v59 c <;> cases ha1 : v412 c <;> cases ha2 : v413 c <;> simp [ClauseSat, litVal, assignment_59, assignment_412, assignment_413, assignment_414, v414, ha0, ha1, ha2]
  have hc2343 : ClauseSat (assignment c) [118,828,825] := by
    cases ha0 : v59 c <;> cases ha1 : v412 c <;> cases ha2 : v413 c <;> simp [ClauseSat, litVal, assignment_59, assignment_412, assignment_414, v414, ha0, ha1, ha2]
  have hc2344 : ClauseSat (assignment c) [118,828,827] := by
    cases ha0 : v59 c <;> cases ha1 : v412 c <;> cases ha2 : v413 c <;> simp [ClauseSat, litVal, assignment_59, assignment_413, assignment_414, v414, ha0, ha1, ha2]
  have hc2345 : ClauseSat (assignment c) [118,829,824,826] := by
    cases ha0 : v59 c <;> cases ha1 : v412 c <;> cases ha2 : v413 c <;> simp [ClauseSat, litVal, assignment_59, assignment_412, assignment_413, assignment_414, v414, ha0, ha1, ha2]
  have hc2346 : ClauseSat (assignment c) [175,831] := by
    by_cases hs : c.a4.val = 0
    · simp [ClauseSat, litVal, assignment_87, assignment_415, v415, v87, hs]
    · simp [ClauseSat, litVal, assignment_87, assignment_415, v87, hs]
  have hc2347 : ClauseSat (assignment c) [177,830] := by
    by_cases hs : c.a4.val = 1
    · simp [ClauseSat, litVal, assignment_88, assignment_415, v415, v88, hs]
    · simp [ClauseSat, litVal, assignment_88, assignment_415, v88, hs]
  have hc2348 : ClauseSat (assignment c) [179,831] := by
    by_cases hs : c.a4.val = 2
    · simp [ClauseSat, litVal, assignment_89, assignment_415, v415, v89, hs]
    · simp [ClauseSat, litVal, assignment_89, assignment_415, v89, hs]
  have hc2349 : ClauseSat (assignment c) [181,831] := by
    by_cases hs : c.a4.val = 3
    · simp [ClauseSat, litVal, assignment_90, assignment_415, v415, v90, hs]
    · simp [ClauseSat, litVal, assignment_90, assignment_415, v90, hs]
  have hc2350 : ClauseSat (assignment c) [183,831,810] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_405, assignment_415, v415, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_405, assignment_415, v91, hs]
  have hc2351 : ClauseSat (assignment c) [183,830,811] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_405, assignment_415, v415, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_405, assignment_415, v91, hs]
  have hc2352 : ClauseSat (assignment c) [185,831,816] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_408, assignment_415, v415, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_408, assignment_415, v92, hs]
  have hc2353 : ClauseSat (assignment c) [185,830,817] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_408, assignment_415, v415, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_408, assignment_415, v92, hs]
  have hc2354 : ClauseSat (assignment c) [187,831,822] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_411, assignment_415, v415, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_411, assignment_415, v93, hs]
  have hc2355 : ClauseSat (assignment c) [187,830,823] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_411, assignment_415, v415, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_411, assignment_415, v93, hs]
  have hc2356 : ClauseSat (assignment c) [189,831,828] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_414, assignment_415, v415, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_414, assignment_415, v94, hs]
  have hc2357 : ClauseSat (assignment c) [189,830,829] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_414, assignment_415, v415, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_414, assignment_415, v94, hs]
  have hc2358 : ClauseSat (assignment c) [191,833] := by
    by_cases hs : c.b4.val = 0
    · simp [ClauseSat, litVal, assignment_95, assignment_416, v416, v95, hs]
    · simp [ClauseSat, litVal, assignment_95, assignment_416, v95, hs]
  have hc2359 : ClauseSat (assignment c) [193,832] := by
    by_cases hs : c.b4.val = 1
    · simp [ClauseSat, litVal, assignment_96, assignment_416, v416, v96, hs]
    · simp [ClauseSat, litVal, assignment_96, assignment_416, v96, hs]
  have hc2360 : ClauseSat (assignment c) [195,833] := by
    by_cases hs : c.b4.val = 2
    · simp [ClauseSat, litVal, assignment_97, assignment_416, v416, v97, hs]
    · simp [ClauseSat, litVal, assignment_97, assignment_416, v97, hs]
  have hc2361 : ClauseSat (assignment c) [197,833] := by
    by_cases hs : c.b4.val = 3
    · simp [ClauseSat, litVal, assignment_98, assignment_416, v416, v98, hs]
    · simp [ClauseSat, litVal, assignment_98, assignment_416, v98, hs]
  have hc2362 : ClauseSat (assignment c) [199,833,810] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_405, assignment_416, v416, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_405, assignment_416, v99, hs]
  have hc2363 : ClauseSat (assignment c) [199,832,811] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_405, assignment_416, v416, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_405, assignment_416, v99, hs]
  have hc2364 : ClauseSat (assignment c) [201,833,816] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_408, assignment_416, v416, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_408, assignment_416, v100, hs]
  have hc2365 : ClauseSat (assignment c) [201,832,817] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_408, assignment_416, v416, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_408, assignment_416, v100, hs]
  have hc2366 : ClauseSat (assignment c) [203,833,822] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_411, assignment_416, v416, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_411, assignment_416, v101, hs]
  have hc2367 : ClauseSat (assignment c) [203,832,823] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_411, assignment_416, v416, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_411, assignment_416, v101, hs]
  have hc2368 : ClauseSat (assignment c) [205,833,828] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_414, assignment_416, v416, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_414, assignment_416, v102, hs]
  have hc2369 : ClauseSat (assignment c) [205,832,829] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_414, assignment_416, v416, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_414, assignment_416, v102, hs]
  have hc2370 : ClauseSat (assignment c) [173,835,830] := by
    cases ha0 : v86 c <;> cases ha1 : v415 c <;> cases ha2 : v416 c <;> simp [ClauseSat, litVal, assignment_86, assignment_415, assignment_417, v417, ha0, ha1, ha2]
  have hc2371 : ClauseSat (assignment c) [173,835,832] := by
    cases ha0 : v86 c <;> cases ha1 : v415 c <;> cases ha2 : v416 c <;> simp [ClauseSat, litVal, assignment_86, assignment_416, assignment_417, v417, ha0, ha1, ha2]
  have hc2372 : ClauseSat (assignment c) [173,834,831,833] := by
    cases ha0 : v86 c <;> cases ha1 : v415 c <;> cases ha2 : v416 c <;> simp [ClauseSat, litVal, assignment_86, assignment_415, assignment_416, assignment_417, v417, ha0, ha1, ha2]
  have hc2373 : ClauseSat (assignment c) [172,834,831] := by
    cases ha0 : v86 c <;> cases ha1 : v415 c <;> cases ha2 : v416 c <;> simp [ClauseSat, litVal, assignment_86, assignment_415, assignment_417, v417, ha0, ha1, ha2]
  have hc2374 : ClauseSat (assignment c) [172,834,833] := by
    cases ha0 : v86 c <;> cases ha1 : v415 c <;> cases ha2 : v416 c <;> simp [ClauseSat, litVal, assignment_86, assignment_416, assignment_417, v417, ha0, ha1, ha2]
  have hc2375 : ClauseSat (assignment c) [172,835,830,832] := by
    cases ha0 : v86 c <;> cases ha1 : v415 c <;> cases ha2 : v416 c <;> simp [ClauseSat, litVal, assignment_86, assignment_415, assignment_416, assignment_417, v417, ha0, ha1, ha2]
  have hc2376 : ClauseSat (assignment c) [7,836] := by
    by_cases hs : c.a0.val = 0
    · simp [ClauseSat, litVal, assignment_3, assignment_418, v418, v3, hs]
    · simp [ClauseSat, litVal, assignment_3, assignment_418, v3, hs]
  have hc2377 : ClauseSat (assignment c) [9,837] := by
    by_cases hs : c.a0.val = 1
    · simp [ClauseSat, litVal, assignment_4, assignment_418, v418, v4, hs]
    · simp [ClauseSat, litVal, assignment_4, assignment_418, v4, hs]
  have hc2378 : ClauseSat (assignment c) [11,837] := by
    by_cases hs : c.a0.val = 2
    · simp [ClauseSat, litVal, assignment_5, assignment_418, v418, v5, hs]
    · simp [ClauseSat, litVal, assignment_5, assignment_418, v5, hs]
  have hc2379 : ClauseSat (assignment c) [13,837] := by
    by_cases hs : c.a0.val = 3
    · simp [ClauseSat, litVal, assignment_6, assignment_418, v418, v6, hs]
    · simp [ClauseSat, litVal, assignment_6, assignment_418, v6, hs]
  have hc2380 : ClauseSat (assignment c) [15,838] := by
    by_cases hs : c.b0.val = 0
    · simp [ClauseSat, litVal, assignment_7, assignment_419, v419, v7, hs]
    · simp [ClauseSat, litVal, assignment_7, assignment_419, v7, hs]
  have hc2381 : ClauseSat (assignment c) [17,839] := by
    by_cases hs : c.b0.val = 1
    · simp [ClauseSat, litVal, assignment_8, assignment_419, v419, v8, hs]
    · simp [ClauseSat, litVal, assignment_8, assignment_419, v8, hs]
  have hc2382 : ClauseSat (assignment c) [19,839] := by
    by_cases hs : c.b0.val = 2
    · simp [ClauseSat, litVal, assignment_9, assignment_419, v419, v9, hs]
    · simp [ClauseSat, litVal, assignment_9, assignment_419, v9, hs]
  have hc2383 : ClauseSat (assignment c) [21,839] := by
    by_cases hs : c.b0.val = 3
    · simp [ClauseSat, litVal, assignment_10, assignment_419, v419, v10, hs]
    · simp [ClauseSat, litVal, assignment_10, assignment_419, v10, hs]
  have hc2384 : ClauseSat (assignment c) [841,806] := by
    cases ha0 : v403 c <;> cases ha1 : v419 c <;> simp [ClauseSat, litVal, assignment_403, assignment_420, v420, ha0, ha1]
  have hc2385 : ClauseSat (assignment c) [841,838] := by
    cases ha0 : v403 c <;> cases ha1 : v419 c <;> simp [ClauseSat, litVal, assignment_419, assignment_420, v420, ha0, ha1]
  have hc2386 : ClauseSat (assignment c) [840,807,839] := by
    cases ha0 : v403 c <;> cases ha1 : v419 c <;> simp [ClauseSat, litVal, assignment_403, assignment_419, assignment_420, v420, ha0, ha1]
  have hc2387 : ClauseSat (assignment c) [843,836] := by
    cases ha0 : v404 c <;> cases ha1 : v418 c <;> simp [ClauseSat, litVal, assignment_418, assignment_421, v421, ha0, ha1]
  have hc2388 : ClauseSat (assignment c) [843,808] := by
    cases ha0 : v404 c <;> cases ha1 : v418 c <;> simp [ClauseSat, litVal, assignment_404, assignment_421, v421, ha0, ha1]
  have hc2389 : ClauseSat (assignment c) [842,837,809] := by
    cases ha0 : v404 c <;> cases ha1 : v418 c <;> simp [ClauseSat, litVal, assignment_404, assignment_418, assignment_421, v421, ha0, ha1]
  have hc2390 : ClauseSat (assignment c) [845,841] := by
    cases ha0 : v420 c <;> cases ha1 : v421 c <;> simp [ClauseSat, litVal, assignment_420, assignment_422, v422, ha0, ha1]
  have hc2391 : ClauseSat (assignment c) [845,843] := by
    cases ha0 : v420 c <;> cases ha1 : v421 c <;> simp [ClauseSat, litVal, assignment_421, assignment_422, v422, ha0, ha1]
  have hc2392 : ClauseSat (assignment c) [844,840,842] := by
    cases ha0 : v420 c <;> cases ha1 : v421 c <;> simp [ClauseSat, litVal, assignment_420, assignment_421, assignment_422, v422, ha0, ha1]
  have hc2393 : ClauseSat (assignment c) [847,837] := by
    cases ha0 : v418 c <;> cases ha1 : v419 c <;> simp [ClauseSat, litVal, assignment_418, assignment_423, v423, ha0, ha1]
  have hc2394 : ClauseSat (assignment c) [847,839] := by
    cases ha0 : v418 c <;> cases ha1 : v419 c <;> simp [ClauseSat, litVal, assignment_419, assignment_423, v423, ha0, ha1]
  have hc2395 : ClauseSat (assignment c) [846,836,838] := by
    cases ha0 : v418 c <;> cases ha1 : v419 c <;> simp [ClauseSat, litVal, assignment_418, assignment_419, assignment_423, v423, ha0, ha1]
  have hc2396 : ClauseSat (assignment c) [5,849,845] := by
    cases ha0 : v2 c <;> cases ha1 : v422 c <;> cases ha2 : v423 c <;> simp [ClauseSat, litVal, assignment_2, assignment_422, assignment_424, v424, ha0, ha1, ha2]
  have hc2397 : ClauseSat (assignment c) [5,848,844] := by
    cases ha0 : v2 c <;> cases ha1 : v422 c <;> cases ha2 : v423 c <;> simp [ClauseSat, litVal, assignment_2, assignment_422, assignment_424, v424, ha0, ha1, ha2]
  have hc2398 : ClauseSat (assignment c) [4,849,847] := by
    cases ha0 : v2 c <;> cases ha1 : v422 c <;> cases ha2 : v423 c <;> simp [ClauseSat, litVal, assignment_2, assignment_423, assignment_424, v424, ha0, ha1, ha2]
  have hc2399 : ClauseSat (assignment c) [4,848,846] := by
    cases ha0 : v2 c <;> cases ha1 : v422 c <;> cases ha2 : v423 c <;> simp [ClauseSat, litVal, assignment_2, assignment_423, assignment_424, v424, ha0, ha1, ha2]
  simp only [chunk23, List.forall_mem_cons]
  exact ⟨hc2300, hc2301, hc2302, hc2303, hc2304, hc2305, hc2306, hc2307, hc2308, hc2309, hc2310, hc2311, hc2312, hc2313, hc2314, hc2315, hc2316, hc2317, hc2318, hc2319, hc2320, hc2321, hc2322, hc2323, hc2324, hc2325, hc2326, hc2327, hc2328, hc2329, hc2330, hc2331, hc2332, hc2333, hc2334, hc2335, hc2336, hc2337, hc2338, hc2339, hc2340, hc2341, hc2342, hc2343, hc2344, hc2345, hc2346, hc2347, hc2348, hc2349, hc2350, hc2351, hc2352, hc2353, hc2354, hc2355, hc2356, hc2357, hc2358, hc2359, hc2360, hc2361, hc2362, hc2363, hc2364, hc2365, hc2366, hc2367, hc2368, hc2369, hc2370, hc2371, hc2372, hc2373, hc2374, hc2375, hc2376, hc2377, hc2378, hc2379, hc2380, hc2381, hc2382, hc2383, hc2384, hc2385, hc2386, hc2387, hc2388, hc2389, hc2390, hc2391, hc2392, hc2393, hc2394, hc2395, hc2396, hc2397, hc2398, hc2399, by simp⟩
#check satChunk23

def chunk24 : List (List Nat) := [[37, 850], [39, 851], [41, 851], [43, 851], [45, 851, 848], [45, 850, 849], [47, 852], [49, 853], [51, 853], [53, 853], [55, 853, 848], [55, 852, 849], [855, 812], [855, 852], [854, 813, 853], [857, 850], [857, 814], [856, 851, 815], [859, 855], [859, 857], [858, 854, 856], [861, 851], [861, 853], [860, 850, 852], [35, 863, 859], [35, 862, 858], [34, 863, 861], [34, 862, 860], [75, 864], [77, 865], [79, 865], [81, 865], [83, 865, 848], [83, 864, 849], [85, 865, 862], [85, 864, 863], [87, 866], [89, 867], [91, 867], [93, 867], [95, 867, 848], [95, 866, 849], [97, 867, 862], [97, 866, 863], [869, 818], [869, 866], [868, 819, 867], [871, 864], [871, 820], [870, 865, 821], [873, 869], [873, 871], [872, 868, 870], [875, 865], [875, 867], [874, 864, 866], [73, 877, 873], [73, 876, 872], [72, 877, 875], [72, 876, 874], [121, 878], [123, 879], [125, 879], [127, 879], [129, 879, 848], [129, 878, 849], [131, 879, 862], [131, 878, 863], [133, 879, 876], [133, 878, 877], [135, 880], [137, 881], [139, 881], [141, 881], [143, 881, 848], [143, 880, 849], [145, 881, 862], [145, 880, 863], [147, 881, 876], [147, 880, 877], [883, 824], [883, 880], [882, 825, 881], [885, 878], [885, 826], [884, 879, 827], [887, 883], [887, 885], [886, 882, 884], [889, 879], [889, 881], [888, 878, 880], [119, 891, 887], [119, 890, 886], [118, 891, 889], [118, 890, 888], [175, 892], [177, 893], [179, 893], [181, 893]]
theorem satChunk24 (c : Candidate) (hv : valid c)
    (hr : ∀ r : Fin 16, output c r = target r)
    (hl : derivativeLeft c = false) (hd : derivativeRight c = false) :
    ∀ cl ∈ chunk24, ClauseSat (assignment c) cl := by
  rcases hv with ⟨h0, h1, h2, h3, h4⟩
  have hc2400 : ClauseSat (assignment c) [37,850] := by
    by_cases hs : c.a1.val = 0
    · simp [ClauseSat, litVal, assignment_18, assignment_425, v425, v18, hs]
    · simp [ClauseSat, litVal, assignment_18, assignment_425, v18, hs]
  have hc2401 : ClauseSat (assignment c) [39,851] := by
    by_cases hs : c.a1.val = 1
    · simp [ClauseSat, litVal, assignment_19, assignment_425, v425, v19, hs]
    · simp [ClauseSat, litVal, assignment_19, assignment_425, v19, hs]
  have hc2402 : ClauseSat (assignment c) [41,851] := by
    by_cases hs : c.a1.val = 2
    · simp [ClauseSat, litVal, assignment_20, assignment_425, v425, v20, hs]
    · simp [ClauseSat, litVal, assignment_20, assignment_425, v20, hs]
  have hc2403 : ClauseSat (assignment c) [43,851] := by
    by_cases hs : c.a1.val = 3
    · simp [ClauseSat, litVal, assignment_21, assignment_425, v425, v21, hs]
    · simp [ClauseSat, litVal, assignment_21, assignment_425, v21, hs]
  have hc2404 : ClauseSat (assignment c) [45,851,848] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_424, assignment_425, v425, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_424, assignment_425, v22, hs]
  have hc2405 : ClauseSat (assignment c) [45,850,849] := by
    by_cases hs : c.a1.val = 4
    · simp [ClauseSat, litVal, assignment_22, assignment_424, assignment_425, v425, v22, hs]
    · simp [ClauseSat, litVal, assignment_22, assignment_424, assignment_425, v22, hs]
  have hc2406 : ClauseSat (assignment c) [47,852] := by
    by_cases hs : c.b1.val = 0
    · simp [ClauseSat, litVal, assignment_23, assignment_426, v426, v23, hs]
    · simp [ClauseSat, litVal, assignment_23, assignment_426, v23, hs]
  have hc2407 : ClauseSat (assignment c) [49,853] := by
    by_cases hs : c.b1.val = 1
    · simp [ClauseSat, litVal, assignment_24, assignment_426, v426, v24, hs]
    · simp [ClauseSat, litVal, assignment_24, assignment_426, v24, hs]
  have hc2408 : ClauseSat (assignment c) [51,853] := by
    by_cases hs : c.b1.val = 2
    · simp [ClauseSat, litVal, assignment_25, assignment_426, v426, v25, hs]
    · simp [ClauseSat, litVal, assignment_25, assignment_426, v25, hs]
  have hc2409 : ClauseSat (assignment c) [53,853] := by
    by_cases hs : c.b1.val = 3
    · simp [ClauseSat, litVal, assignment_26, assignment_426, v426, v26, hs]
    · simp [ClauseSat, litVal, assignment_26, assignment_426, v26, hs]
  have hc2410 : ClauseSat (assignment c) [55,853,848] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_424, assignment_426, v426, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_424, assignment_426, v27, hs]
  have hc2411 : ClauseSat (assignment c) [55,852,849] := by
    by_cases hs : c.b1.val = 4
    · simp [ClauseSat, litVal, assignment_27, assignment_424, assignment_426, v426, v27, hs]
    · simp [ClauseSat, litVal, assignment_27, assignment_424, assignment_426, v27, hs]
  have hc2412 : ClauseSat (assignment c) [855,812] := by
    cases ha0 : v406 c <;> cases ha1 : v426 c <;> simp [ClauseSat, litVal, assignment_406, assignment_427, v427, ha0, ha1]
  have hc2413 : ClauseSat (assignment c) [855,852] := by
    cases ha0 : v406 c <;> cases ha1 : v426 c <;> simp [ClauseSat, litVal, assignment_426, assignment_427, v427, ha0, ha1]
  have hc2414 : ClauseSat (assignment c) [854,813,853] := by
    cases ha0 : v406 c <;> cases ha1 : v426 c <;> simp [ClauseSat, litVal, assignment_406, assignment_426, assignment_427, v427, ha0, ha1]
  have hc2415 : ClauseSat (assignment c) [857,850] := by
    cases ha0 : v407 c <;> cases ha1 : v425 c <;> simp [ClauseSat, litVal, assignment_425, assignment_428, v428, ha0, ha1]
  have hc2416 : ClauseSat (assignment c) [857,814] := by
    cases ha0 : v407 c <;> cases ha1 : v425 c <;> simp [ClauseSat, litVal, assignment_407, assignment_428, v428, ha0, ha1]
  have hc2417 : ClauseSat (assignment c) [856,851,815] := by
    cases ha0 : v407 c <;> cases ha1 : v425 c <;> simp [ClauseSat, litVal, assignment_407, assignment_425, assignment_428, v428, ha0, ha1]
  have hc2418 : ClauseSat (assignment c) [859,855] := by
    cases ha0 : v427 c <;> cases ha1 : v428 c <;> simp [ClauseSat, litVal, assignment_427, assignment_429, v429, ha0, ha1]
  have hc2419 : ClauseSat (assignment c) [859,857] := by
    cases ha0 : v427 c <;> cases ha1 : v428 c <;> simp [ClauseSat, litVal, assignment_428, assignment_429, v429, ha0, ha1]
  have hc2420 : ClauseSat (assignment c) [858,854,856] := by
    cases ha0 : v427 c <;> cases ha1 : v428 c <;> simp [ClauseSat, litVal, assignment_427, assignment_428, assignment_429, v429, ha0, ha1]
  have hc2421 : ClauseSat (assignment c) [861,851] := by
    cases ha0 : v425 c <;> cases ha1 : v426 c <;> simp [ClauseSat, litVal, assignment_425, assignment_430, v430, ha0, ha1]
  have hc2422 : ClauseSat (assignment c) [861,853] := by
    cases ha0 : v425 c <;> cases ha1 : v426 c <;> simp [ClauseSat, litVal, assignment_426, assignment_430, v430, ha0, ha1]
  have hc2423 : ClauseSat (assignment c) [860,850,852] := by
    cases ha0 : v425 c <;> cases ha1 : v426 c <;> simp [ClauseSat, litVal, assignment_425, assignment_426, assignment_430, v430, ha0, ha1]
  have hc2424 : ClauseSat (assignment c) [35,863,859] := by
    cases ha0 : v17 c <;> cases ha1 : v429 c <;> cases ha2 : v430 c <;> simp [ClauseSat, litVal, assignment_17, assignment_429, assignment_431, v431, ha0, ha1, ha2]
  have hc2425 : ClauseSat (assignment c) [35,862,858] := by
    cases ha0 : v17 c <;> cases ha1 : v429 c <;> cases ha2 : v430 c <;> simp [ClauseSat, litVal, assignment_17, assignment_429, assignment_431, v431, ha0, ha1, ha2]
  have hc2426 : ClauseSat (assignment c) [34,863,861] := by
    cases ha0 : v17 c <;> cases ha1 : v429 c <;> cases ha2 : v430 c <;> simp [ClauseSat, litVal, assignment_17, assignment_430, assignment_431, v431, ha0, ha1, ha2]
  have hc2427 : ClauseSat (assignment c) [34,862,860] := by
    cases ha0 : v17 c <;> cases ha1 : v429 c <;> cases ha2 : v430 c <;> simp [ClauseSat, litVal, assignment_17, assignment_430, assignment_431, v431, ha0, ha1, ha2]
  have hc2428 : ClauseSat (assignment c) [75,864] := by
    by_cases hs : c.a2.val = 0
    · simp [ClauseSat, litVal, assignment_37, assignment_432, v432, v37, hs]
    · simp [ClauseSat, litVal, assignment_37, assignment_432, v37, hs]
  have hc2429 : ClauseSat (assignment c) [77,865] := by
    by_cases hs : c.a2.val = 1
    · simp [ClauseSat, litVal, assignment_38, assignment_432, v432, v38, hs]
    · simp [ClauseSat, litVal, assignment_38, assignment_432, v38, hs]
  have hc2430 : ClauseSat (assignment c) [79,865] := by
    by_cases hs : c.a2.val = 2
    · simp [ClauseSat, litVal, assignment_39, assignment_432, v432, v39, hs]
    · simp [ClauseSat, litVal, assignment_39, assignment_432, v39, hs]
  have hc2431 : ClauseSat (assignment c) [81,865] := by
    by_cases hs : c.a2.val = 3
    · simp [ClauseSat, litVal, assignment_40, assignment_432, v432, v40, hs]
    · simp [ClauseSat, litVal, assignment_40, assignment_432, v40, hs]
  have hc2432 : ClauseSat (assignment c) [83,865,848] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_424, assignment_432, v432, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_424, assignment_432, v41, hs]
  have hc2433 : ClauseSat (assignment c) [83,864,849] := by
    by_cases hs : c.a2.val = 4
    · simp [ClauseSat, litVal, assignment_41, assignment_424, assignment_432, v432, v41, hs]
    · simp [ClauseSat, litVal, assignment_41, assignment_424, assignment_432, v41, hs]
  have hc2434 : ClauseSat (assignment c) [85,865,862] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_431, assignment_432, v432, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_431, assignment_432, v42, hs]
  have hc2435 : ClauseSat (assignment c) [85,864,863] := by
    by_cases hs : c.a2.val = 5
    · simp [ClauseSat, litVal, assignment_42, assignment_431, assignment_432, v432, v42, hs]
    · simp [ClauseSat, litVal, assignment_42, assignment_431, assignment_432, v42, hs]
  have hc2436 : ClauseSat (assignment c) [87,866] := by
    by_cases hs : c.b2.val = 0
    · simp [ClauseSat, litVal, assignment_43, assignment_433, v433, v43, hs]
    · simp [ClauseSat, litVal, assignment_43, assignment_433, v43, hs]
  have hc2437 : ClauseSat (assignment c) [89,867] := by
    by_cases hs : c.b2.val = 1
    · simp [ClauseSat, litVal, assignment_44, assignment_433, v433, v44, hs]
    · simp [ClauseSat, litVal, assignment_44, assignment_433, v44, hs]
  have hc2438 : ClauseSat (assignment c) [91,867] := by
    by_cases hs : c.b2.val = 2
    · simp [ClauseSat, litVal, assignment_45, assignment_433, v433, v45, hs]
    · simp [ClauseSat, litVal, assignment_45, assignment_433, v45, hs]
  have hc2439 : ClauseSat (assignment c) [93,867] := by
    by_cases hs : c.b2.val = 3
    · simp [ClauseSat, litVal, assignment_46, assignment_433, v433, v46, hs]
    · simp [ClauseSat, litVal, assignment_46, assignment_433, v46, hs]
  have hc2440 : ClauseSat (assignment c) [95,867,848] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_424, assignment_433, v433, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_424, assignment_433, v47, hs]
  have hc2441 : ClauseSat (assignment c) [95,866,849] := by
    by_cases hs : c.b2.val = 4
    · simp [ClauseSat, litVal, assignment_47, assignment_424, assignment_433, v433, v47, hs]
    · simp [ClauseSat, litVal, assignment_47, assignment_424, assignment_433, v47, hs]
  have hc2442 : ClauseSat (assignment c) [97,867,862] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_431, assignment_433, v433, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_431, assignment_433, v48, hs]
  have hc2443 : ClauseSat (assignment c) [97,866,863] := by
    by_cases hs : c.b2.val = 5
    · simp [ClauseSat, litVal, assignment_48, assignment_431, assignment_433, v433, v48, hs]
    · simp [ClauseSat, litVal, assignment_48, assignment_431, assignment_433, v48, hs]
  have hc2444 : ClauseSat (assignment c) [869,818] := by
    cases ha0 : v409 c <;> cases ha1 : v433 c <;> simp [ClauseSat, litVal, assignment_409, assignment_434, v434, ha0, ha1]
  have hc2445 : ClauseSat (assignment c) [869,866] := by
    cases ha0 : v409 c <;> cases ha1 : v433 c <;> simp [ClauseSat, litVal, assignment_433, assignment_434, v434, ha0, ha1]
  have hc2446 : ClauseSat (assignment c) [868,819,867] := by
    cases ha0 : v409 c <;> cases ha1 : v433 c <;> simp [ClauseSat, litVal, assignment_409, assignment_433, assignment_434, v434, ha0, ha1]
  have hc2447 : ClauseSat (assignment c) [871,864] := by
    cases ha0 : v410 c <;> cases ha1 : v432 c <;> simp [ClauseSat, litVal, assignment_432, assignment_435, v435, ha0, ha1]
  have hc2448 : ClauseSat (assignment c) [871,820] := by
    cases ha0 : v410 c <;> cases ha1 : v432 c <;> simp [ClauseSat, litVal, assignment_410, assignment_435, v435, ha0, ha1]
  have hc2449 : ClauseSat (assignment c) [870,865,821] := by
    cases ha0 : v410 c <;> cases ha1 : v432 c <;> simp [ClauseSat, litVal, assignment_410, assignment_432, assignment_435, v435, ha0, ha1]
  have hc2450 : ClauseSat (assignment c) [873,869] := by
    cases ha0 : v434 c <;> cases ha1 : v435 c <;> simp [ClauseSat, litVal, assignment_434, assignment_436, v436, ha0, ha1]
  have hc2451 : ClauseSat (assignment c) [873,871] := by
    cases ha0 : v434 c <;> cases ha1 : v435 c <;> simp [ClauseSat, litVal, assignment_435, assignment_436, v436, ha0, ha1]
  have hc2452 : ClauseSat (assignment c) [872,868,870] := by
    cases ha0 : v434 c <;> cases ha1 : v435 c <;> simp [ClauseSat, litVal, assignment_434, assignment_435, assignment_436, v436, ha0, ha1]
  have hc2453 : ClauseSat (assignment c) [875,865] := by
    cases ha0 : v432 c <;> cases ha1 : v433 c <;> simp [ClauseSat, litVal, assignment_432, assignment_437, v437, ha0, ha1]
  have hc2454 : ClauseSat (assignment c) [875,867] := by
    cases ha0 : v432 c <;> cases ha1 : v433 c <;> simp [ClauseSat, litVal, assignment_433, assignment_437, v437, ha0, ha1]
  have hc2455 : ClauseSat (assignment c) [874,864,866] := by
    cases ha0 : v432 c <;> cases ha1 : v433 c <;> simp [ClauseSat, litVal, assignment_432, assignment_433, assignment_437, v437, ha0, ha1]
  have hc2456 : ClauseSat (assignment c) [73,877,873] := by
    cases ha0 : v36 c <;> cases ha1 : v436 c <;> cases ha2 : v437 c <;> simp [ClauseSat, litVal, assignment_36, assignment_436, assignment_438, v438, ha0, ha1, ha2]
  have hc2457 : ClauseSat (assignment c) [73,876,872] := by
    cases ha0 : v36 c <;> cases ha1 : v436 c <;> cases ha2 : v437 c <;> simp [ClauseSat, litVal, assignment_36, assignment_436, assignment_438, v438, ha0, ha1, ha2]
  have hc2458 : ClauseSat (assignment c) [72,877,875] := by
    cases ha0 : v36 c <;> cases ha1 : v436 c <;> cases ha2 : v437 c <;> simp [ClauseSat, litVal, assignment_36, assignment_437, assignment_438, v438, ha0, ha1, ha2]
  have hc2459 : ClauseSat (assignment c) [72,876,874] := by
    cases ha0 : v36 c <;> cases ha1 : v436 c <;> cases ha2 : v437 c <;> simp [ClauseSat, litVal, assignment_36, assignment_437, assignment_438, v438, ha0, ha1, ha2]
  have hc2460 : ClauseSat (assignment c) [121,878] := by
    by_cases hs : c.a3.val = 0
    · simp [ClauseSat, litVal, assignment_60, assignment_439, v439, v60, hs]
    · simp [ClauseSat, litVal, assignment_60, assignment_439, v60, hs]
  have hc2461 : ClauseSat (assignment c) [123,879] := by
    by_cases hs : c.a3.val = 1
    · simp [ClauseSat, litVal, assignment_61, assignment_439, v439, v61, hs]
    · simp [ClauseSat, litVal, assignment_61, assignment_439, v61, hs]
  have hc2462 : ClauseSat (assignment c) [125,879] := by
    by_cases hs : c.a3.val = 2
    · simp [ClauseSat, litVal, assignment_62, assignment_439, v439, v62, hs]
    · simp [ClauseSat, litVal, assignment_62, assignment_439, v62, hs]
  have hc2463 : ClauseSat (assignment c) [127,879] := by
    by_cases hs : c.a3.val = 3
    · simp [ClauseSat, litVal, assignment_63, assignment_439, v439, v63, hs]
    · simp [ClauseSat, litVal, assignment_63, assignment_439, v63, hs]
  have hc2464 : ClauseSat (assignment c) [129,879,848] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_424, assignment_439, v439, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_424, assignment_439, v64, hs]
  have hc2465 : ClauseSat (assignment c) [129,878,849] := by
    by_cases hs : c.a3.val = 4
    · simp [ClauseSat, litVal, assignment_64, assignment_424, assignment_439, v439, v64, hs]
    · simp [ClauseSat, litVal, assignment_64, assignment_424, assignment_439, v64, hs]
  have hc2466 : ClauseSat (assignment c) [131,879,862] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_431, assignment_439, v439, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_431, assignment_439, v65, hs]
  have hc2467 : ClauseSat (assignment c) [131,878,863] := by
    by_cases hs : c.a3.val = 5
    · simp [ClauseSat, litVal, assignment_65, assignment_431, assignment_439, v439, v65, hs]
    · simp [ClauseSat, litVal, assignment_65, assignment_431, assignment_439, v65, hs]
  have hc2468 : ClauseSat (assignment c) [133,879,876] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_438, assignment_439, v439, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_438, assignment_439, v66, hs]
  have hc2469 : ClauseSat (assignment c) [133,878,877] := by
    by_cases hs : c.a3.val = 6
    · simp [ClauseSat, litVal, assignment_66, assignment_438, assignment_439, v439, v66, hs]
    · simp [ClauseSat, litVal, assignment_66, assignment_438, assignment_439, v66, hs]
  have hc2470 : ClauseSat (assignment c) [135,880] := by
    by_cases hs : c.b3.val = 0
    · simp [ClauseSat, litVal, assignment_67, assignment_440, v440, v67, hs]
    · simp [ClauseSat, litVal, assignment_67, assignment_440, v67, hs]
  have hc2471 : ClauseSat (assignment c) [137,881] := by
    by_cases hs : c.b3.val = 1
    · simp [ClauseSat, litVal, assignment_68, assignment_440, v440, v68, hs]
    · simp [ClauseSat, litVal, assignment_68, assignment_440, v68, hs]
  have hc2472 : ClauseSat (assignment c) [139,881] := by
    by_cases hs : c.b3.val = 2
    · simp [ClauseSat, litVal, assignment_69, assignment_440, v440, v69, hs]
    · simp [ClauseSat, litVal, assignment_69, assignment_440, v69, hs]
  have hc2473 : ClauseSat (assignment c) [141,881] := by
    by_cases hs : c.b3.val = 3
    · simp [ClauseSat, litVal, assignment_70, assignment_440, v440, v70, hs]
    · simp [ClauseSat, litVal, assignment_70, assignment_440, v70, hs]
  have hc2474 : ClauseSat (assignment c) [143,881,848] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_424, assignment_440, v440, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_424, assignment_440, v71, hs]
  have hc2475 : ClauseSat (assignment c) [143,880,849] := by
    by_cases hs : c.b3.val = 4
    · simp [ClauseSat, litVal, assignment_71, assignment_424, assignment_440, v440, v71, hs]
    · simp [ClauseSat, litVal, assignment_71, assignment_424, assignment_440, v71, hs]
  have hc2476 : ClauseSat (assignment c) [145,881,862] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_431, assignment_440, v440, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_431, assignment_440, v72, hs]
  have hc2477 : ClauseSat (assignment c) [145,880,863] := by
    by_cases hs : c.b3.val = 5
    · simp [ClauseSat, litVal, assignment_72, assignment_431, assignment_440, v440, v72, hs]
    · simp [ClauseSat, litVal, assignment_72, assignment_431, assignment_440, v72, hs]
  have hc2478 : ClauseSat (assignment c) [147,881,876] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_438, assignment_440, v440, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_438, assignment_440, v73, hs]
  have hc2479 : ClauseSat (assignment c) [147,880,877] := by
    by_cases hs : c.b3.val = 6
    · simp [ClauseSat, litVal, assignment_73, assignment_438, assignment_440, v440, v73, hs]
    · simp [ClauseSat, litVal, assignment_73, assignment_438, assignment_440, v73, hs]
  have hc2480 : ClauseSat (assignment c) [883,824] := by
    cases ha0 : v412 c <;> cases ha1 : v440 c <;> simp [ClauseSat, litVal, assignment_412, assignment_441, v441, ha0, ha1]
  have hc2481 : ClauseSat (assignment c) [883,880] := by
    cases ha0 : v412 c <;> cases ha1 : v440 c <;> simp [ClauseSat, litVal, assignment_440, assignment_441, v441, ha0, ha1]
  have hc2482 : ClauseSat (assignment c) [882,825,881] := by
    cases ha0 : v412 c <;> cases ha1 : v440 c <;> simp [ClauseSat, litVal, assignment_412, assignment_440, assignment_441, v441, ha0, ha1]
  have hc2483 : ClauseSat (assignment c) [885,878] := by
    cases ha0 : v413 c <;> cases ha1 : v439 c <;> simp [ClauseSat, litVal, assignment_439, assignment_442, v442, ha0, ha1]
  have hc2484 : ClauseSat (assignment c) [885,826] := by
    cases ha0 : v413 c <;> cases ha1 : v439 c <;> simp [ClauseSat, litVal, assignment_413, assignment_442, v442, ha0, ha1]
  have hc2485 : ClauseSat (assignment c) [884,879,827] := by
    cases ha0 : v413 c <;> cases ha1 : v439 c <;> simp [ClauseSat, litVal, assignment_413, assignment_439, assignment_442, v442, ha0, ha1]
  have hc2486 : ClauseSat (assignment c) [887,883] := by
    cases ha0 : v441 c <;> cases ha1 : v442 c <;> simp [ClauseSat, litVal, assignment_441, assignment_443, v443, ha0, ha1]
  have hc2487 : ClauseSat (assignment c) [887,885] := by
    cases ha0 : v441 c <;> cases ha1 : v442 c <;> simp [ClauseSat, litVal, assignment_442, assignment_443, v443, ha0, ha1]
  have hc2488 : ClauseSat (assignment c) [886,882,884] := by
    cases ha0 : v441 c <;> cases ha1 : v442 c <;> simp [ClauseSat, litVal, assignment_441, assignment_442, assignment_443, v443, ha0, ha1]
  have hc2489 : ClauseSat (assignment c) [889,879] := by
    cases ha0 : v439 c <;> cases ha1 : v440 c <;> simp [ClauseSat, litVal, assignment_439, assignment_444, v444, ha0, ha1]
  have hc2490 : ClauseSat (assignment c) [889,881] := by
    cases ha0 : v439 c <;> cases ha1 : v440 c <;> simp [ClauseSat, litVal, assignment_440, assignment_444, v444, ha0, ha1]
  have hc2491 : ClauseSat (assignment c) [888,878,880] := by
    cases ha0 : v439 c <;> cases ha1 : v440 c <;> simp [ClauseSat, litVal, assignment_439, assignment_440, assignment_444, v444, ha0, ha1]
  have hc2492 : ClauseSat (assignment c) [119,891,887] := by
    cases ha0 : v59 c <;> cases ha1 : v443 c <;> cases ha2 : v444 c <;> simp [ClauseSat, litVal, assignment_59, assignment_443, assignment_445, v445, ha0, ha1, ha2]
  have hc2493 : ClauseSat (assignment c) [119,890,886] := by
    cases ha0 : v59 c <;> cases ha1 : v443 c <;> cases ha2 : v444 c <;> simp [ClauseSat, litVal, assignment_59, assignment_443, assignment_445, v445, ha0, ha1, ha2]
  have hc2494 : ClauseSat (assignment c) [118,891,889] := by
    cases ha0 : v59 c <;> cases ha1 : v443 c <;> cases ha2 : v444 c <;> simp [ClauseSat, litVal, assignment_59, assignment_444, assignment_445, v445, ha0, ha1, ha2]
  have hc2495 : ClauseSat (assignment c) [118,890,888] := by
    cases ha0 : v59 c <;> cases ha1 : v443 c <;> cases ha2 : v444 c <;> simp [ClauseSat, litVal, assignment_59, assignment_444, assignment_445, v445, ha0, ha1, ha2]
  have hc2496 : ClauseSat (assignment c) [175,892] := by
    by_cases hs : c.a4.val = 0
    · simp [ClauseSat, litVal, assignment_87, assignment_446, v446, v87, hs]
    · simp [ClauseSat, litVal, assignment_87, assignment_446, v87, hs]
  have hc2497 : ClauseSat (assignment c) [177,893] := by
    by_cases hs : c.a4.val = 1
    · simp [ClauseSat, litVal, assignment_88, assignment_446, v446, v88, hs]
    · simp [ClauseSat, litVal, assignment_88, assignment_446, v88, hs]
  have hc2498 : ClauseSat (assignment c) [179,893] := by
    by_cases hs : c.a4.val = 2
    · simp [ClauseSat, litVal, assignment_89, assignment_446, v446, v89, hs]
    · simp [ClauseSat, litVal, assignment_89, assignment_446, v89, hs]
  have hc2499 : ClauseSat (assignment c) [181,893] := by
    by_cases hs : c.a4.val = 3
    · simp [ClauseSat, litVal, assignment_90, assignment_446, v446, v90, hs]
    · simp [ClauseSat, litVal, assignment_90, assignment_446, v90, hs]
  simp only [chunk24, List.forall_mem_cons]
  exact ⟨hc2400, hc2401, hc2402, hc2403, hc2404, hc2405, hc2406, hc2407, hc2408, hc2409, hc2410, hc2411, hc2412, hc2413, hc2414, hc2415, hc2416, hc2417, hc2418, hc2419, hc2420, hc2421, hc2422, hc2423, hc2424, hc2425, hc2426, hc2427, hc2428, hc2429, hc2430, hc2431, hc2432, hc2433, hc2434, hc2435, hc2436, hc2437, hc2438, hc2439, hc2440, hc2441, hc2442, hc2443, hc2444, hc2445, hc2446, hc2447, hc2448, hc2449, hc2450, hc2451, hc2452, hc2453, hc2454, hc2455, hc2456, hc2457, hc2458, hc2459, hc2460, hc2461, hc2462, hc2463, hc2464, hc2465, hc2466, hc2467, hc2468, hc2469, hc2470, hc2471, hc2472, hc2473, hc2474, hc2475, hc2476, hc2477, hc2478, hc2479, hc2480, hc2481, hc2482, hc2483, hc2484, hc2485, hc2486, hc2487, hc2488, hc2489, hc2490, hc2491, hc2492, hc2493, hc2494, hc2495, hc2496, hc2497, hc2498, hc2499, by simp⟩
#check satChunk24

def chunk25 : List (List Nat) := [[183, 893, 848], [183, 892, 849], [185, 893, 862], [185, 892, 863], [187, 893, 876], [187, 892, 877], [189, 893, 890], [189, 892, 891], [191, 894], [193, 895], [195, 895], [197, 895], [199, 895, 848], [199, 894, 849], [201, 895, 862], [201, 894, 863], [203, 895, 876], [203, 894, 877], [205, 895, 890], [205, 894, 891], [897, 830], [897, 894], [896, 831, 895], [899, 892], [899, 832], [898, 893, 833], [901, 897], [901, 899], [900, 896, 898], [903, 893], [903, 895], [902, 892, 894], [173, 905, 901], [173, 904, 900], [172, 905, 903], [172, 904, 902], [905]]
theorem satChunk25 (c : Candidate) (hv : valid c)
    (hr : ∀ r : Fin 16, output c r = target r)
    (hl : derivativeLeft c = false) (hd : derivativeRight c = false) :
    ∀ cl ∈ chunk25, ClauseSat (assignment c) cl := by
  rcases hv with ⟨h0, h1, h2, h3, h4⟩
  have hc2500 : ClauseSat (assignment c) [183,893,848] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_424, assignment_446, v446, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_424, assignment_446, v91, hs]
  have hc2501 : ClauseSat (assignment c) [183,892,849] := by
    by_cases hs : c.a4.val = 4
    · simp [ClauseSat, litVal, assignment_91, assignment_424, assignment_446, v446, v91, hs]
    · simp [ClauseSat, litVal, assignment_91, assignment_424, assignment_446, v91, hs]
  have hc2502 : ClauseSat (assignment c) [185,893,862] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_431, assignment_446, v446, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_431, assignment_446, v92, hs]
  have hc2503 : ClauseSat (assignment c) [185,892,863] := by
    by_cases hs : c.a4.val = 5
    · simp [ClauseSat, litVal, assignment_92, assignment_431, assignment_446, v446, v92, hs]
    · simp [ClauseSat, litVal, assignment_92, assignment_431, assignment_446, v92, hs]
  have hc2504 : ClauseSat (assignment c) [187,893,876] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_438, assignment_446, v446, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_438, assignment_446, v93, hs]
  have hc2505 : ClauseSat (assignment c) [187,892,877] := by
    by_cases hs : c.a4.val = 6
    · simp [ClauseSat, litVal, assignment_93, assignment_438, assignment_446, v446, v93, hs]
    · simp [ClauseSat, litVal, assignment_93, assignment_438, assignment_446, v93, hs]
  have hc2506 : ClauseSat (assignment c) [189,893,890] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_445, assignment_446, v446, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_445, assignment_446, v94, hs]
  have hc2507 : ClauseSat (assignment c) [189,892,891] := by
    by_cases hs : c.a4.val = 7
    · simp [ClauseSat, litVal, assignment_94, assignment_445, assignment_446, v446, v94, hs]
    · simp [ClauseSat, litVal, assignment_94, assignment_445, assignment_446, v94, hs]
  have hc2508 : ClauseSat (assignment c) [191,894] := by
    by_cases hs : c.b4.val = 0
    · simp [ClauseSat, litVal, assignment_95, assignment_447, v447, v95, hs]
    · simp [ClauseSat, litVal, assignment_95, assignment_447, v95, hs]
  have hc2509 : ClauseSat (assignment c) [193,895] := by
    by_cases hs : c.b4.val = 1
    · simp [ClauseSat, litVal, assignment_96, assignment_447, v447, v96, hs]
    · simp [ClauseSat, litVal, assignment_96, assignment_447, v96, hs]
  have hc2510 : ClauseSat (assignment c) [195,895] := by
    by_cases hs : c.b4.val = 2
    · simp [ClauseSat, litVal, assignment_97, assignment_447, v447, v97, hs]
    · simp [ClauseSat, litVal, assignment_97, assignment_447, v97, hs]
  have hc2511 : ClauseSat (assignment c) [197,895] := by
    by_cases hs : c.b4.val = 3
    · simp [ClauseSat, litVal, assignment_98, assignment_447, v447, v98, hs]
    · simp [ClauseSat, litVal, assignment_98, assignment_447, v98, hs]
  have hc2512 : ClauseSat (assignment c) [199,895,848] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_424, assignment_447, v447, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_424, assignment_447, v99, hs]
  have hc2513 : ClauseSat (assignment c) [199,894,849] := by
    by_cases hs : c.b4.val = 4
    · simp [ClauseSat, litVal, assignment_99, assignment_424, assignment_447, v447, v99, hs]
    · simp [ClauseSat, litVal, assignment_99, assignment_424, assignment_447, v99, hs]
  have hc2514 : ClauseSat (assignment c) [201,895,862] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_431, assignment_447, v447, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_431, assignment_447, v100, hs]
  have hc2515 : ClauseSat (assignment c) [201,894,863] := by
    by_cases hs : c.b4.val = 5
    · simp [ClauseSat, litVal, assignment_100, assignment_431, assignment_447, v447, v100, hs]
    · simp [ClauseSat, litVal, assignment_100, assignment_431, assignment_447, v100, hs]
  have hc2516 : ClauseSat (assignment c) [203,895,876] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_438, assignment_447, v447, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_438, assignment_447, v101, hs]
  have hc2517 : ClauseSat (assignment c) [203,894,877] := by
    by_cases hs : c.b4.val = 6
    · simp [ClauseSat, litVal, assignment_101, assignment_438, assignment_447, v447, v101, hs]
    · simp [ClauseSat, litVal, assignment_101, assignment_438, assignment_447, v101, hs]
  have hc2518 : ClauseSat (assignment c) [205,895,890] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_445, assignment_447, v447, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_445, assignment_447, v102, hs]
  have hc2519 : ClauseSat (assignment c) [205,894,891] := by
    by_cases hs : c.b4.val = 7
    · simp [ClauseSat, litVal, assignment_102, assignment_445, assignment_447, v447, v102, hs]
    · simp [ClauseSat, litVal, assignment_102, assignment_445, assignment_447, v102, hs]
  have hc2520 : ClauseSat (assignment c) [897,830] := by
    cases ha0 : v415 c <;> cases ha1 : v447 c <;> simp [ClauseSat, litVal, assignment_415, assignment_448, v448, ha0, ha1]
  have hc2521 : ClauseSat (assignment c) [897,894] := by
    cases ha0 : v415 c <;> cases ha1 : v447 c <;> simp [ClauseSat, litVal, assignment_447, assignment_448, v448, ha0, ha1]
  have hc2522 : ClauseSat (assignment c) [896,831,895] := by
    cases ha0 : v415 c <;> cases ha1 : v447 c <;> simp [ClauseSat, litVal, assignment_415, assignment_447, assignment_448, v448, ha0, ha1]
  have hc2523 : ClauseSat (assignment c) [899,892] := by
    cases ha0 : v416 c <;> cases ha1 : v446 c <;> simp [ClauseSat, litVal, assignment_446, assignment_449, v449, ha0, ha1]
  have hc2524 : ClauseSat (assignment c) [899,832] := by
    cases ha0 : v416 c <;> cases ha1 : v446 c <;> simp [ClauseSat, litVal, assignment_416, assignment_449, v449, ha0, ha1]
  have hc2525 : ClauseSat (assignment c) [898,893,833] := by
    cases ha0 : v416 c <;> cases ha1 : v446 c <;> simp [ClauseSat, litVal, assignment_416, assignment_446, assignment_449, v449, ha0, ha1]
  have hc2526 : ClauseSat (assignment c) [901,897] := by
    cases ha0 : v448 c <;> cases ha1 : v449 c <;> simp [ClauseSat, litVal, assignment_448, assignment_450, v450, ha0, ha1]
  have hc2527 : ClauseSat (assignment c) [901,899] := by
    cases ha0 : v448 c <;> cases ha1 : v449 c <;> simp [ClauseSat, litVal, assignment_449, assignment_450, v450, ha0, ha1]
  have hc2528 : ClauseSat (assignment c) [900,896,898] := by
    cases ha0 : v448 c <;> cases ha1 : v449 c <;> simp [ClauseSat, litVal, assignment_448, assignment_449, assignment_450, v450, ha0, ha1]
  have hc2529 : ClauseSat (assignment c) [903,893] := by
    cases ha0 : v446 c <;> cases ha1 : v447 c <;> simp [ClauseSat, litVal, assignment_446, assignment_451, v451, ha0, ha1]
  have hc2530 : ClauseSat (assignment c) [903,895] := by
    cases ha0 : v446 c <;> cases ha1 : v447 c <;> simp [ClauseSat, litVal, assignment_447, assignment_451, v451, ha0, ha1]
  have hc2531 : ClauseSat (assignment c) [902,892,894] := by
    cases ha0 : v446 c <;> cases ha1 : v447 c <;> simp [ClauseSat, litVal, assignment_446, assignment_447, assignment_451, v451, ha0, ha1]
  have hc2532 : ClauseSat (assignment c) [173,905,901] := by
    cases ha0 : v86 c <;> cases ha1 : v450 c <;> cases ha2 : v451 c <;> simp [ClauseSat, litVal, assignment_86, assignment_450, assignment_452, v452, ha0, ha1, ha2]
  have hc2533 : ClauseSat (assignment c) [173,904,900] := by
    cases ha0 : v86 c <;> cases ha1 : v450 c <;> cases ha2 : v451 c <;> simp [ClauseSat, litVal, assignment_86, assignment_450, assignment_452, v452, ha0, ha1, ha2]
  have hc2534 : ClauseSat (assignment c) [172,905,903] := by
    cases ha0 : v86 c <;> cases ha1 : v450 c <;> cases ha2 : v451 c <;> simp [ClauseSat, litVal, assignment_86, assignment_451, assignment_452, v452, ha0, ha1, ha2]
  have hc2535 : ClauseSat (assignment c) [172,904,902] := by
    cases ha0 : v86 c <;> cases ha1 : v450 c <;> cases ha2 : v451 c <;> simp [ClauseSat, litVal, assignment_86, assignment_451, assignment_452, v452, ha0, ha1, ha2]
  have hc2536 : ClauseSat (assignment c) [905] := by
    simpa [ClauseSat, litVal, assignment_452, derivativeRight] using hd
  simp only [chunk25, List.forall_mem_cons]
  exact ⟨hc2500, hc2501, hc2502, hc2503, hc2504, hc2505, hc2506, hc2507, hc2508, hc2509, hc2510, hc2511, hc2512, hc2513, hc2514, hc2515, hc2516, hc2517, hc2518, hc2519, hc2520, hc2521, hc2522, hc2523, hc2524, hc2525, hc2526, hc2527, hc2528, hc2529, hc2530, hc2531, hc2532, hc2533, hc2534, hc2535, hc2536, by simp⟩
#check satChunk25

theorem encodedImpossibleChunks (c : Candidate) (hv : valid c)
    (hr : ∀ r : Fin 16, output c r = target r)
    (hl : derivativeLeft c = false) (hd : derivativeRight c = false) : False := by
  apply cnfUnsat
  refine ⟨assignment c, ?_⟩
  change ∀ cl ∈ chunk0 ++ chunk1 ++ chunk2 ++ chunk3 ++ chunk4 ++ chunk5 ++ chunk6 ++ chunk7 ++ chunk8 ++ chunk9 ++ chunk10 ++ chunk11 ++ chunk12 ++ chunk13 ++ chunk14 ++ chunk15 ++ chunk16 ++ chunk17 ++ chunk18 ++ chunk19 ++ chunk20 ++ chunk21 ++ chunk22 ++ chunk23 ++ chunk24 ++ chunk25 ++ [], ClauseSat (assignment c) cl
  simp only [List.mem_append, or_imp, forall_and, and_assoc]
  exact ⟨satChunk0 c hv hr hl hd, satChunk1 c hv hr hl hd, satChunk2 c hv hr hl hd, satChunk3 c hv hr hl hd, satChunk4 c hv hr hl hd, satChunk5 c hv hr hl hd, satChunk6 c hv hr hl hd, satChunk7 c hv hr hl hd, satChunk8 c hv hr hl hd, satChunk9 c hv hr hl hd, satChunk10 c hv hr hl hd, satChunk11 c hv hr hl hd, satChunk12 c hv hr hl hd, satChunk13 c hv hr hl hd, satChunk14 c hv hr hl hd, satChunk15 c hv hr hl hd, satChunk16 c hv hr hl hd, satChunk17 c hv hr hl hd, satChunk18 c hv hr hl hd, satChunk19 c hv hr hl hd, satChunk20 c hv hr hl hd, satChunk21 c hv hr hl hd, satChunk22 c hv hr hl hd, satChunk23 c hv hr hl hd, satChunk24 c hv hr hl hd, satChunk25 c hv hr hl hd, by simp⟩

end PEqualNP.Outside.Pilot64Bridge
