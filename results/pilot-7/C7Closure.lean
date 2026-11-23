import C7NoGoal
import C7Chunk4_0
import C7Chunk5_0
import C7Chunk5_4
import C7Chunk6_0
import C7Chunk6_4
import C7Chunk6_8
import C7Chunk6_12
import C7Chunk6_16
import C7Chunk6_20
import C7Chunk6_24
import C7Chunk6_28
import C7Chunk6_32
import C7Chunk6_36
import C7Chunk6_40
import C7Chunk7_0
import C7Chunk7_4
import C7Chunk7_8
import C7Chunk7_12
import C7Chunk7_16
import C7Chunk7_20
import C7Chunk7_24
import C7Chunk7_28
import C7Chunk7_32
import C7Chunk7_36
import C7Chunk7_40
import C7Chunk7_44
import C7Chunk7_48
import C7Chunk7_52
import C7Chunk7_56
import C7Chunk8_0
import C7Chunk8_4
import C7Chunk9_0
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PEqualNP.Outside.L_meta_982_aux.Finite
theorem seed8_level_0 : (List.range (seed8Count 0)).all (seed8Check 0) = true := by
  decide +kernel
theorem seed8_level_1 : (List.range (seed8Count 1)).all (seed8Check 1) = true := by
  decide +kernel
theorem seed8_level_2 : (List.range (seed8Count 2)).all (seed8Check 2) = true := by
  decide +kernel
theorem seed8_level_3 : (List.range (seed8Count 3)).all (seed8Check 3) = true := by
  decide +kernel
theorem seed8_level_4 : (List.range (seed8Count 4)).all (seed8Check 4) = true := by
  change [0].all (seed8Check 4) = true
  simp only [List.all_cons, List.all_nil, Bool.true_and, seed8_bar_4_0]
theorem seed8_level_5 : (List.range (seed8Count 5)).all (seed8Check 5) = true := by
  change [0, 1, 2, 3, 4, 5, 6, 7].all (seed8Check 5) = true
  simp only [List.all_cons, List.all_nil, Bool.true_and, seed8_bar_5_0, seed8_bar_5_1, seed8_bar_5_2, seed8_bar_5_3, seed8_bar_5_4, seed8_bar_5_5, seed8_bar_5_6, seed8_bar_5_7]
theorem seed8_level_6 : (List.range (seed8Count 6)).all (seed8Check 6) = true := by
  change [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40].all (seed8Check 6) = true
  simp only [List.all_cons, List.all_nil, Bool.true_and, seed8_bar_6_0, seed8_bar_6_1, seed8_bar_6_2, seed8_bar_6_3, seed8_bar_6_4, seed8_bar_6_5, seed8_bar_6_6, seed8_bar_6_7, seed8_bar_6_8, seed8_bar_6_9, seed8_bar_6_10, seed8_bar_6_11, seed8_bar_6_12, seed8_bar_6_13, seed8_bar_6_14, seed8_bar_6_15, seed8_bar_6_16, seed8_bar_6_17, seed8_bar_6_18, seed8_bar_6_19, seed8_bar_6_20, seed8_bar_6_21, seed8_bar_6_22, seed8_bar_6_23, seed8_bar_6_24, seed8_bar_6_25, seed8_bar_6_26, seed8_bar_6_27, seed8_bar_6_28, seed8_bar_6_29, seed8_bar_6_30, seed8_bar_6_31, seed8_bar_6_32, seed8_bar_6_33, seed8_bar_6_34, seed8_bar_6_35, seed8_bar_6_36, seed8_bar_6_37, seed8_bar_6_38, seed8_bar_6_39, seed8_bar_6_40]
theorem seed8_level_7 : (List.range (seed8Count 7)).all (seed8Check 7) = true := by
  change [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56].all (seed8Check 7) = true
  simp only [List.all_cons, List.all_nil, Bool.true_and, seed8_bar_7_0, seed8_bar_7_1, seed8_bar_7_2, seed8_bar_7_3, seed8_bar_7_4, seed8_bar_7_5, seed8_bar_7_6, seed8_bar_7_7, seed8_bar_7_8, seed8_bar_7_9, seed8_bar_7_10, seed8_bar_7_11, seed8_bar_7_12, seed8_bar_7_13, seed8_bar_7_14, seed8_bar_7_15, seed8_bar_7_16, seed8_bar_7_17, seed8_bar_7_18, seed8_bar_7_19, seed8_bar_7_20, seed8_bar_7_21, seed8_bar_7_22, seed8_bar_7_23, seed8_bar_7_24, seed8_bar_7_25, seed8_bar_7_26, seed8_bar_7_27, seed8_bar_7_28, seed8_bar_7_29, seed8_bar_7_30, seed8_bar_7_31, seed8_bar_7_32, seed8_bar_7_33, seed8_bar_7_34, seed8_bar_7_35, seed8_bar_7_36, seed8_bar_7_37, seed8_bar_7_38, seed8_bar_7_39, seed8_bar_7_40, seed8_bar_7_41, seed8_bar_7_42, seed8_bar_7_43, seed8_bar_7_44, seed8_bar_7_45, seed8_bar_7_46, seed8_bar_7_47, seed8_bar_7_48, seed8_bar_7_49, seed8_bar_7_50, seed8_bar_7_51, seed8_bar_7_52, seed8_bar_7_53, seed8_bar_7_54, seed8_bar_7_55, seed8_bar_7_56]
theorem seed8_level_8 : (List.range (seed8Count 8)).all (seed8Check 8) = true := by
  change [0, 1, 2, 3, 4, 5, 6, 7].all (seed8Check 8) = true
  simp only [List.all_cons, List.all_nil, Bool.true_and, seed8_bar_8_0, seed8_bar_8_1, seed8_bar_8_2, seed8_bar_8_3, seed8_bar_8_4, seed8_bar_8_5, seed8_bar_8_6, seed8_bar_8_7]
theorem seed8_level_9 : (List.range (seed8Count 9)).all (seed8Check 9) = true := by
  change [0].all (seed8Check 9) = true
  simp only [List.all_cons, List.all_nil, Bool.true_and, seed8_bar_9_0]

theorem seed8_closure_checked :
    (List.range 10).all (fun s => (List.range (seed8Count s)).all (seed8Check s)) = true := by
  change [0,1,2,3,4,5,6,7,8,9].all (fun s => (List.range (seed8Count s)).all (seed8Check s)) = true
  simp only [List.all_cons, List.all_nil, Bool.true_and,
    seed8_level_0, seed8_level_1, seed8_level_2, seed8_level_3, seed8_level_4,
    seed8_level_5, seed8_level_6, seed8_level_7, seed8_level_8, seed8_level_9]

theorem seed8_checked (s : Nat) (hs : s ≤ 9) (i : Nat) (hi : i < seed8Count s) :
    Reduced.pairedBar seed8Forbidden seed8K seed8ScoreWidth seed8States seed8Count
      seed8Child seed8Orient seed8Pool s i = true := by
  have h1 := List.all_eq_true.1 seed8_closure_checked s (List.mem_range.2 (by omega))
  have h2 := List.all_eq_true.1 h1 i (List.mem_range.2 hi)
  change Fast.pairedBar _ _ _ _ _ _ _ _ s i = true at h2
  rw [Fast.pairedBar_eq] at h2
  exact h2

#print axioms seed8_checked
end PEqualNP.Outside.L_meta_982_aux.Finite
