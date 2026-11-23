import Seed0NoGoal
import Seed0Chunk4_0
import Seed0Chunk5_0
import Seed0Chunk5_8
import Seed0Chunk5_16
import Seed0Chunk5_24
import Seed0Chunk6_0
import Seed0Chunk6_8
import Seed0Chunk6_16
import Seed0Chunk6_24
import Seed0Chunk6_32
import Seed0Chunk6_40
import Seed0Chunk6_48
import Seed0Chunk6_56
import Seed0Chunk6_64
import Seed0Chunk6_72
import Seed0Chunk6_80
import Seed0Chunk6_88
import Seed0Chunk6_96
import Seed0Chunk6_104
import Seed0Chunk6_112
import Seed0Chunk6_120
import Seed0Chunk6_128
import Seed0Chunk6_136
import Seed0Chunk7_0
import Seed0Chunk7_8
import Seed0Chunk7_16
import Seed0Chunk7_24
import Seed0Chunk7_32
import Seed0Chunk7_40
import Seed0Chunk7_48
import Seed0Chunk7_56
import Seed0Chunk7_64
import Seed0Chunk7_72
import Seed0Chunk7_80
import Seed0Chunk7_88
import Seed0Chunk7_96
import Seed0Chunk7_104
import Seed0Chunk7_112
import Seed0Chunk7_120
import Seed0Chunk7_128
import Seed0Chunk7_136
import Seed0Chunk7_144
import Seed0Chunk7_152
import Seed0Chunk7_160
import Seed0Chunk7_168
import Seed0Chunk8_0
import Seed0Chunk8_8
import Seed0Chunk9_0
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PEqualNP.Outside.L_meta_982_aux.Finite
theorem seed0_level_0 : (List.range (seed0Count 0)).all (seed0Check 0) = true := by
  decide +kernel
theorem seed0_level_1 : (List.range (seed0Count 1)).all (seed0Check 1) = true := by
  decide +kernel
theorem seed0_level_2 : (List.range (seed0Count 2)).all (seed0Check 2) = true := by
  decide +kernel
theorem seed0_level_3 : (List.range (seed0Count 3)).all (seed0Check 3) = true := by
  decide +kernel
theorem seed0_level_4 : (List.range (seed0Count 4)).all (seed0Check 4) = true := by
  change [0, 1].all (seed0Check 4) = true
  simp only [List.all_cons, List.all_nil, Bool.true_and, seed0_bar_4_0, seed0_bar_4_1]
theorem seed0_level_5 : (List.range (seed0Count 5)).all (seed0Check 5) = true := by
  change [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24].all (seed0Check 5) = true
  simp only [List.all_cons, List.all_nil, Bool.true_and, seed0_bar_5_0, seed0_bar_5_1, seed0_bar_5_2, seed0_bar_5_3, seed0_bar_5_4, seed0_bar_5_5, seed0_bar_5_6, seed0_bar_5_7, seed0_bar_5_8, seed0_bar_5_9, seed0_bar_5_10, seed0_bar_5_11, seed0_bar_5_12, seed0_bar_5_13, seed0_bar_5_14, seed0_bar_5_15, seed0_bar_5_16, seed0_bar_5_17, seed0_bar_5_18, seed0_bar_5_19, seed0_bar_5_20, seed0_bar_5_21, seed0_bar_5_22, seed0_bar_5_23, seed0_bar_5_24]
theorem seed0_level_6 : (List.range (seed0Count 6)).all (seed0Check 6) = true := by
  change [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143].all (seed0Check 6) = true
  simp only [List.all_cons, List.all_nil, Bool.true_and, seed0_bar_6_0, seed0_bar_6_1, seed0_bar_6_2, seed0_bar_6_3, seed0_bar_6_4, seed0_bar_6_5, seed0_bar_6_6, seed0_bar_6_7, seed0_bar_6_8, seed0_bar_6_9, seed0_bar_6_10, seed0_bar_6_11, seed0_bar_6_12, seed0_bar_6_13, seed0_bar_6_14, seed0_bar_6_15, seed0_bar_6_16, seed0_bar_6_17, seed0_bar_6_18, seed0_bar_6_19, seed0_bar_6_20, seed0_bar_6_21, seed0_bar_6_22, seed0_bar_6_23, seed0_bar_6_24, seed0_bar_6_25, seed0_bar_6_26, seed0_bar_6_27, seed0_bar_6_28, seed0_bar_6_29, seed0_bar_6_30, seed0_bar_6_31, seed0_bar_6_32, seed0_bar_6_33, seed0_bar_6_34, seed0_bar_6_35, seed0_bar_6_36, seed0_bar_6_37, seed0_bar_6_38, seed0_bar_6_39, seed0_bar_6_40, seed0_bar_6_41, seed0_bar_6_42, seed0_bar_6_43, seed0_bar_6_44, seed0_bar_6_45, seed0_bar_6_46, seed0_bar_6_47, seed0_bar_6_48, seed0_bar_6_49, seed0_bar_6_50, seed0_bar_6_51, seed0_bar_6_52, seed0_bar_6_53, seed0_bar_6_54, seed0_bar_6_55, seed0_bar_6_56, seed0_bar_6_57, seed0_bar_6_58, seed0_bar_6_59, seed0_bar_6_60, seed0_bar_6_61, seed0_bar_6_62, seed0_bar_6_63, seed0_bar_6_64, seed0_bar_6_65, seed0_bar_6_66, seed0_bar_6_67, seed0_bar_6_68, seed0_bar_6_69, seed0_bar_6_70, seed0_bar_6_71, seed0_bar_6_72, seed0_bar_6_73, seed0_bar_6_74, seed0_bar_6_75, seed0_bar_6_76, seed0_bar_6_77, seed0_bar_6_78, seed0_bar_6_79, seed0_bar_6_80, seed0_bar_6_81, seed0_bar_6_82, seed0_bar_6_83, seed0_bar_6_84, seed0_bar_6_85, seed0_bar_6_86, seed0_bar_6_87, seed0_bar_6_88, seed0_bar_6_89, seed0_bar_6_90, seed0_bar_6_91, seed0_bar_6_92, seed0_bar_6_93, seed0_bar_6_94, seed0_bar_6_95, seed0_bar_6_96, seed0_bar_6_97, seed0_bar_6_98, seed0_bar_6_99, seed0_bar_6_100, seed0_bar_6_101, seed0_bar_6_102, seed0_bar_6_103, seed0_bar_6_104, seed0_bar_6_105, seed0_bar_6_106, seed0_bar_6_107, seed0_bar_6_108, seed0_bar_6_109, seed0_bar_6_110, seed0_bar_6_111, seed0_bar_6_112, seed0_bar_6_113, seed0_bar_6_114, seed0_bar_6_115, seed0_bar_6_116, seed0_bar_6_117, seed0_bar_6_118, seed0_bar_6_119, seed0_bar_6_120, seed0_bar_6_121, seed0_bar_6_122, seed0_bar_6_123, seed0_bar_6_124, seed0_bar_6_125, seed0_bar_6_126, seed0_bar_6_127, seed0_bar_6_128, seed0_bar_6_129, seed0_bar_6_130, seed0_bar_6_131, seed0_bar_6_132, seed0_bar_6_133, seed0_bar_6_134, seed0_bar_6_135, seed0_bar_6_136, seed0_bar_6_137, seed0_bar_6_138, seed0_bar_6_139, seed0_bar_6_140, seed0_bar_6_141, seed0_bar_6_142, seed0_bar_6_143]
theorem seed0_level_7 : (List.range (seed0Count 7)).all (seed0Check 7) = true := by
  change [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169].all (seed0Check 7) = true
  simp only [List.all_cons, List.all_nil, Bool.true_and, seed0_bar_7_0, seed0_bar_7_1, seed0_bar_7_2, seed0_bar_7_3, seed0_bar_7_4, seed0_bar_7_5, seed0_bar_7_6, seed0_bar_7_7, seed0_bar_7_8, seed0_bar_7_9, seed0_bar_7_10, seed0_bar_7_11, seed0_bar_7_12, seed0_bar_7_13, seed0_bar_7_14, seed0_bar_7_15, seed0_bar_7_16, seed0_bar_7_17, seed0_bar_7_18, seed0_bar_7_19, seed0_bar_7_20, seed0_bar_7_21, seed0_bar_7_22, seed0_bar_7_23, seed0_bar_7_24, seed0_bar_7_25, seed0_bar_7_26, seed0_bar_7_27, seed0_bar_7_28, seed0_bar_7_29, seed0_bar_7_30, seed0_bar_7_31, seed0_bar_7_32, seed0_bar_7_33, seed0_bar_7_34, seed0_bar_7_35, seed0_bar_7_36, seed0_bar_7_37, seed0_bar_7_38, seed0_bar_7_39, seed0_bar_7_40, seed0_bar_7_41, seed0_bar_7_42, seed0_bar_7_43, seed0_bar_7_44, seed0_bar_7_45, seed0_bar_7_46, seed0_bar_7_47, seed0_bar_7_48, seed0_bar_7_49, seed0_bar_7_50, seed0_bar_7_51, seed0_bar_7_52, seed0_bar_7_53, seed0_bar_7_54, seed0_bar_7_55, seed0_bar_7_56, seed0_bar_7_57, seed0_bar_7_58, seed0_bar_7_59, seed0_bar_7_60, seed0_bar_7_61, seed0_bar_7_62, seed0_bar_7_63, seed0_bar_7_64, seed0_bar_7_65, seed0_bar_7_66, seed0_bar_7_67, seed0_bar_7_68, seed0_bar_7_69, seed0_bar_7_70, seed0_bar_7_71, seed0_bar_7_72, seed0_bar_7_73, seed0_bar_7_74, seed0_bar_7_75, seed0_bar_7_76, seed0_bar_7_77, seed0_bar_7_78, seed0_bar_7_79, seed0_bar_7_80, seed0_bar_7_81, seed0_bar_7_82, seed0_bar_7_83, seed0_bar_7_84, seed0_bar_7_85, seed0_bar_7_86, seed0_bar_7_87, seed0_bar_7_88, seed0_bar_7_89, seed0_bar_7_90, seed0_bar_7_91, seed0_bar_7_92, seed0_bar_7_93, seed0_bar_7_94, seed0_bar_7_95, seed0_bar_7_96, seed0_bar_7_97, seed0_bar_7_98, seed0_bar_7_99, seed0_bar_7_100, seed0_bar_7_101, seed0_bar_7_102, seed0_bar_7_103, seed0_bar_7_104, seed0_bar_7_105, seed0_bar_7_106, seed0_bar_7_107, seed0_bar_7_108, seed0_bar_7_109, seed0_bar_7_110, seed0_bar_7_111, seed0_bar_7_112, seed0_bar_7_113, seed0_bar_7_114, seed0_bar_7_115, seed0_bar_7_116, seed0_bar_7_117, seed0_bar_7_118, seed0_bar_7_119, seed0_bar_7_120, seed0_bar_7_121, seed0_bar_7_122, seed0_bar_7_123, seed0_bar_7_124, seed0_bar_7_125, seed0_bar_7_126, seed0_bar_7_127, seed0_bar_7_128, seed0_bar_7_129, seed0_bar_7_130, seed0_bar_7_131, seed0_bar_7_132, seed0_bar_7_133, seed0_bar_7_134, seed0_bar_7_135, seed0_bar_7_136, seed0_bar_7_137, seed0_bar_7_138, seed0_bar_7_139, seed0_bar_7_140, seed0_bar_7_141, seed0_bar_7_142, seed0_bar_7_143, seed0_bar_7_144, seed0_bar_7_145, seed0_bar_7_146, seed0_bar_7_147, seed0_bar_7_148, seed0_bar_7_149, seed0_bar_7_150, seed0_bar_7_151, seed0_bar_7_152, seed0_bar_7_153, seed0_bar_7_154, seed0_bar_7_155, seed0_bar_7_156, seed0_bar_7_157, seed0_bar_7_158, seed0_bar_7_159, seed0_bar_7_160, seed0_bar_7_161, seed0_bar_7_162, seed0_bar_7_163, seed0_bar_7_164, seed0_bar_7_165, seed0_bar_7_166, seed0_bar_7_167, seed0_bar_7_168, seed0_bar_7_169]
theorem seed0_level_8 : (List.range (seed0Count 8)).all (seed0Check 8) = true := by
  change [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14].all (seed0Check 8) = true
  simp only [List.all_cons, List.all_nil, Bool.true_and, seed0_bar_8_0, seed0_bar_8_1, seed0_bar_8_2, seed0_bar_8_3, seed0_bar_8_4, seed0_bar_8_5, seed0_bar_8_6, seed0_bar_8_7, seed0_bar_8_8, seed0_bar_8_9, seed0_bar_8_10, seed0_bar_8_11, seed0_bar_8_12, seed0_bar_8_13, seed0_bar_8_14]
theorem seed0_level_9 : (List.range (seed0Count 9)).all (seed0Check 9) = true := by
  change [0].all (seed0Check 9) = true
  simp only [List.all_cons, List.all_nil, Bool.true_and, seed0_bar_9_0]

theorem seed0_closure_checked :
    (List.range 10).all (fun s => (List.range (seed0Count s)).all (seed0Check s)) = true := by
  change [0,1,2,3,4,5,6,7,8,9].all (fun s => (List.range (seed0Count s)).all (seed0Check s)) = true
  simp only [List.all_cons, List.all_nil, Bool.true_and,
    seed0_level_0, seed0_level_1, seed0_level_2, seed0_level_3, seed0_level_4,
    seed0_level_5, seed0_level_6, seed0_level_7, seed0_level_8, seed0_level_9]

theorem seed0_checked (s : Nat) (hs : s ≤ 9) (i : Nat) (hi : i < seed0Count s) :
    Reduced.pairedBar seed0Forbidden seed0K seed0ScoreWidth seed0States seed0Count
      seed0Child seed0Orient seed0Pool s i = true := by
  have h1 := List.all_eq_true.1 seed0_closure_checked s (List.mem_range.2 (by omega))
  have h2 := List.all_eq_true.1 h1 i (List.mem_range.2 hi)
  change Fast.pairedBar _ _ _ _ _ _ _ _ s i = true at h2
  rw [Fast.pairedBar_eq] at h2
  exact h2

#print axioms seed0_checked
end PEqualNP.Outside.L_meta_982_aux.Finite
