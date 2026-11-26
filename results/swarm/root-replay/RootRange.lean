import RangeAssembly
import RootNodes0_31
import RootNodes32_63
import RootNodes64_95
import RootNodes96_127
import RootNodes128_159
import RootNodes160_191
import RootNodes192_223
import RootNodes224_255
namespace PEqualNP.Outside.L_meta_2373_aux.Cert18.RootReplay
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma checked (i : Fin 5230) (upper : i.val < 256) :
    Replay.DirectMode.Packed.checkNode i = true := by
  have blocks : ∀ q : Fin 64, Replay.DirectMode.Packed.slice (4*q.val) 4 = true := by
    intro q
    fin_cases q
    · exact checked_0_3
    · exact checked_4_7
    · exact checked_8_11
    · exact checked_12_15
    · exact checked_16_19
    · exact checked_20_23
    · exact checked_24_27
    · exact checked_28_31
    · exact checked_32_35
    · exact checked_36_39
    · exact checked_40_43
    · exact checked_44_47
    · exact checked_48_51
    · exact checked_52_55
    · exact checked_56_59
    · exact checked_60_63
    · exact checked_64_67
    · exact checked_68_71
    · exact checked_72_75
    · exact checked_76_79
    · exact checked_80_83
    · exact checked_84_87
    · exact checked_88_91
    · exact checked_92_95
    · exact checked_96_99
    · exact checked_100_103
    · exact checked_104_107
    · exact checked_108_111
    · exact checked_112_115
    · exact checked_116_119
    · exact checked_120_123
    · exact checked_124_127
    · exact checked_128_131
    · exact checked_132_135
    · exact checked_136_139
    · exact checked_140_143
    · exact checked_144_147
    · exact checked_148_151
    · exact checked_152_155
    · exact checked_156_159
    · exact checked_160_163
    · exact checked_164_167
    · exact checked_168_171
    · exact checked_172_175
    · exact checked_176_179
    · exact checked_180_183
    · exact checked_184_187
    · exact checked_188_191
    · exact checked_192_195
    · exact checked_196_199
    · exact checked_200_203
    · exact checked_204_207
    · exact checked_208_211
    · exact checked_212_215
    · exact checked_216_219
    · exact checked_220_223
    · exact checked_224_227
    · exact checked_228_231
    · exact checked_232_235
    · exact checked_236_239
    · exact checked_240_243
    · exact checked_244_247
    · exact checked_248_251
    · exact checked_252_255
  have chunks : ∀ q : Fin 64, Replay.DirectMode.Packed.slice
      (0+4*q.val) (min 4 (256-4*q.val)) = true := by
    intro q
    have hm : min 4 (256-4*q.val) = 4 := by omega
    simpa only [Nat.zero_add,hm] using blocks q
  exact Replay.DirectMode.Packed.blocks_sound 0 256 4 64 (by decide) (by decide)
    chunks i (Nat.zero_le _) upper
end PEqualNP.Outside.L_meta_2373_aux.Cert18.RootReplay
