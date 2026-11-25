import PackingThreeDefs
import PackingChunkProofs

namespace PEqualNP.Outside.L_meta_1896_aux
namespace PackingThree

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk_coverage : ∀ r : Fin 31,
    ((rootChunkIndices r).flatMap fun c =>
      (List.range (chunkData c).2.2).map fun j => (chunkData c).2.1 + j) =
      List.range (rootCandidates r).length := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chunk_roots : ∀ r : Fin 31, ∀ c ∈ rootChunkIndices r, (chunkData c).1 = r := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma roots_good : ∀ r : Fin 31, good (rootState r) = true := by
  decide +kernel

set_option maxRecDepth 100000
set_option maxHeartbeats 0

lemma chunk_check_0 : chunkCheck 0 = true := by decide +kernel

lemma chunk_check_1 : chunkCheck 1 = true := by decide +kernel

lemma chunk_check_2 : chunkCheck 2 = true := by decide +kernel

lemma chunk_check_3 : chunkCheck 3 = true := by decide +kernel

lemma chunk_check_4 : chunkCheck 4 = true := by decide +kernel

lemma chunk_check_5 : chunkCheck 5 = true := by decide +kernel

lemma chunk_check_6 : chunkCheck 6 = true := by decide +kernel

lemma chunk_check_7 : chunkCheck 7 = true := by decide +kernel

lemma chunk_check_8 : chunkCheck 8 = true := by decide +kernel

lemma chunk_check_9 : chunkCheck 9 = true := by decide +kernel

lemma chunk_check_10 : chunkCheck 10 = true := by decide +kernel

lemma chunk_check_11 : chunkCheck 11 = true := by decide +kernel

lemma chunk_check_12 : chunkCheck 12 = true := by decide +kernel

lemma chunk_check_13 : chunkCheck 13 = true := by decide +kernel

lemma chunk_check_14 : chunkCheck 14 = true := by decide +kernel

lemma chunk_check_15 : chunkCheck 15 = true := by decide +kernel

lemma chunk_check_16 : chunkCheck 16 = true := by decide +kernel

lemma chunk_check_17 : chunkCheck 17 = true := by decide +kernel

lemma chunk_check_18 : chunkCheck 18 = true := by decide +kernel

lemma chunk_check_19 : chunkCheck 19 = true := by decide +kernel

lemma chunk_check_20 : chunkCheck 20 = true := by decide +kernel

lemma chunk_check_21 : chunkCheck 21 = true := by decide +kernel

lemma chunk_check_22 : chunkCheck 22 = true := by decide +kernel

lemma chunk_check_23 : chunkCheck 23 = true := by decide +kernel

lemma chunk_check_24 : chunkCheck 24 = true := by decide +kernel

lemma chunk_check_25 : chunkCheck 25 = true := by decide +kernel

lemma chunk_check_26 : chunkCheck 26 = true := by decide +kernel

lemma chunk_check_27 : chunkCheck 27 = true := by decide +kernel

lemma chunk_check_28 : chunkCheck 28 = true := by decide +kernel

lemma chunk_check_29 : chunkCheck 29 = true := by decide +kernel

lemma chunk_check_30 : chunkCheck 30 = true := by decide +kernel

lemma chunk_check_31 : chunkCheck 31 = true := by decide +kernel

lemma chunk_check_32 : chunkCheck 32 = true := by decide +kernel

lemma chunk_check_33 : chunkCheck 33 = true := by decide +kernel

lemma chunk_check_34 : chunkCheck 34 = true := by decide +kernel

lemma chunk_check_35 : chunkCheck 35 = true := by decide +kernel

lemma chunk_check_36 : chunkCheck 36 = true := by decide +kernel

lemma chunk_check_37 : chunkCheck 37 = true := by decide +kernel

lemma chunk_check_38 : chunkCheck 38 = true := by decide +kernel

lemma chunk_check_39 : chunkCheck 39 = true := by decide +kernel

lemma chunk_check_40 : chunkCheck 40 = true := by decide +kernel

lemma chunk_check_41 : chunkCheck 41 = true := by decide +kernel

lemma chunk_check_42 : chunkCheck 42 = true := by decide +kernel

lemma chunk_check_43 : chunkCheck 43 = true := by decide +kernel

lemma chunk_check_44 : chunkCheck 44 = true := by decide +kernel

lemma chunk_check_45 : chunkCheck 45 = true := by decide +kernel

lemma chunk_check_46 : chunkCheck 46 = true := by decide +kernel

lemma chunk_check_47 : chunkCheck 47 = true := by decide +kernel

lemma chunk_check_48 : chunkCheck 48 = true := by decide +kernel

lemma chunk_check_49 : chunkCheck 49 = true := by decide +kernel

lemma chunk_check_50 : chunkCheck 50 = true := by decide +kernel

lemma chunk_check_51 : chunkCheck 51 = true := by decide +kernel

lemma chunk_check_52 : chunkCheck 52 = true := by decide +kernel

lemma chunk_check_53 : chunkCheck 53 = true := by decide +kernel

lemma chunk_check_54 : chunkCheck 54 = true := by decide +kernel

lemma chunk_check_55 : chunkCheck 55 = true := by decide +kernel

lemma chunk_check_56 : chunkCheck 56 = true := by decide +kernel

lemma chunk_check_57 : chunkCheck 57 = true := by decide +kernel

lemma chunk_check_58 : chunkCheck 58 = true := by decide +kernel

lemma chunk_check_59 : chunkCheck 59 = true := by decide +kernel

lemma chunk_check_60 : chunkCheck 60 = true := by decide +kernel

lemma chunk_check_61 : chunkCheck 61 = true := by decide +kernel

lemma chunk_check_62 : chunkCheck 62 = true := by decide +kernel

lemma chunk_check_63 : chunkCheck 63 = true := by decide +kernel

lemma chunk_check_64 : chunkCheck 64 = true := by decide +kernel

lemma chunk_check_65 : chunkCheck 65 = true := by decide +kernel

lemma chunk_check_66 : chunkCheck 66 = true := by decide +kernel

lemma chunk_check_67 : chunkCheck 67 = true := by decide +kernel

lemma chunk_check_68 : chunkCheck 68 = true := by decide +kernel

lemma chunk_check_69 : chunkCheck 69 = true := by decide +kernel

lemma chunk_check_70 : chunkCheck 70 = true := by decide +kernel

lemma chunk_check_71 : chunkCheck 71 = true := by decide +kernel

lemma chunk_check_72 : chunkCheck 72 = true := by decide +kernel

lemma chunk_check_73 : chunkCheck 73 = true := by decide +kernel

lemma chunk_check_74 : chunkCheck 74 = true := by decide +kernel

lemma chunk_check_75 : chunkCheck 75 = true := by decide +kernel

lemma chunk_check_76 : chunkCheck 76 = true := by decide +kernel

lemma chunk_check_77 : chunkCheck 77 = true := by decide +kernel

lemma chunk_check_78 : chunkCheck 78 = true := by decide +kernel

lemma chunk_check_79 : chunkCheck 79 = true := by decide +kernel

lemma chunk_check_80 : chunkCheck 80 = true := by decide +kernel

lemma chunk_check_81 : chunkCheck 81 = true := by decide +kernel

lemma chunk_check_82 : chunkCheck 82 = true := by decide +kernel

lemma chunk_check_83 : chunkCheck 83 = true := by decide +kernel

lemma chunk_check_84 : chunkCheck 84 = true := by decide +kernel

lemma chunk_check_85 : chunkCheck 85 = true := by decide +kernel

lemma chunk_check_86 : chunkCheck 86 = true := by decide +kernel

lemma chunk_check_87 : chunkCheck 87 = true := by decide +kernel

lemma chunk_check_88 : chunkCheck 88 = true := by decide +kernel

lemma chunk_check_89 : chunkCheck 89 = true := by decide +kernel

lemma chunk_check_90 : chunkCheck 90 = true := by decide +kernel

lemma chunk_check_91 : chunkCheck 91 = true := by decide +kernel

lemma chunk_check_92 : chunkCheck 92 = true := by decide +kernel

lemma chunk_check_93 : chunkCheck 93 = true := by decide +kernel

lemma chunk_check_94 : chunkCheck 94 = true := by decide +kernel

lemma chunk_check_95 : chunkCheck 95 = true := by decide +kernel

lemma chunk_check_96 : chunkCheck 96 = true := by decide +kernel

lemma chunk_check_97 : chunkCheck 97 = true := by decide +kernel

lemma chunk_check_98 : chunkCheck 98 = true := by decide +kernel

lemma chunk_check_99 : chunkCheck 99 = true := by decide +kernel

lemma chunk_check_100 : chunkCheck 100 = true := by decide +kernel

lemma chunk_check_101 : chunkCheck 101 = true := by decide +kernel

lemma chunk_check_102 : chunkCheck 102 = true := by decide +kernel

lemma chunk_check_103 : chunkCheck 103 = true := by decide +kernel

lemma chunk_check_104 : chunkCheck 104 = true := by decide +kernel

lemma chunk_check_105 : chunkCheck 105 = true := by decide +kernel

lemma chunk_check_106 : chunkCheck 106 = true := by decide +kernel

lemma chunk_check_107 : chunkCheck 107 = true := by decide +kernel

lemma chunk_check_108 : chunkCheck 108 = true := by decide +kernel

lemma chunk_check_109 : chunkCheck 109 = true := by decide +kernel

lemma chunk_check_110 : chunkCheck 110 = true := by decide +kernel

lemma chunk_check_111 : chunkCheck 111 = true := by decide +kernel

lemma chunk_check_112 : chunkCheck 112 = true := by decide +kernel

lemma chunk_check_113 : chunkCheck 113 = true := by decide +kernel

lemma chunk_check_114 : chunkCheck 114 = true := by decide +kernel

lemma chunk_check_115 : chunkCheck 115 = true := by decide +kernel

lemma chunk_check_116 : chunkCheck 116 = true := by decide +kernel

lemma chunk_check_117 : chunkCheck 117 = true := by decide +kernel

lemma chunk_check_118 : chunkCheck 118 = true := by decide +kernel

lemma chunk_check_119 : chunkCheck 119 = true := by decide +kernel

lemma chunk_check_120 : chunkCheck 120 = true := by decide +kernel

lemma chunk_check_121 : chunkCheck 121 = true := by decide +kernel

lemma chunk_check_122 : chunkCheck 122 = true := by decide +kernel

lemma chunk_check_123 : chunkCheck 123 = true := by decide +kernel

lemma chunk_check_124 : chunkCheck 124 = true := by decide +kernel

lemma chunk_check_125 : chunkCheck 125 = true := by decide +kernel

lemma chunk_check_126 : chunkCheck 126 = true := by decide +kernel

lemma chunk_check_127 : chunkCheck 127 = true := by decide +kernel

lemma chunk_check_128 : chunkCheck 128 = true := by decide +kernel

lemma chunk_check_129 : chunkCheck 129 = true := by decide +kernel

lemma chunk_check_130 : chunkCheck 130 = true := by decide +kernel

lemma chunk_check_131 : chunkCheck 131 = true := by decide +kernel

lemma chunk_check_132 : chunkCheck 132 = true := by decide +kernel

lemma chunk_check_133 : chunkCheck 133 = true := by decide +kernel

lemma chunk_check_134 : chunkCheck 134 = true := by decide +kernel

lemma chunk_check_135 : chunkCheck 135 = true := by decide +kernel

lemma chunk_check_136 : chunkCheck 136 = true := by decide +kernel

lemma chunk_check_137 : chunkCheck 137 = true := by decide +kernel

lemma chunk_check_138 : chunkCheck 138 = true := by decide +kernel

lemma chunk_check_139 : chunkCheck 139 = true := by decide +kernel

lemma chunk_check_140 : chunkCheck 140 = true := by decide +kernel

lemma chunk_check_141 : chunkCheck 141 = true := by decide +kernel

lemma chunk_check_142 : chunkCheck 142 = true := by decide +kernel

lemma chunk_check_143 : chunkCheck 143 = true := by decide +kernel

lemma chunk_check_144 : chunkCheck 144 = true := by decide +kernel

lemma chunk_check_145 : chunkCheck 145 = true := by decide +kernel

lemma chunk_check_146 : chunkCheck 146 = true := by decide +kernel

lemma chunk_check_147 : chunkCheck 147 = true := by decide +kernel

lemma chunk_check_148 : chunkCheck 148 = true := by decide +kernel

lemma chunk_check_149 : chunkCheck 149 = true := by decide +kernel

lemma chunk_check_150 : chunkCheck 150 = true := by decide +kernel

lemma chunk_check_151 : chunkCheck 151 = true := by decide +kernel

lemma chunk_check_152 : chunkCheck 152 = true := by decide +kernel

lemma chunk_check_153 : chunkCheck 153 = true := by decide +kernel

lemma chunk_check_154 : chunkCheck 154 = true := by decide +kernel

lemma chunk_check_155 : chunkCheck 155 = true := by decide +kernel

lemma chunk_check_156 : chunkCheck 156 = true := by decide +kernel

lemma chunk_check_157 : chunkCheck 157 = true := by decide +kernel

lemma chunk_check_158 : chunkCheck 158 = true := by decide +kernel

lemma chunk_check_159 : chunkCheck 159 = true := by decide +kernel

lemma chunk_check_160 : chunkCheck 160 = true := by decide +kernel

lemma chunk_check_161 : chunkCheck 161 = true := by decide +kernel

lemma chunk_check_162 : chunkCheck 162 = true := by decide +kernel

lemma chunk_check_163 : chunkCheck 163 = true := by decide +kernel

lemma chunk_check_164 : chunkCheck 164 = true := by decide +kernel

lemma chunk_check_165 : chunkCheck 165 = true := by decide +kernel

lemma chunk_check_166 : chunkCheck 166 = true := by decide +kernel

lemma chunk_check_167 : chunkCheck 167 = true := by decide +kernel

lemma chunk_check_168 : chunkCheck 168 = true := by decide +kernel

lemma chunk_check_169 : chunkCheck 169 = true := by decide +kernel

lemma chunk_check_170 : chunkCheck 170 = true := by decide +kernel

lemma chunk_check_171 : chunkCheck 171 = true := by decide +kernel

lemma chunk_check_172 : chunkCheck 172 = true := by decide +kernel

lemma chunk_check_173 : chunkCheck 173 = true := by decide +kernel

lemma chunk_check_174 : chunkCheck 174 = true := by decide +kernel

lemma chunk_check_175 : chunkCheck 175 = true := by decide +kernel

lemma chunk_check_176 : chunkCheck 176 = true := by decide +kernel

lemma chunk_check_177 : chunkCheck 177 = true := by decide +kernel

lemma chunk_check_178 : chunkCheck 178 = true := by decide +kernel

lemma chunk_check_179 : chunkCheck 179 = true := by decide +kernel

lemma chunk_check_180 : chunkCheck 180 = true := by decide +kernel

lemma chunk_check_181 : chunkCheck 181 = true := by decide +kernel

lemma chunk_check_182 : chunkCheck 182 = true := by decide +kernel

lemma chunk_check_183 : chunkCheck 183 = true := by decide +kernel

lemma chunk_check_184 : chunkCheck 184 = true := by decide +kernel

lemma chunk_check_185 : chunkCheck 185 = true := by decide +kernel

lemma chunk_check_186 : chunkCheck 186 = true := by decide +kernel

lemma chunk_check_187 : chunkCheck 187 = true := by decide +kernel

lemma chunk_check_188 : chunkCheck 188 = true := by decide +kernel

lemma chunk_check_189 : chunkCheck 189 = true := by decide +kernel

lemma chunk_check_190 : chunkCheck 190 = true := by decide +kernel

lemma chunk_check_191 : chunkCheck 191 = true := by decide +kernel

lemma chunk_check_192 : chunkCheck 192 = true := by decide +kernel

lemma chunk_check_193 : chunkCheck 193 = true := by decide +kernel

lemma chunk_check_194 : chunkCheck 194 = true := by decide +kernel

lemma chunk_check_195 : chunkCheck 195 = true := by decide +kernel

lemma chunk_check_196 : chunkCheck 196 = true := by decide +kernel

lemma chunk_check_197 : chunkCheck 197 = true := by decide +kernel

lemma chunk_check_198 : chunkCheck 198 = true := by decide +kernel

lemma chunk_check_199 : chunkCheck 199 = true := by decide +kernel

lemma chunk_check_200 : chunkCheck 200 = true := by decide +kernel

lemma chunk_check_201 : chunkCheck 201 = true := by decide +kernel

lemma chunk_check_202 : chunkCheck 202 = true := by decide +kernel

lemma chunk_check_203 : chunkCheck 203 = true := by decide +kernel

lemma chunk_check_204 : chunkCheck 204 = true := by decide +kernel

lemma chunk_check_205 : chunkCheck 205 = true := by decide +kernel

lemma chunk_check_206 : chunkCheck 206 = true := by decide +kernel

lemma chunk_check_207 : chunkCheck 207 = true := by decide +kernel

lemma chunk_check_208 : chunkCheck 208 = true := by decide +kernel

lemma chunk_check_209 : chunkCheck 209 = true := by decide +kernel

lemma chunk_check_210 : chunkCheck 210 = true := by decide +kernel

lemma chunk_check_211 : chunkCheck 211 = true := by decide +kernel

lemma chunk_check_212 : chunkCheck 212 = true := by decide +kernel

lemma chunk_check_213 : chunkCheck 213 = true := by decide +kernel

lemma chunk_check_214 : chunkCheck 214 = true := by decide +kernel

lemma chunk_check_215 : chunkCheck 215 = true := by decide +kernel

lemma chunk_check_216 : chunkCheck 216 = true := by decide +kernel

lemma chunk_check_217 : chunkCheck 217 = true := by decide +kernel

lemma chunk_check_218 : chunkCheck 218 = true := by decide +kernel

lemma chunk_check_219 : chunkCheck 219 = true := by decide +kernel

lemma chunk_check_220 : chunkCheck 220 = true := by decide +kernel

lemma chunk_check_221 : chunkCheck 221 = true := by decide +kernel

lemma chunk_check_222 : chunkCheck 222 = true := by decide +kernel

lemma chunk_check_223 : chunkCheck 223 = true := by decide +kernel

lemma chunk_check_224 : chunkCheck 224 = true := by decide +kernel

lemma chunk_check_225 : chunkCheck 225 = true := by decide +kernel

lemma chunk_check_226 : chunkCheck 226 = true := by decide +kernel

lemma chunk_check_227 : chunkCheck 227 = true := by decide +kernel

lemma chunk_check_228 : chunkCheck 228 = true := by decide +kernel

lemma chunk_check_229 : chunkCheck 229 = true := by decide +kernel

lemma chunk_check_230 : chunkCheck 230 = true := by decide +kernel

lemma chunk_check_231 : chunkCheck 231 = true := by decide +kernel

lemma chunk_check_232 : chunkCheck 232 = true := by decide +kernel

lemma chunk_check_233 : chunkCheck 233 = true := by decide +kernel

lemma chunk_check_234 : chunkCheck 234 = true := by decide +kernel

lemma chunk_check_235 : chunkCheck 235 = true := by decide +kernel

lemma all_chunks_checked : ∀ c : Fin 236, chunkCheck c = true := by
  exact (Fin.cases chunk_check_0 (Fin.cases chunk_check_1 (Fin.cases chunk_check_2 (Fin.cases chunk_check_3 (Fin.cases chunk_check_4 (Fin.cases chunk_check_5 (Fin.cases chunk_check_6 (Fin.cases chunk_check_7 (Fin.cases chunk_check_8 (Fin.cases chunk_check_9 (Fin.cases chunk_check_10 (Fin.cases chunk_check_11 (Fin.cases chunk_check_12 (Fin.cases chunk_check_13 (Fin.cases chunk_check_14 (Fin.cases chunk_check_15 (Fin.cases chunk_check_16 (Fin.cases chunk_check_17 (Fin.cases chunk_check_18 (Fin.cases chunk_check_19 (Fin.cases chunk_check_20 (Fin.cases chunk_check_21 (Fin.cases chunk_check_22 (Fin.cases chunk_check_23 (Fin.cases chunk_check_24 (Fin.cases chunk_check_25 (Fin.cases chunk_check_26 (Fin.cases chunk_check_27 (Fin.cases chunk_check_28 (Fin.cases chunk_check_29 (Fin.cases chunk_check_30 (Fin.cases chunk_check_31 (Fin.cases chunk_check_32 (Fin.cases chunk_check_33 (Fin.cases chunk_check_34 (Fin.cases chunk_check_35 (Fin.cases chunk_check_36 (Fin.cases chunk_check_37 (Fin.cases chunk_check_38 (Fin.cases chunk_check_39 (Fin.cases chunk_check_40 (Fin.cases chunk_check_41 (Fin.cases chunk_check_42 (Fin.cases chunk_check_43 (Fin.cases chunk_check_44 (Fin.cases chunk_check_45 (Fin.cases chunk_check_46 (Fin.cases chunk_check_47 (Fin.cases chunk_check_48 (Fin.cases chunk_check_49 (Fin.cases chunk_check_50 (Fin.cases chunk_check_51 (Fin.cases chunk_check_52 (Fin.cases chunk_check_53 (Fin.cases chunk_check_54 (Fin.cases chunk_check_55 (Fin.cases chunk_check_56 (Fin.cases chunk_check_57 (Fin.cases chunk_check_58 (Fin.cases chunk_check_59 (Fin.cases chunk_check_60 (Fin.cases chunk_check_61 (Fin.cases chunk_check_62 (Fin.cases chunk_check_63 (Fin.cases chunk_check_64 (Fin.cases chunk_check_65 (Fin.cases chunk_check_66 (Fin.cases chunk_check_67 (Fin.cases chunk_check_68 (Fin.cases chunk_check_69 (Fin.cases chunk_check_70 (Fin.cases chunk_check_71 (Fin.cases chunk_check_72 (Fin.cases chunk_check_73 (Fin.cases chunk_check_74 (Fin.cases chunk_check_75 (Fin.cases chunk_check_76 (Fin.cases chunk_check_77 (Fin.cases chunk_check_78 (Fin.cases chunk_check_79 (Fin.cases chunk_check_80 (Fin.cases chunk_check_81 (Fin.cases chunk_check_82 (Fin.cases chunk_check_83 (Fin.cases chunk_check_84 (Fin.cases chunk_check_85 (Fin.cases chunk_check_86 (Fin.cases chunk_check_87 (Fin.cases chunk_check_88 (Fin.cases chunk_check_89 (Fin.cases chunk_check_90 (Fin.cases chunk_check_91 (Fin.cases chunk_check_92 (Fin.cases chunk_check_93 (Fin.cases chunk_check_94 (Fin.cases chunk_check_95 (Fin.cases chunk_check_96 (Fin.cases chunk_check_97 (Fin.cases chunk_check_98 (Fin.cases chunk_check_99 (Fin.cases chunk_check_100 (Fin.cases chunk_check_101 (Fin.cases chunk_check_102 (Fin.cases chunk_check_103 (Fin.cases chunk_check_104 (Fin.cases chunk_check_105 (Fin.cases chunk_check_106 (Fin.cases chunk_check_107 (Fin.cases chunk_check_108 (Fin.cases chunk_check_109 (Fin.cases chunk_check_110 (Fin.cases chunk_check_111 (Fin.cases chunk_check_112 (Fin.cases chunk_check_113 (Fin.cases chunk_check_114 (Fin.cases chunk_check_115 (Fin.cases chunk_check_116 (Fin.cases chunk_check_117 (Fin.cases chunk_check_118 (Fin.cases chunk_check_119 (Fin.cases chunk_check_120 (Fin.cases chunk_check_121 (Fin.cases chunk_check_122 (Fin.cases chunk_check_123 (Fin.cases chunk_check_124 (Fin.cases chunk_check_125 (Fin.cases chunk_check_126 (Fin.cases chunk_check_127 (Fin.cases chunk_check_128 (Fin.cases chunk_check_129 (Fin.cases chunk_check_130 (Fin.cases chunk_check_131 (Fin.cases chunk_check_132 (Fin.cases chunk_check_133 (Fin.cases chunk_check_134 (Fin.cases chunk_check_135 (Fin.cases chunk_check_136 (Fin.cases chunk_check_137 (Fin.cases chunk_check_138 (Fin.cases chunk_check_139 (Fin.cases chunk_check_140 (Fin.cases chunk_check_141 (Fin.cases chunk_check_142 (Fin.cases chunk_check_143 (Fin.cases chunk_check_144 (Fin.cases chunk_check_145 (Fin.cases chunk_check_146 (Fin.cases chunk_check_147 (Fin.cases chunk_check_148 (Fin.cases chunk_check_149 (Fin.cases chunk_check_150 (Fin.cases chunk_check_151 (Fin.cases chunk_check_152 (Fin.cases chunk_check_153 (Fin.cases chunk_check_154 (Fin.cases chunk_check_155 (Fin.cases chunk_check_156 (Fin.cases chunk_check_157 (Fin.cases chunk_check_158 (Fin.cases chunk_check_159 (Fin.cases chunk_check_160 (Fin.cases chunk_check_161 (Fin.cases chunk_check_162 (Fin.cases chunk_check_163 (Fin.cases chunk_check_164 (Fin.cases chunk_check_165 (Fin.cases chunk_check_166 (Fin.cases chunk_check_167 (Fin.cases chunk_check_168 (Fin.cases chunk_check_169 (Fin.cases chunk_check_170 (Fin.cases chunk_check_171 (Fin.cases chunk_check_172 (Fin.cases chunk_check_173 (Fin.cases chunk_check_174 (Fin.cases chunk_check_175 (Fin.cases chunk_check_176 (Fin.cases chunk_check_177 (Fin.cases chunk_check_178 (Fin.cases chunk_check_179 (Fin.cases chunk_check_180 (Fin.cases chunk_check_181 (Fin.cases chunk_check_182 (Fin.cases chunk_check_183 (Fin.cases chunk_check_184 (Fin.cases chunk_check_185 (Fin.cases chunk_check_186 (Fin.cases chunk_check_187 (Fin.cases chunk_check_188 (Fin.cases chunk_check_189 (Fin.cases chunk_check_190 (Fin.cases chunk_check_191 (Fin.cases chunk_check_192 (Fin.cases chunk_check_193 (Fin.cases chunk_check_194 (Fin.cases chunk_check_195 (Fin.cases chunk_check_196 (Fin.cases chunk_check_197 (Fin.cases chunk_check_198 (Fin.cases chunk_check_199 (Fin.cases chunk_check_200 (Fin.cases chunk_check_201 (Fin.cases chunk_check_202 (Fin.cases chunk_check_203 (Fin.cases chunk_check_204 (Fin.cases chunk_check_205 (Fin.cases chunk_check_206 (Fin.cases chunk_check_207 (Fin.cases chunk_check_208 (Fin.cases chunk_check_209 (Fin.cases chunk_check_210 (Fin.cases chunk_check_211 (Fin.cases chunk_check_212 (Fin.cases chunk_check_213 (Fin.cases chunk_check_214 (Fin.cases chunk_check_215 (Fin.cases chunk_check_216 (Fin.cases chunk_check_217 (Fin.cases chunk_check_218 (Fin.cases chunk_check_219 (Fin.cases chunk_check_220 (Fin.cases chunk_check_221 (Fin.cases chunk_check_222 (Fin.cases chunk_check_223 (Fin.cases chunk_check_224 (Fin.cases chunk_check_225 (Fin.cases chunk_check_226 (Fin.cases chunk_check_227 (Fin.cases chunk_check_228 (Fin.cases chunk_check_229 (Fin.cases chunk_check_230 (Fin.cases chunk_check_231 (Fin.cases chunk_check_232 (Fin.cases chunk_check_233 (Fin.cases chunk_check_234 (Fin.cases chunk_check_235 (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

lemma all_rootChecks : ∀ r : Fin 31, rootCheck r = true := by
  intro r
  have hb : PackingPrunedDFS.branches ok step
      (PackingPrunedDFS.check ok step good prune 25)
      (rootState r) (rootCandidates r) = true := by
    apply PackingPrunedDFS.branches_of_branchAt
    intro i hi
    have hm : i ∈ ((rootChunkIndices r).flatMap fun c =>
        (List.range (chunkData c).2.2).map fun j => (chunkData c).2.1 + j) := by
      rw [chunk_coverage]
      exact List.mem_range.mpr hi
    obtain ⟨c, hc, hj⟩ := List.mem_flatMap.mp hm
    obtain ⟨j, hmem, heq⟩ := List.mem_map.mp hj
    have hcheck : PackingPrunedDFS.chunk ok step
        (PackingPrunedDFS.check ok step good prune 25)
        (rootState r) (rootCandidates r) (chunkData c).2.1 (chunkData c).2.2 = true := by
      have h := all_chunks_checked c
      simpa only [chunkCheck, chunk_roots r c hc] using h
    have h := PackingPrunedDFS.branchAt_of_chunk ok step
      (PackingPrunedDFS.check ok step good prune 25)
      (rootState r) (rootCandidates r) (chunkData c).2.1 (chunkData c).2.2 j
      hcheck (List.mem_range.mp hmem)
    simpa only [heq] using h
  unfold rootCheck
  rw [PackingPrunedDFS.check, roots_good r, hb]
  simp

end PackingThree
end PEqualNP.Outside.L_meta_1896_aux
