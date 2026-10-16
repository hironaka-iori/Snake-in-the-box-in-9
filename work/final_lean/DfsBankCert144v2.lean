import DfsBankCert144v2_j57c60
import DfsBankCert144v2_j52c60
import DfsBankCert144v2_j59c60
import DfsBankCert144v2_j78c32
import DfsBankCert144v2_j63c31
import DfsBankCert144v2_j186c31
import DfsBankCert144v2_j50c28
import DfsBankCert144v2_j55c28
import DfsBankCert144v2_j255c13
import DfsBankCert144v2_j257c13
import DfsBankCert144v2_j259c13
import DfsBankCert144v2_j261c13
import DfsBankCert144v2_j68c12
import DfsBankCert144v2_j81c12
import DfsBankCert144v2_j191c12
import DfsBankCert144v2_j203c12
import DfsBankCert144v2_j74c12
import DfsBankCert144v2_j93c12
import DfsBankCert144v2_j115c12
import DfsBankCert144v2_j117c12
import DfsBankCert144v2_j198c12
import DfsBankCert144v2_j213c12
import DfsBankCert144v2_j215c12
import DfsBankCert144v2_j217c12
import DfsBankCert144v2_j64c11
import DfsBankCert144v2_j77c11
import DfsBankCert144v2_j193c9
import DfsBankCert144v2_j207c9
import DfsBankCert144v2_j6c5
import DfsBankCert144v2_j20c5
import DfsBankCert144v2_j22c5
import DfsBankCert144v2_j5c5
import DfsBankCert144v2_j41c5
import DfsBankCert144v2_j105c4
import DfsBankCert144v2_j89c3
import DfsBankCert144v2_j146c3
import DfsBankCert144v2_j171c3
import DfsBankCert144v2_j90c2
import DfsBankCert144v2_j183c2
import DfsBankCert144v2_j158c1
import DfsBankCert144v2_j94c1
import DfsBankCert144v2_j167c1
import DfsBankCert144v2_j173c1
import DfsBankCert144v2_j11c1
import DfsBankCert144v2_j17c1
import DfsBankCert144v2_j168c1
import DfsBankCert144v2_j1c1
import DfsBankCert144v2_j14c1
import DfsBankCert144v2_j161c1
import DfsBankCert144v2_j24c1
import DfsBankCert144v2_j150c1
import DfsBankCert144v2_j148c1
import DfsBankCert144v2_j0c1
import DfsBankCert144v2_j10c1
import DfsBankCert144v2_j16c1
import DfsBankCert144v2_g0
import DfsBankCert144v2_g1
import DfsBankCert144v2_g2
import DfsBankCert144v2_g3
import DfsBankCert144v2_g4
import DfsBankCert144v2_g5
import DfsBankCert144v2_g6
import DfsBankCert144v2_g7
import DfsBankCert144v2_g8
import DfsBankCert144v2_g9
import DfsBankCert144v2_g10
import DfsBankCert144v2_g11
import DfsBankCert144v2_g12
import DfsBankCert144v2_g13
import DfsBankCert144v2_g14
import DfsBankCert144v2_g15
import DfsBankCert144v2_g16
import DfsBankCert144v2_g17
import DfsBankCert144v2_g18
import DfsBankCert144v2_g19
import DfsBankCert144v2_g20
import DfsBankCert144v2_g21
import DfsBankCert144v2_g22
import DfsBankCert144v2_g23
import DfsBankCert144v2_g24
import DfsBankCert144v2_g25
import DfsBankCert144v2_g26
import DfsBankCert144v2_g27
import DfsBankCert144v2_g28
import DfsBankCert144v2_g29
import DfsBankCert144v2_g30
import DfsBankCert144v2_g31
import DfsBankCert144v2_g32
import DfsBankCert144v2_g33
import DfsBankCert144v2_g34
import DfsBankCert144v2_g35
import DfsBankCert144v2_g36
import DfsBankCert144v2_g37
import DfsBankCert144v2_g38
import DfsBankCert144v2_g39
import DfsBankCert144v2_g40
import DfsBankCert144v2_g41

namespace Snake9.Dfs
set_option maxRecDepth 100000

theorem search_keep144v2 (j : Nat) (hj : j < 262) :
    search2 (oriented j)[143]! (banFrom (fun i => (oriented j)[i]!) 143) 49 = false := by
  match j, hj with
  | 0, _ => exact keep144v2_0
  | 1, _ => exact keep144v2_1
  | 2, _ => exact keep144v2_2
  | 3, _ => exact keep144v2_3
  | 4, _ => exact keep144v2_4
  | 5, _ => exact keep144v2_5
  | 6, _ => exact keep144v2_6
  | 7, _ => exact keep144v2_7
  | 8, _ => exact keep144v2_8
  | 9, _ => exact keep144v2_9
  | 10, _ => exact keep144v2_10
  | 11, _ => exact keep144v2_11
  | 12, _ => exact keep144v2_12
  | 13, _ => exact keep144v2_13
  | 14, _ => exact keep144v2_14
  | 15, _ => exact keep144v2_15
  | 16, _ => exact keep144v2_16
  | 17, _ => exact keep144v2_17
  | 18, _ => exact keep144v2_18
  | 19, _ => exact keep144v2_19
  | 20, _ => exact keep144v2_20
  | 21, _ => exact keep144v2_21
  | 22, _ => exact keep144v2_22
  | 23, _ => exact keep144v2_23
  | 24, _ => exact keep144v2_24
  | 25, _ => exact keep144v2_25
  | 26, _ => exact keep144v2_26
  | 27, _ => exact keep144v2_27
  | 28, _ => exact keep144v2_28
  | 29, _ => exact keep144v2_29
  | 30, _ => exact keep144v2_30
  | 31, _ => exact keep144v2_31
  | 32, _ => exact keep144v2_32
  | 33, _ => exact keep144v2_33
  | 34, _ => exact keep144v2_34
  | 35, _ => exact keep144v2_35
  | 36, _ => exact keep144v2_36
  | 37, _ => exact keep144v2_37
  | 38, _ => exact keep144v2_38
  | 39, _ => exact keep144v2_39
  | 40, _ => exact keep144v2_40
  | 41, _ => exact keep144v2_41
  | 42, _ => exact keep144v2_42
  | 43, _ => exact keep144v2_43
  | 44, _ => exact keep144v2_44
  | 45, _ => exact keep144v2_45
  | 46, _ => exact keep144v2_46
  | 47, _ => exact keep144v2_47
  | 48, _ => exact keep144v2_48
  | 49, _ => exact keep144v2_49
  | 50, _ => exact keep144v2_50
  | 51, _ => exact keep144v2_51
  | 52, _ => exact keep144v2_52
  | 53, _ => exact keep144v2_53
  | 54, _ => exact keep144v2_54
  | 55, _ => exact keep144v2_55
  | 56, _ => exact keep144v2_56
  | 57, _ => exact keep144v2_57
  | 58, _ => exact keep144v2_58
  | 59, _ => exact keep144v2_59
  | 60, _ => exact keep144v2_60
  | 61, _ => exact keep144v2_61
  | 62, _ => exact keep144v2_62
  | 63, _ => exact keep144v2_63
  | 64, _ => exact keep144v2_64
  | 65, _ => exact keep144v2_65
  | 66, _ => exact keep144v2_66
  | 67, _ => exact keep144v2_67
  | 68, _ => exact keep144v2_68
  | 69, _ => exact keep144v2_69
  | 70, _ => exact keep144v2_70
  | 71, _ => exact keep144v2_71
  | 72, _ => exact keep144v2_72
  | 73, _ => exact keep144v2_73
  | 74, _ => exact keep144v2_74
  | 75, _ => exact keep144v2_75
  | 76, _ => exact keep144v2_76
  | 77, _ => exact keep144v2_77
  | 78, _ => exact keep144v2_78
  | 79, _ => exact keep144v2_79
  | 80, _ => exact keep144v2_80
  | 81, _ => exact keep144v2_81
  | 82, _ => exact keep144v2_82
  | 83, _ => exact keep144v2_83
  | 84, _ => exact keep144v2_84
  | 85, _ => exact keep144v2_85
  | 86, _ => exact keep144v2_86
  | 87, _ => exact keep144v2_87
  | 88, _ => exact keep144v2_88
  | 89, _ => exact keep144v2_89
  | 90, _ => exact keep144v2_90
  | 91, _ => exact keep144v2_91
  | 92, _ => exact keep144v2_92
  | 93, _ => exact keep144v2_93
  | 94, _ => exact keep144v2_94
  | 95, _ => exact keep144v2_95
  | 96, _ => exact keep144v2_96
  | 97, _ => exact keep144v2_97
  | 98, _ => exact keep144v2_98
  | 99, _ => exact keep144v2_99
  | 100, _ => exact keep144v2_100
  | 101, _ => exact keep144v2_101
  | 102, _ => exact keep144v2_102
  | 103, _ => exact keep144v2_103
  | 104, _ => exact keep144v2_104
  | 105, _ => exact keep144v2_105
  | 106, _ => exact keep144v2_106
  | 107, _ => exact keep144v2_107
  | 108, _ => exact keep144v2_108
  | 109, _ => exact keep144v2_109
  | 110, _ => exact keep144v2_110
  | 111, _ => exact keep144v2_111
  | 112, _ => exact keep144v2_112
  | 113, _ => exact keep144v2_113
  | 114, _ => exact keep144v2_114
  | 115, _ => exact keep144v2_115
  | 116, _ => exact keep144v2_116
  | 117, _ => exact keep144v2_117
  | 118, _ => exact keep144v2_118
  | 119, _ => exact keep144v2_119
  | 120, _ => exact keep144v2_120
  | 121, _ => exact keep144v2_121
  | 122, _ => exact keep144v2_122
  | 123, _ => exact keep144v2_123
  | 124, _ => exact keep144v2_124
  | 125, _ => exact keep144v2_125
  | 126, _ => exact keep144v2_126
  | 127, _ => exact keep144v2_127
  | 128, _ => exact keep144v2_128
  | 129, _ => exact keep144v2_129
  | 130, _ => exact keep144v2_130
  | 131, _ => exact keep144v2_131
  | 132, _ => exact keep144v2_132
  | 133, _ => exact keep144v2_133
  | 134, _ => exact keep144v2_134
  | 135, _ => exact keep144v2_135
  | 136, _ => exact keep144v2_136
  | 137, _ => exact keep144v2_137
  | 138, _ => exact keep144v2_138
  | 139, _ => exact keep144v2_139
  | 140, _ => exact keep144v2_140
  | 141, _ => exact keep144v2_141
  | 142, _ => exact keep144v2_142
  | 143, _ => exact keep144v2_143
  | 144, _ => exact keep144v2_144
  | 145, _ => exact keep144v2_145
  | 146, _ => exact keep144v2_146
  | 147, _ => exact keep144v2_147
  | 148, _ => exact keep144v2_148
  | 149, _ => exact keep144v2_149
  | 150, _ => exact keep144v2_150
  | 151, _ => exact keep144v2_151
  | 152, _ => exact keep144v2_152
  | 153, _ => exact keep144v2_153
  | 154, _ => exact keep144v2_154
  | 155, _ => exact keep144v2_155
  | 156, _ => exact keep144v2_156
  | 157, _ => exact keep144v2_157
  | 158, _ => exact keep144v2_158
  | 159, _ => exact keep144v2_159
  | 160, _ => exact keep144v2_160
  | 161, _ => exact keep144v2_161
  | 162, _ => exact keep144v2_162
  | 163, _ => exact keep144v2_163
  | 164, _ => exact keep144v2_164
  | 165, _ => exact keep144v2_165
  | 166, _ => exact keep144v2_166
  | 167, _ => exact keep144v2_167
  | 168, _ => exact keep144v2_168
  | 169, _ => exact keep144v2_169
  | 170, _ => exact keep144v2_170
  | 171, _ => exact keep144v2_171
  | 172, _ => exact keep144v2_172
  | 173, _ => exact keep144v2_173
  | 174, _ => exact keep144v2_174
  | 175, _ => exact keep144v2_175
  | 176, _ => exact keep144v2_176
  | 177, _ => exact keep144v2_177
  | 178, _ => exact keep144v2_178
  | 179, _ => exact keep144v2_179
  | 180, _ => exact keep144v2_180
  | 181, _ => exact keep144v2_181
  | 182, _ => exact keep144v2_182
  | 183, _ => exact keep144v2_183
  | 184, _ => exact keep144v2_184
  | 185, _ => exact keep144v2_185
  | 186, _ => exact keep144v2_186
  | 187, _ => exact keep144v2_187
  | 188, _ => exact keep144v2_188
  | 189, _ => exact keep144v2_189
  | 190, _ => exact keep144v2_190
  | 191, _ => exact keep144v2_191
  | 192, _ => exact keep144v2_192
  | 193, _ => exact keep144v2_193
  | 194, _ => exact keep144v2_194
  | 195, _ => exact keep144v2_195
  | 196, _ => exact keep144v2_196
  | 197, _ => exact keep144v2_197
  | 198, _ => exact keep144v2_198
  | 199, _ => exact keep144v2_199
  | 200, _ => exact keep144v2_200
  | 201, _ => exact keep144v2_201
  | 202, _ => exact keep144v2_202
  | 203, _ => exact keep144v2_203
  | 204, _ => exact keep144v2_204
  | 205, _ => exact keep144v2_205
  | 206, _ => exact keep144v2_206
  | 207, _ => exact keep144v2_207
  | 208, _ => exact keep144v2_208
  | 209, _ => exact keep144v2_209
  | 210, _ => exact keep144v2_210
  | 211, _ => exact keep144v2_211
  | 212, _ => exact keep144v2_212
  | 213, _ => exact keep144v2_213
  | 214, _ => exact keep144v2_214
  | 215, _ => exact keep144v2_215
  | 216, _ => exact keep144v2_216
  | 217, _ => exact keep144v2_217
  | 218, _ => exact keep144v2_218
  | 219, _ => exact keep144v2_219
  | 220, _ => exact keep144v2_220
  | 221, _ => exact keep144v2_221
  | 222, _ => exact keep144v2_222
  | 223, _ => exact keep144v2_223
  | 224, _ => exact keep144v2_224
  | 225, _ => exact keep144v2_225
  | 226, _ => exact keep144v2_226
  | 227, _ => exact keep144v2_227
  | 228, _ => exact keep144v2_228
  | 229, _ => exact keep144v2_229
  | 230, _ => exact keep144v2_230
  | 231, _ => exact keep144v2_231
  | 232, _ => exact keep144v2_232
  | 233, _ => exact keep144v2_233
  | 234, _ => exact keep144v2_234
  | 235, _ => exact keep144v2_235
  | 236, _ => exact keep144v2_236
  | 237, _ => exact keep144v2_237
  | 238, _ => exact keep144v2_238
  | 239, _ => exact keep144v2_239
  | 240, _ => exact keep144v2_240
  | 241, _ => exact keep144v2_241
  | 242, _ => exact keep144v2_242
  | 243, _ => exact keep144v2_243
  | 244, _ => exact keep144v2_244
  | 245, _ => exact keep144v2_245
  | 246, _ => exact keep144v2_246
  | 247, _ => exact keep144v2_247
  | 248, _ => exact keep144v2_248
  | 249, _ => exact keep144v2_249
  | 250, _ => exact keep144v2_250
  | 251, _ => exact keep144v2_251
  | 252, _ => exact keep144v2_252
  | 253, _ => exact keep144v2_253
  | 254, _ => exact keep144v2_254
  | 255, _ => exact keep144v2_255
  | 256, _ => exact keep144v2_256
  | 257, _ => exact keep144v2_257
  | 258, _ => exact keep144v2_258
  | 259, _ => exact keep144v2_259
  | 260, _ => exact keep144v2_260
  | 261, _ => exact keep144v2_261
  | n + 262, h => exact absurd h (by omega)

/-- No 192-edge snake begins with the first 144 vertices of any bank snake, in either
orientation (entry `2*s` of `oriented` is bank snake `s`, entry `2*s+1` its reversal).
Reversing a snake, this also excludes 192-edge snakes ending in those 144 vertices. -/
theorem bank_no192_keep144v2 (j : Nat) (hj : j < 262) :
    ¬ ∃ p : Snake 192, ∀ i (h : i < 144), (p.vertex ⟨i, by omega⟩).val = (oriented j)[i]! :=
  no192_from_prefix2 (oriented j) 144 (by decide) (by decide) (search_keep144v2 j hj)

#print axioms bank_no192_keep144v2
end Snake9.Dfs
