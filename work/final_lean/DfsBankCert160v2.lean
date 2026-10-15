import DfsBankCert160v2_0
import DfsBankCert160v2_1
import DfsBankCert160v2_2
import DfsBankCert160v2_3
import DfsBankCert160v2_4
import DfsBankCert160v2_5
import DfsBankCert160v2_6
import DfsBankCert160v2_7
import DfsBankCert160v2_8
import DfsBankCert160v2_9
import DfsBankCert160v2_10
import DfsBankCert160v2_11
import DfsBankCert160v2_12
import DfsBankCert160v2_13
import DfsBankCert160v2_14
import DfsBankCert160v2_15
import DfsBankCert160v2_16
import DfsBankCert160v2_17
import DfsBankCert160v2_18
import DfsBankCert160v2_19

namespace Snake9.Dfs
set_option maxRecDepth 100000

theorem search_keep160v2 (j : Nat) (hj : j < 262) :
    search2 (oriented j)[159]! (banFrom (fun i => (oriented j)[i]!) 159) 33 = false := by
  match j, hj with
  | 0, _ => exact keep160v2_0
  | 1, _ => exact keep160v2_1
  | 2, _ => exact keep160v2_2
  | 3, _ => exact keep160v2_3
  | 4, _ => exact keep160v2_4
  | 5, _ => exact keep160v2_5
  | 6, _ => exact keep160v2_6
  | 7, _ => exact keep160v2_7
  | 8, _ => exact keep160v2_8
  | 9, _ => exact keep160v2_9
  | 10, _ => exact keep160v2_10
  | 11, _ => exact keep160v2_11
  | 12, _ => exact keep160v2_12
  | 13, _ => exact keep160v2_13
  | 14, _ => exact keep160v2_14
  | 15, _ => exact keep160v2_15
  | 16, _ => exact keep160v2_16
  | 17, _ => exact keep160v2_17
  | 18, _ => exact keep160v2_18
  | 19, _ => exact keep160v2_19
  | 20, _ => exact keep160v2_20
  | 21, _ => exact keep160v2_21
  | 22, _ => exact keep160v2_22
  | 23, _ => exact keep160v2_23
  | 24, _ => exact keep160v2_24
  | 25, _ => exact keep160v2_25
  | 26, _ => exact keep160v2_26
  | 27, _ => exact keep160v2_27
  | 28, _ => exact keep160v2_28
  | 29, _ => exact keep160v2_29
  | 30, _ => exact keep160v2_30
  | 31, _ => exact keep160v2_31
  | 32, _ => exact keep160v2_32
  | 33, _ => exact keep160v2_33
  | 34, _ => exact keep160v2_34
  | 35, _ => exact keep160v2_35
  | 36, _ => exact keep160v2_36
  | 37, _ => exact keep160v2_37
  | 38, _ => exact keep160v2_38
  | 39, _ => exact keep160v2_39
  | 40, _ => exact keep160v2_40
  | 41, _ => exact keep160v2_41
  | 42, _ => exact keep160v2_42
  | 43, _ => exact keep160v2_43
  | 44, _ => exact keep160v2_44
  | 45, _ => exact keep160v2_45
  | 46, _ => exact keep160v2_46
  | 47, _ => exact keep160v2_47
  | 48, _ => exact keep160v2_48
  | 49, _ => exact keep160v2_49
  | 50, _ => exact keep160v2_50
  | 51, _ => exact keep160v2_51
  | 52, _ => exact keep160v2_52
  | 53, _ => exact keep160v2_53
  | 54, _ => exact keep160v2_54
  | 55, _ => exact keep160v2_55
  | 56, _ => exact keep160v2_56
  | 57, _ => exact keep160v2_57
  | 58, _ => exact keep160v2_58
  | 59, _ => exact keep160v2_59
  | 60, _ => exact keep160v2_60
  | 61, _ => exact keep160v2_61
  | 62, _ => exact keep160v2_62
  | 63, _ => exact keep160v2_63
  | 64, _ => exact keep160v2_64
  | 65, _ => exact keep160v2_65
  | 66, _ => exact keep160v2_66
  | 67, _ => exact keep160v2_67
  | 68, _ => exact keep160v2_68
  | 69, _ => exact keep160v2_69
  | 70, _ => exact keep160v2_70
  | 71, _ => exact keep160v2_71
  | 72, _ => exact keep160v2_72
  | 73, _ => exact keep160v2_73
  | 74, _ => exact keep160v2_74
  | 75, _ => exact keep160v2_75
  | 76, _ => exact keep160v2_76
  | 77, _ => exact keep160v2_77
  | 78, _ => exact keep160v2_78
  | 79, _ => exact keep160v2_79
  | 80, _ => exact keep160v2_80
  | 81, _ => exact keep160v2_81
  | 82, _ => exact keep160v2_82
  | 83, _ => exact keep160v2_83
  | 84, _ => exact keep160v2_84
  | 85, _ => exact keep160v2_85
  | 86, _ => exact keep160v2_86
  | 87, _ => exact keep160v2_87
  | 88, _ => exact keep160v2_88
  | 89, _ => exact keep160v2_89
  | 90, _ => exact keep160v2_90
  | 91, _ => exact keep160v2_91
  | 92, _ => exact keep160v2_92
  | 93, _ => exact keep160v2_93
  | 94, _ => exact keep160v2_94
  | 95, _ => exact keep160v2_95
  | 96, _ => exact keep160v2_96
  | 97, _ => exact keep160v2_97
  | 98, _ => exact keep160v2_98
  | 99, _ => exact keep160v2_99
  | 100, _ => exact keep160v2_100
  | 101, _ => exact keep160v2_101
  | 102, _ => exact keep160v2_102
  | 103, _ => exact keep160v2_103
  | 104, _ => exact keep160v2_104
  | 105, _ => exact keep160v2_105
  | 106, _ => exact keep160v2_106
  | 107, _ => exact keep160v2_107
  | 108, _ => exact keep160v2_108
  | 109, _ => exact keep160v2_109
  | 110, _ => exact keep160v2_110
  | 111, _ => exact keep160v2_111
  | 112, _ => exact keep160v2_112
  | 113, _ => exact keep160v2_113
  | 114, _ => exact keep160v2_114
  | 115, _ => exact keep160v2_115
  | 116, _ => exact keep160v2_116
  | 117, _ => exact keep160v2_117
  | 118, _ => exact keep160v2_118
  | 119, _ => exact keep160v2_119
  | 120, _ => exact keep160v2_120
  | 121, _ => exact keep160v2_121
  | 122, _ => exact keep160v2_122
  | 123, _ => exact keep160v2_123
  | 124, _ => exact keep160v2_124
  | 125, _ => exact keep160v2_125
  | 126, _ => exact keep160v2_126
  | 127, _ => exact keep160v2_127
  | 128, _ => exact keep160v2_128
  | 129, _ => exact keep160v2_129
  | 130, _ => exact keep160v2_130
  | 131, _ => exact keep160v2_131
  | 132, _ => exact keep160v2_132
  | 133, _ => exact keep160v2_133
  | 134, _ => exact keep160v2_134
  | 135, _ => exact keep160v2_135
  | 136, _ => exact keep160v2_136
  | 137, _ => exact keep160v2_137
  | 138, _ => exact keep160v2_138
  | 139, _ => exact keep160v2_139
  | 140, _ => exact keep160v2_140
  | 141, _ => exact keep160v2_141
  | 142, _ => exact keep160v2_142
  | 143, _ => exact keep160v2_143
  | 144, _ => exact keep160v2_144
  | 145, _ => exact keep160v2_145
  | 146, _ => exact keep160v2_146
  | 147, _ => exact keep160v2_147
  | 148, _ => exact keep160v2_148
  | 149, _ => exact keep160v2_149
  | 150, _ => exact keep160v2_150
  | 151, _ => exact keep160v2_151
  | 152, _ => exact keep160v2_152
  | 153, _ => exact keep160v2_153
  | 154, _ => exact keep160v2_154
  | 155, _ => exact keep160v2_155
  | 156, _ => exact keep160v2_156
  | 157, _ => exact keep160v2_157
  | 158, _ => exact keep160v2_158
  | 159, _ => exact keep160v2_159
  | 160, _ => exact keep160v2_160
  | 161, _ => exact keep160v2_161
  | 162, _ => exact keep160v2_162
  | 163, _ => exact keep160v2_163
  | 164, _ => exact keep160v2_164
  | 165, _ => exact keep160v2_165
  | 166, _ => exact keep160v2_166
  | 167, _ => exact keep160v2_167
  | 168, _ => exact keep160v2_168
  | 169, _ => exact keep160v2_169
  | 170, _ => exact keep160v2_170
  | 171, _ => exact keep160v2_171
  | 172, _ => exact keep160v2_172
  | 173, _ => exact keep160v2_173
  | 174, _ => exact keep160v2_174
  | 175, _ => exact keep160v2_175
  | 176, _ => exact keep160v2_176
  | 177, _ => exact keep160v2_177
  | 178, _ => exact keep160v2_178
  | 179, _ => exact keep160v2_179
  | 180, _ => exact keep160v2_180
  | 181, _ => exact keep160v2_181
  | 182, _ => exact keep160v2_182
  | 183, _ => exact keep160v2_183
  | 184, _ => exact keep160v2_184
  | 185, _ => exact keep160v2_185
  | 186, _ => exact keep160v2_186
  | 187, _ => exact keep160v2_187
  | 188, _ => exact keep160v2_188
  | 189, _ => exact keep160v2_189
  | 190, _ => exact keep160v2_190
  | 191, _ => exact keep160v2_191
  | 192, _ => exact keep160v2_192
  | 193, _ => exact keep160v2_193
  | 194, _ => exact keep160v2_194
  | 195, _ => exact keep160v2_195
  | 196, _ => exact keep160v2_196
  | 197, _ => exact keep160v2_197
  | 198, _ => exact keep160v2_198
  | 199, _ => exact keep160v2_199
  | 200, _ => exact keep160v2_200
  | 201, _ => exact keep160v2_201
  | 202, _ => exact keep160v2_202
  | 203, _ => exact keep160v2_203
  | 204, _ => exact keep160v2_204
  | 205, _ => exact keep160v2_205
  | 206, _ => exact keep160v2_206
  | 207, _ => exact keep160v2_207
  | 208, _ => exact keep160v2_208
  | 209, _ => exact keep160v2_209
  | 210, _ => exact keep160v2_210
  | 211, _ => exact keep160v2_211
  | 212, _ => exact keep160v2_212
  | 213, _ => exact keep160v2_213
  | 214, _ => exact keep160v2_214
  | 215, _ => exact keep160v2_215
  | 216, _ => exact keep160v2_216
  | 217, _ => exact keep160v2_217
  | 218, _ => exact keep160v2_218
  | 219, _ => exact keep160v2_219
  | 220, _ => exact keep160v2_220
  | 221, _ => exact keep160v2_221
  | 222, _ => exact keep160v2_222
  | 223, _ => exact keep160v2_223
  | 224, _ => exact keep160v2_224
  | 225, _ => exact keep160v2_225
  | 226, _ => exact keep160v2_226
  | 227, _ => exact keep160v2_227
  | 228, _ => exact keep160v2_228
  | 229, _ => exact keep160v2_229
  | 230, _ => exact keep160v2_230
  | 231, _ => exact keep160v2_231
  | 232, _ => exact keep160v2_232
  | 233, _ => exact keep160v2_233
  | 234, _ => exact keep160v2_234
  | 235, _ => exact keep160v2_235
  | 236, _ => exact keep160v2_236
  | 237, _ => exact keep160v2_237
  | 238, _ => exact keep160v2_238
  | 239, _ => exact keep160v2_239
  | 240, _ => exact keep160v2_240
  | 241, _ => exact keep160v2_241
  | 242, _ => exact keep160v2_242
  | 243, _ => exact keep160v2_243
  | 244, _ => exact keep160v2_244
  | 245, _ => exact keep160v2_245
  | 246, _ => exact keep160v2_246
  | 247, _ => exact keep160v2_247
  | 248, _ => exact keep160v2_248
  | 249, _ => exact keep160v2_249
  | 250, _ => exact keep160v2_250
  | 251, _ => exact keep160v2_251
  | 252, _ => exact keep160v2_252
  | 253, _ => exact keep160v2_253
  | 254, _ => exact keep160v2_254
  | 255, _ => exact keep160v2_255
  | 256, _ => exact keep160v2_256
  | 257, _ => exact keep160v2_257
  | 258, _ => exact keep160v2_258
  | 259, _ => exact keep160v2_259
  | 260, _ => exact keep160v2_260
  | 261, _ => exact keep160v2_261
  | n + 262, h => exact absurd h (by omega)

/-- No 192-edge snake begins with the first 160 vertices of any bank snake, in either
orientation (entry `2*s` of `oriented` is bank snake `s`, entry `2*s+1` its reversal).
Reversing a snake, this also excludes 192-edge snakes ending in those 160 vertices. -/
theorem bank_no192_keep160v2 (j : Nat) (hj : j < 262) :
    ¬ ∃ p : Snake 192, ∀ i (h : i < 160), (p.vertex ⟨i, by omega⟩).val = (oriented j)[i]! :=
  no192_from_prefix2 (oriented j) 160 (by decide) (by decide) (search_keep160v2 j hj)

#print axioms bank_no192_keep160v2
end Snake9.Dfs
