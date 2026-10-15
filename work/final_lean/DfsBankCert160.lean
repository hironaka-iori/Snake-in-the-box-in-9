import DfsBankCert160_0
import DfsBankCert160_1
import DfsBankCert160_2
import DfsBankCert160_3
import DfsBankCert160_4
import DfsBankCert160_5
import DfsBankCert160_6
import DfsBankCert160_7
import DfsBankCert160_8
import DfsBankCert160_9
import DfsBankCert160_10
import DfsBankCert160_11
import DfsBankCert160_12
import DfsBankCert160_13
import DfsBankCert160_14
import DfsBankCert160_15
import DfsBankCert160_16
import DfsBankCert160_17
import DfsBankCert160_18
import DfsBankCert160_19
import DfsBankCert160_20
import DfsBankCert160_21
import DfsBankCert160_22
import DfsBankCert160_23
import DfsBankCert160_24
import DfsBankCert160_25
import DfsBankCert160_26
import DfsBankCert160_27
import DfsBankCert160_28
import DfsBankCert160_29
import DfsBankCert160_30
import DfsBankCert160_31
import DfsBankCert160_32
import DfsBankCert160_33
import DfsBankCert160_34
import DfsBankCert160_35
import DfsBankCert160_36
import DfsBankCert160_37
import DfsBankCert160_38
import DfsBankCert160_39

namespace Snake9.Dfs
set_option maxRecDepth 100000

theorem search_keep160 (j : Nat) (hj : j < 262) :
    search (oriented j)[159]! (banFrom (fun i => (oriented j)[i]!) 159) 33 = false := by
  match j, hj with
  | 0, _ => exact keep160_0
  | 1, _ => exact keep160_1
  | 2, _ => exact keep160_2
  | 3, _ => exact keep160_3
  | 4, _ => exact keep160_4
  | 5, _ => exact keep160_5
  | 6, _ => exact keep160_6
  | 7, _ => exact keep160_7
  | 8, _ => exact keep160_8
  | 9, _ => exact keep160_9
  | 10, _ => exact keep160_10
  | 11, _ => exact keep160_11
  | 12, _ => exact keep160_12
  | 13, _ => exact keep160_13
  | 14, _ => exact keep160_14
  | 15, _ => exact keep160_15
  | 16, _ => exact keep160_16
  | 17, _ => exact keep160_17
  | 18, _ => exact keep160_18
  | 19, _ => exact keep160_19
  | 20, _ => exact keep160_20
  | 21, _ => exact keep160_21
  | 22, _ => exact keep160_22
  | 23, _ => exact keep160_23
  | 24, _ => exact keep160_24
  | 25, _ => exact keep160_25
  | 26, _ => exact keep160_26
  | 27, _ => exact keep160_27
  | 28, _ => exact keep160_28
  | 29, _ => exact keep160_29
  | 30, _ => exact keep160_30
  | 31, _ => exact keep160_31
  | 32, _ => exact keep160_32
  | 33, _ => exact keep160_33
  | 34, _ => exact keep160_34
  | 35, _ => exact keep160_35
  | 36, _ => exact keep160_36
  | 37, _ => exact keep160_37
  | 38, _ => exact keep160_38
  | 39, _ => exact keep160_39
  | 40, _ => exact keep160_40
  | 41, _ => exact keep160_41
  | 42, _ => exact keep160_42
  | 43, _ => exact keep160_43
  | 44, _ => exact keep160_44
  | 45, _ => exact keep160_45
  | 46, _ => exact keep160_46
  | 47, _ => exact keep160_47
  | 48, _ => exact keep160_48
  | 49, _ => exact keep160_49
  | 50, _ => exact keep160_50
  | 51, _ => exact keep160_51
  | 52, _ => exact keep160_52
  | 53, _ => exact keep160_53
  | 54, _ => exact keep160_54
  | 55, _ => exact keep160_55
  | 56, _ => exact keep160_56
  | 57, _ => exact keep160_57
  | 58, _ => exact keep160_58
  | 59, _ => exact keep160_59
  | 60, _ => exact keep160_60
  | 61, _ => exact keep160_61
  | 62, _ => exact keep160_62
  | 63, _ => exact keep160_63
  | 64, _ => exact keep160_64
  | 65, _ => exact keep160_65
  | 66, _ => exact keep160_66
  | 67, _ => exact keep160_67
  | 68, _ => exact keep160_68
  | 69, _ => exact keep160_69
  | 70, _ => exact keep160_70
  | 71, _ => exact keep160_71
  | 72, _ => exact keep160_72
  | 73, _ => exact keep160_73
  | 74, _ => exact keep160_74
  | 75, _ => exact keep160_75
  | 76, _ => exact keep160_76
  | 77, _ => exact keep160_77
  | 78, _ => exact keep160_78
  | 79, _ => exact keep160_79
  | 80, _ => exact keep160_80
  | 81, _ => exact keep160_81
  | 82, _ => exact keep160_82
  | 83, _ => exact keep160_83
  | 84, _ => exact keep160_84
  | 85, _ => exact keep160_85
  | 86, _ => exact keep160_86
  | 87, _ => exact keep160_87
  | 88, _ => exact keep160_88
  | 89, _ => exact keep160_89
  | 90, _ => exact keep160_90
  | 91, _ => exact keep160_91
  | 92, _ => exact keep160_92
  | 93, _ => exact keep160_93
  | 94, _ => exact keep160_94
  | 95, _ => exact keep160_95
  | 96, _ => exact keep160_96
  | 97, _ => exact keep160_97
  | 98, _ => exact keep160_98
  | 99, _ => exact keep160_99
  | 100, _ => exact keep160_100
  | 101, _ => exact keep160_101
  | 102, _ => exact keep160_102
  | 103, _ => exact keep160_103
  | 104, _ => exact keep160_104
  | 105, _ => exact keep160_105
  | 106, _ => exact keep160_106
  | 107, _ => exact keep160_107
  | 108, _ => exact keep160_108
  | 109, _ => exact keep160_109
  | 110, _ => exact keep160_110
  | 111, _ => exact keep160_111
  | 112, _ => exact keep160_112
  | 113, _ => exact keep160_113
  | 114, _ => exact keep160_114
  | 115, _ => exact keep160_115
  | 116, _ => exact keep160_116
  | 117, _ => exact keep160_117
  | 118, _ => exact keep160_118
  | 119, _ => exact keep160_119
  | 120, _ => exact keep160_120
  | 121, _ => exact keep160_121
  | 122, _ => exact keep160_122
  | 123, _ => exact keep160_123
  | 124, _ => exact keep160_124
  | 125, _ => exact keep160_125
  | 126, _ => exact keep160_126
  | 127, _ => exact keep160_127
  | 128, _ => exact keep160_128
  | 129, _ => exact keep160_129
  | 130, _ => exact keep160_130
  | 131, _ => exact keep160_131
  | 132, _ => exact keep160_132
  | 133, _ => exact keep160_133
  | 134, _ => exact keep160_134
  | 135, _ => exact keep160_135
  | 136, _ => exact keep160_136
  | 137, _ => exact keep160_137
  | 138, _ => exact keep160_138
  | 139, _ => exact keep160_139
  | 140, _ => exact keep160_140
  | 141, _ => exact keep160_141
  | 142, _ => exact keep160_142
  | 143, _ => exact keep160_143
  | 144, _ => exact keep160_144
  | 145, _ => exact keep160_145
  | 146, _ => exact keep160_146
  | 147, _ => exact keep160_147
  | 148, _ => exact keep160_148
  | 149, _ => exact keep160_149
  | 150, _ => exact keep160_150
  | 151, _ => exact keep160_151
  | 152, _ => exact keep160_152
  | 153, _ => exact keep160_153
  | 154, _ => exact keep160_154
  | 155, _ => exact keep160_155
  | 156, _ => exact keep160_156
  | 157, _ => exact keep160_157
  | 158, _ => exact keep160_158
  | 159, _ => exact keep160_159
  | 160, _ => exact keep160_160
  | 161, _ => exact keep160_161
  | 162, _ => exact keep160_162
  | 163, _ => exact keep160_163
  | 164, _ => exact keep160_164
  | 165, _ => exact keep160_165
  | 166, _ => exact keep160_166
  | 167, _ => exact keep160_167
  | 168, _ => exact keep160_168
  | 169, _ => exact keep160_169
  | 170, _ => exact keep160_170
  | 171, _ => exact keep160_171
  | 172, _ => exact keep160_172
  | 173, _ => exact keep160_173
  | 174, _ => exact keep160_174
  | 175, _ => exact keep160_175
  | 176, _ => exact keep160_176
  | 177, _ => exact keep160_177
  | 178, _ => exact keep160_178
  | 179, _ => exact keep160_179
  | 180, _ => exact keep160_180
  | 181, _ => exact keep160_181
  | 182, _ => exact keep160_182
  | 183, _ => exact keep160_183
  | 184, _ => exact keep160_184
  | 185, _ => exact keep160_185
  | 186, _ => exact keep160_186
  | 187, _ => exact keep160_187
  | 188, _ => exact keep160_188
  | 189, _ => exact keep160_189
  | 190, _ => exact keep160_190
  | 191, _ => exact keep160_191
  | 192, _ => exact keep160_192
  | 193, _ => exact keep160_193
  | 194, _ => exact keep160_194
  | 195, _ => exact keep160_195
  | 196, _ => exact keep160_196
  | 197, _ => exact keep160_197
  | 198, _ => exact keep160_198
  | 199, _ => exact keep160_199
  | 200, _ => exact keep160_200
  | 201, _ => exact keep160_201
  | 202, _ => exact keep160_202
  | 203, _ => exact keep160_203
  | 204, _ => exact keep160_204
  | 205, _ => exact keep160_205
  | 206, _ => exact keep160_206
  | 207, _ => exact keep160_207
  | 208, _ => exact keep160_208
  | 209, _ => exact keep160_209
  | 210, _ => exact keep160_210
  | 211, _ => exact keep160_211
  | 212, _ => exact keep160_212
  | 213, _ => exact keep160_213
  | 214, _ => exact keep160_214
  | 215, _ => exact keep160_215
  | 216, _ => exact keep160_216
  | 217, _ => exact keep160_217
  | 218, _ => exact keep160_218
  | 219, _ => exact keep160_219
  | 220, _ => exact keep160_220
  | 221, _ => exact keep160_221
  | 222, _ => exact keep160_222
  | 223, _ => exact keep160_223
  | 224, _ => exact keep160_224
  | 225, _ => exact keep160_225
  | 226, _ => exact keep160_226
  | 227, _ => exact keep160_227
  | 228, _ => exact keep160_228
  | 229, _ => exact keep160_229
  | 230, _ => exact keep160_230
  | 231, _ => exact keep160_231
  | 232, _ => exact keep160_232
  | 233, _ => exact keep160_233
  | 234, _ => exact keep160_234
  | 235, _ => exact keep160_235
  | 236, _ => exact keep160_236
  | 237, _ => exact keep160_237
  | 238, _ => exact keep160_238
  | 239, _ => exact keep160_239
  | 240, _ => exact keep160_240
  | 241, _ => exact keep160_241
  | 242, _ => exact keep160_242
  | 243, _ => exact keep160_243
  | 244, _ => exact keep160_244
  | 245, _ => exact keep160_245
  | 246, _ => exact keep160_246
  | 247, _ => exact keep160_247
  | 248, _ => exact keep160_248
  | 249, _ => exact keep160_249
  | 250, _ => exact keep160_250
  | 251, _ => exact keep160_251
  | 252, _ => exact keep160_252
  | 253, _ => exact keep160_253
  | 254, _ => exact keep160_254
  | 255, _ => exact keep160_255
  | 256, _ => exact keep160_256
  | 257, _ => exact keep160_257
  | 258, _ => exact keep160_258
  | 259, _ => exact keep160_259
  | 260, _ => exact keep160_260
  | 261, _ => exact keep160_261
  | n + 262, h => exact absurd h (by omega)

/-- No 192-edge snake begins with the first 160 vertices of any bank snake, in either
orientation (entry `2*s` of `oriented` is bank snake `s`, entry `2*s+1` its reversal).
Reversing a snake, this also excludes 192-edge snakes ending in those 160 vertices. -/
theorem bank_no192_keep160 (j : Nat) (hj : j < 262) :
    ¬ ∃ p : Snake 192, ∀ i (h : i < 160), (p.vertex ⟨i, by omega⟩).val = (oriented j)[i]! :=
  no192_from_prefix (oriented j) 160 (by decide) (by decide) (search_keep160 j hj)

#print axioms bank_no192_keep160
end Snake9.Dfs
