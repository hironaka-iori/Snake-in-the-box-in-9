import ContextWeights101
import StateWalk
import DefinedProofGraph

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

namespace Snake9.Context101
open Snake9.Direction77 Snake9.DirectionWindow Snake9.GraphInterpretation75
open Snake9.WindowAutomaton
open Snake9.GeometricCredit97 Snake9.Conditioned98 Snake9.CountFree98
open Snake9.ContextWeights101 Snake9.HistoryCredit95 Snake9.ConcreteCatalogue95
open Snake9.GraphWalk78 Snake9.Batch92 Snake9.Weights98

theorem direction_192 :
    2 = geometricCredits.getD 192 0 ∧
    12 = completedCredit 192 ∧
    16 = conditionalCredit 192 := by decide +kernel

theorem conditioned_192 (code : Nat) :
    conditionedCredit 192 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 192 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 192 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_192
#print axioms conditioned_192

theorem direction_193 :
    2 = geometricCredits.getD 193 0 ∧
    0 = completedCredit 193 ∧
    16 = conditionalCredit 193 := by decide +kernel

theorem conditioned_193 (code : Nat) :
    conditionedCredit 193 code = 0 := by
  have hf : canon ((extensions.getD 193 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 193 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_193
#print axioms conditioned_193

theorem direction_194 :
    2 = geometricCredits.getD 194 0 ∧
    0 = completedCredit 194 ∧
    18 = conditionalCredit 194 := by decide +kernel

theorem conditioned_194 (code : Nat) :
    conditionedCredit 194 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 194 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 194 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_194
#print axioms conditioned_194

theorem direction_195 :
    2 = geometricCredits.getD 195 0 ∧
    12 = completedCredit 195 ∧
    16 = conditionalCredit 195 := by decide +kernel

theorem conditioned_195 (code : Nat) :
    conditionedCredit 195 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 195 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 195 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_195
#print axioms conditioned_195

theorem direction_196 :
    8 = geometricCredits.getD 196 0 ∧
    16 = completedCredit 196 ∧
    16 = conditionalCredit 196 := by decide +kernel

theorem conditioned_196 (code : Nat) :
    conditionedCredit 196 code = 0 := by
  have hf : canon ((extensions.getD 196 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 196 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_196
#print axioms conditioned_196

theorem direction_197 :
    8 = geometricCredits.getD 197 0 ∧
    12 = completedCredit 197 ∧
    16 = conditionalCredit 197 := by decide +kernel

theorem conditioned_197 (code : Nat) :
    conditionedCredit 197 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 197 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 197 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_197
#print axioms conditioned_197

theorem direction_198 :
    4 = geometricCredits.getD 198 0 ∧
    16 = completedCredit 198 ∧
    16 = conditionalCredit 198 := by decide +kernel

theorem conditioned_198 (code : Nat) :
    conditionedCredit 198 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 198 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 198 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_198
#print axioms conditioned_198

theorem direction_199 :
    4 = geometricCredits.getD 199 0 ∧
    16 = completedCredit 199 ∧
    16 = conditionalCredit 199 := by decide +kernel

theorem conditioned_199 (code : Nat) :
    conditionedCredit 199 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 199 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 199 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_199
#print axioms conditioned_199

theorem direction_200 :
    8 = geometricCredits.getD 200 0 ∧
    12 = completedCredit 200 ∧
    16 = conditionalCredit 200 := by decide +kernel

theorem conditioned_200 (code : Nat) :
    conditionedCredit 200 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 200 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 200 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_200
#print axioms conditioned_200

theorem direction_201 :
    8 = geometricCredits.getD 201 0 ∧
    16 = completedCredit 201 ∧
    16 = conditionalCredit 201 := by decide +kernel

theorem conditioned_201 (code : Nat) :
    conditionedCredit 201 code = 0 := by
  have hf : canon ((extensions.getD 201 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 201 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_201
#print axioms conditioned_201

theorem direction_202 :
    7 = geometricCredits.getD 202 0 ∧
    0 = completedCredit 202 ∧
    16 = conditionalCredit 202 := by decide +kernel

theorem conditioned_202 (code : Nat) :
    conditionedCredit 202 code = 0 := by
  have hf : canon ((extensions.getD 202 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 202 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_202
#print axioms conditioned_202

theorem direction_203 :
    8 = geometricCredits.getD 203 0 ∧
    0 = completedCredit 203 ∧
    18 = conditionalCredit 203 := by decide +kernel

theorem conditioned_203 (code : Nat) :
    conditionedCredit 203 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 203 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 203 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_203
#print axioms conditioned_203

theorem direction_204 :
    8 = geometricCredits.getD 204 0 ∧
    12 = completedCredit 204 ∧
    16 = conditionalCredit 204 := by decide +kernel

theorem conditioned_204 (code : Nat) :
    conditionedCredit 204 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 204 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 204 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_204
#print axioms conditioned_204

theorem direction_205 :
    5 = geometricCredits.getD 205 0 ∧
    16 = completedCredit 205 ∧
    16 = conditionalCredit 205 := by decide +kernel

theorem conditioned_205 (code : Nat) :
    conditionedCredit 205 code = 0 := by
  have hf : canon ((extensions.getD 205 []).drop 3) = [0,1,2,0,3,1] := by decide +kernel
  have hb : canon (((extensions.getD 205 []).drop 3).reverse) = [0,1,2,3,0,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_205
#print axioms conditioned_205

theorem direction_206 :
    5 = geometricCredits.getD 206 0 ∧
    0 = completedCredit 206 ∧
    18 = conditionalCredit 206 := by decide +kernel

theorem conditioned_206 (code : Nat) :
    conditionedCredit 206 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 206 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 206 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_206
#print axioms conditioned_206

theorem direction_207 :
    7 = geometricCredits.getD 207 0 ∧
    0 = completedCredit 207 ∧
    18 = conditionalCredit 207 := by decide +kernel

theorem conditioned_207 (code : Nat) :
    conditionedCredit 207 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 207 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 207 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_207
#print axioms conditioned_207

theorem direction_208 :
    7 = geometricCredits.getD 208 0 ∧
    16 = completedCredit 208 ∧
    16 = conditionalCredit 208 := by decide +kernel

theorem conditioned_208 (code : Nat) :
    conditionedCredit 208 code = 0 := by
  have hf : canon ((extensions.getD 208 []).drop 3) = [0,1,2,0,3,1] := by decide +kernel
  have hb : canon (((extensions.getD 208 []).drop 3).reverse) = [0,1,2,3,0,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_208
#print axioms conditioned_208

theorem direction_209 :
    7 = geometricCredits.getD 209 0 ∧
    0 = completedCredit 209 ∧
    18 = conditionalCredit 209 := by decide +kernel

theorem conditioned_209 (code : Nat) :
    conditionedCredit 209 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 209 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 209 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_209
#print axioms conditioned_209

theorem direction_210 :
    0 = geometricCredits.getD 210 0 ∧
    0 = completedCredit 210 ∧
    16 = conditionalCredit 210 := by decide +kernel

theorem conditioned_210 (code : Nat) :
    conditionedCredit 210 code = 0 := by
  have hf : canon ((extensions.getD 210 []).drop 3) = [0,1,2,0,3,2] := by decide +kernel
  have hb : canon (((extensions.getD 210 []).drop 3).reverse) = [0,1,2,0,3,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_210
#print axioms conditioned_210

theorem direction_211 :
    7 = geometricCredits.getD 211 0 ∧
    0 = completedCredit 211 ∧
    18 = conditionalCredit 211 := by decide +kernel

theorem conditioned_211 (code : Nat) :
    conditionedCredit 211 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 211 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 211 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_211
#print axioms conditioned_211

theorem direction_212 :
    2 = geometricCredits.getD 212 0 ∧
    16 = completedCredit 212 ∧
    16 = conditionalCredit 212 := by decide +kernel

theorem conditioned_212 (code : Nat) :
    conditionedCredit 212 code = 0 := by
  have hf : canon ((extensions.getD 212 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 212 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_212
#print axioms conditioned_212

theorem direction_213 :
    2 = geometricCredits.getD 213 0 ∧
    12 = completedCredit 213 ∧
    16 = conditionalCredit 213 := by decide +kernel

theorem conditioned_213 (code : Nat) :
    conditionedCredit 213 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 213 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 213 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_213
#print axioms conditioned_213

theorem direction_214 :
    2 = geometricCredits.getD 214 0 ∧
    0 = completedCredit 214 ∧
    16 = conditionalCredit 214 := by decide +kernel

theorem conditioned_214 (code : Nat) :
    conditionedCredit 214 code = 0 := by
  have hf : canon ((extensions.getD 214 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 214 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_214
#print axioms conditioned_214

theorem direction_215 :
    2 = geometricCredits.getD 215 0 ∧
    0 = completedCredit 215 ∧
    18 = conditionalCredit 215 := by decide +kernel

theorem conditioned_215 (code : Nat) :
    conditionedCredit 215 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 215 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 215 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_215
#print axioms conditioned_215

theorem direction_216 :
    2 = geometricCredits.getD 216 0 ∧
    12 = completedCredit 216 ∧
    16 = conditionalCredit 216 := by decide +kernel

theorem conditioned_216 (code : Nat) :
    conditionedCredit 216 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 216 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 216 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_216
#print axioms conditioned_216

theorem direction_217 :
    7 = geometricCredits.getD 217 0 ∧
    16 = completedCredit 217 ∧
    16 = conditionalCredit 217 := by decide +kernel

theorem conditioned_217 (code : Nat) :
    conditionedCredit 217 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 217 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 217 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_217
#print axioms conditioned_217

theorem direction_218 :
    7 = geometricCredits.getD 218 0 ∧
    16 = completedCredit 218 ∧
    16 = conditionalCredit 218 := by decide +kernel

theorem conditioned_218 (code : Nat) :
    conditionedCredit 218 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 218 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 218 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_218
#print axioms conditioned_218

theorem direction_219 :
    2 = geometricCredits.getD 219 0 ∧
    12 = completedCredit 219 ∧
    12 = conditionalCredit 219 := by decide +kernel

theorem conditioned_219 (code : Nat) :
    conditionedCredit 219 code = 0 := by
  have hf : canon ((extensions.getD 219 []).drop 3) = [0,1,2,3,1,0] := by decide +kernel
  have hb : canon (((extensions.getD 219 []).drop 3).reverse) = [0,1,2,3,1,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_219
#print axioms conditioned_219

theorem direction_220 :
    7 = geometricCredits.getD 220 0 ∧
    16 = completedCredit 220 ∧
    16 = conditionalCredit 220 := by decide +kernel

theorem conditioned_220 (code : Nat) :
    conditionedCredit 220 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 220 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 220 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_220
#print axioms conditioned_220

theorem direction_221 :
    7 = geometricCredits.getD 221 0 ∧
    12 = completedCredit 221 ∧
    16 = conditionalCredit 221 := by decide +kernel

theorem conditioned_221 (code : Nat) :
    conditionedCredit 221 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 221 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 221 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_221
#print axioms conditioned_221

theorem direction_222 :
    7 = geometricCredits.getD 222 0 ∧
    16 = completedCredit 222 ∧
    16 = conditionalCredit 222 := by decide +kernel

theorem conditioned_222 (code : Nat) :
    conditionedCredit 222 code = 0 := by
  have hf : canon ((extensions.getD 222 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 222 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_222
#print axioms conditioned_222

theorem direction_223 :
    2 = geometricCredits.getD 223 0 ∧
    0 = completedCredit 223 ∧
    16 = conditionalCredit 223 := by decide +kernel

theorem conditioned_223 (code : Nat) :
    conditionedCredit 223 code = 0 := by
  have hf : canon ((extensions.getD 223 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 223 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_223
#print axioms conditioned_223

theorem direction_224 :
    7 = geometricCredits.getD 224 0 ∧
    0 = completedCredit 224 ∧
    18 = conditionalCredit 224 := by decide +kernel

theorem conditioned_224 (code : Nat) :
    conditionedCredit 224 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 224 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 224 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_224
#print axioms conditioned_224

theorem direction_225 :
    7 = geometricCredits.getD 225 0 ∧
    12 = completedCredit 225 ∧
    16 = conditionalCredit 225 := by decide +kernel

theorem conditioned_225 (code : Nat) :
    conditionedCredit 225 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 225 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 225 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_225
#print axioms conditioned_225

theorem direction_226 :
    29 = geometricCredits.getD 226 0 ∧
    16 = completedCredit 226 ∧
    16 = conditionalCredit 226 := by decide +kernel

theorem conditioned_226 (code : Nat) :
    conditionedCredit 226 code = 0 := by
  have hf : canon ((extensions.getD 226 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 226 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_226
#print axioms conditioned_226

theorem direction_227 :
    17 = geometricCredits.getD 227 0 ∧
    0 = completedCredit 227 ∧
    16 = conditionalCredit 227 := by decide +kernel

theorem conditioned_227 (code : Nat) :
    conditionedCredit 227 code = 0 := by
  have hf : canon ((extensions.getD 227 []).drop 3) = [0,1,2,3,0,1] := by decide +kernel
  have hb : canon (((extensions.getD 227 []).drop 3).reverse) = [0,1,2,3,0,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_227
#print axioms conditioned_227

theorem direction_228 :
    24 = geometricCredits.getD 228 0 ∧
    16 = completedCredit 228 ∧
    16 = conditionalCredit 228 := by decide +kernel

theorem conditioned_228 (code : Nat) :
    conditionedCredit 228 code = 0 := by
  have hf : canon ((extensions.getD 228 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 228 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_228
#print axioms conditioned_228

theorem direction_229 :
    21 = geometricCredits.getD 229 0 ∧
    16 = completedCredit 229 ∧
    16 = conditionalCredit 229 := by decide +kernel

theorem conditioned_229 (code : Nat) :
    conditionedCredit 229 code = 0 := by
  have hf : canon ((extensions.getD 229 []).drop 3) = [0,1,2,3,0,2] := by decide +kernel
  have hb : canon (((extensions.getD 229 []).drop 3).reverse) = [0,1,2,0,3,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_229
#print axioms conditioned_229

theorem direction_230 :
    29 = geometricCredits.getD 230 0 ∧
    16 = completedCredit 230 ∧
    16 = conditionalCredit 230 := by decide +kernel

theorem conditioned_230 (code : Nat) :
    conditionedCredit 230 code = 0 := by
  have hf : canon ((extensions.getD 230 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 230 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_230
#print axioms conditioned_230

theorem direction_231 :
    2 = geometricCredits.getD 231 0 ∧
    12 = completedCredit 231 ∧
    16 = conditionalCredit 231 := by decide +kernel

theorem conditioned_231 (code : Nat) :
    conditionedCredit 231 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 231 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 231 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_231
#print axioms conditioned_231

theorem direction_232 :
    2 = geometricCredits.getD 232 0 ∧
    16 = completedCredit 232 ∧
    16 = conditionalCredit 232 := by decide +kernel

theorem conditioned_232 (code : Nat) :
    conditionedCredit 232 code = 0 := by
  have hf : canon ((extensions.getD 232 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 232 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_232
#print axioms conditioned_232

theorem direction_233 :
    2 = geometricCredits.getD 233 0 ∧
    12 = completedCredit 233 ∧
    16 = conditionalCredit 233 := by decide +kernel

theorem conditioned_233 (code : Nat) :
    conditionedCredit 233 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 233 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 233 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_233
#print axioms conditioned_233

theorem direction_234 :
    2 = geometricCredits.getD 234 0 ∧
    0 = completedCredit 234 ∧
    16 = conditionalCredit 234 := by decide +kernel

theorem conditioned_234 (code : Nat) :
    conditionedCredit 234 code = 0 := by
  have hf : canon ((extensions.getD 234 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 234 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_234
#print axioms conditioned_234

theorem direction_235 :
    2 = geometricCredits.getD 235 0 ∧
    0 = completedCredit 235 ∧
    18 = conditionalCredit 235 := by decide +kernel

theorem conditioned_235 (code : Nat) :
    conditionedCredit 235 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 235 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 235 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_235
#print axioms conditioned_235

theorem direction_236 :
    2 = geometricCredits.getD 236 0 ∧
    12 = completedCredit 236 ∧
    16 = conditionalCredit 236 := by decide +kernel

theorem conditioned_236 (code : Nat) :
    conditionedCredit 236 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 236 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 236 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_236
#print axioms conditioned_236

theorem direction_237 :
    5 = geometricCredits.getD 237 0 ∧
    0 = completedCredit 237 ∧
    18 = conditionalCredit 237 := by decide +kernel

theorem conditioned_237 (code : Nat) :
    conditionedCredit 237 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 237 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 237 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_237
#print axioms conditioned_237

theorem direction_238 :
    21 = geometricCredits.getD 238 0 ∧
    12 = completedCredit 238 ∧
    16 = conditionalCredit 238 := by decide +kernel

theorem conditioned_238 (code : Nat) :
    conditionedCredit 238 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 238 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 238 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_238
#print axioms conditioned_238

theorem direction_239 :
    12 = geometricCredits.getD 239 0 ∧
    16 = completedCredit 239 ∧
    16 = conditionalCredit 239 := by decide +kernel

theorem conditioned_239 (code : Nat) :
    conditionedCredit 239 code = 0 := by
  have hf : canon ((extensions.getD 239 []).drop 3) = [0,1,2,3,0,2] := by decide +kernel
  have hb : canon (((extensions.getD 239 []).drop 3).reverse) = [0,1,2,0,3,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_239
#print axioms conditioned_239

theorem direction_240 :
    22 = geometricCredits.getD 240 0 ∧
    16 = completedCredit 240 ∧
    16 = conditionalCredit 240 := by decide +kernel

theorem conditioned_240 (code : Nat) :
    conditionedCredit 240 code = 0 := by
  have hf : canon ((extensions.getD 240 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 240 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_240
#print axioms conditioned_240

theorem direction_241 :
    5 = geometricCredits.getD 241 0 ∧
    16 = completedCredit 241 ∧
    16 = conditionalCredit 241 := by decide +kernel

theorem conditioned_241 (code : Nat) :
    conditionedCredit 241 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 241 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 241 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_241
#print axioms conditioned_241

theorem direction_242 :
    0 = geometricCredits.getD 242 0 ∧
    0 = completedCredit 242 ∧
    18 = conditionalCredit 242 := by decide +kernel

theorem conditioned_242 (code : Nat) :
    conditionedCredit 242 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 242 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 242 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_242
#print axioms conditioned_242

theorem direction_243 :
    0 = geometricCredits.getD 243 0 ∧
    12 = completedCredit 243 ∧
    16 = conditionalCredit 243 := by decide +kernel

theorem conditioned_243 (code : Nat) :
    conditionedCredit 243 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 243 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 243 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_243
#print axioms conditioned_243

theorem direction_244 :
    0 = geometricCredits.getD 244 0 ∧
    0 = completedCredit 244 ∧
    16 = conditionalCredit 244 := by decide +kernel

theorem conditioned_244 (code : Nat) :
    conditionedCredit 244 code = 0 := by
  have hf : canon ((extensions.getD 244 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 244 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_244
#print axioms conditioned_244

theorem direction_245 :
    0 = geometricCredits.getD 245 0 ∧
    16 = completedCredit 245 ∧
    16 = conditionalCredit 245 := by decide +kernel

theorem conditioned_245 (code : Nat) :
    conditionedCredit 245 code = 0 := by
  have hf : canon ((extensions.getD 245 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 245 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_245
#print axioms conditioned_245

theorem direction_246 :
    0 = geometricCredits.getD 246 0 ∧
    12 = completedCredit 246 ∧
    16 = conditionalCredit 246 := by decide +kernel

theorem conditioned_246 (code : Nat) :
    conditionedCredit 246 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 246 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 246 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_246
#print axioms conditioned_246

theorem direction_247 :
    22 = geometricCredits.getD 247 0 ∧
    0 = completedCredit 247 ∧
    18 = conditionalCredit 247 := by decide +kernel

theorem conditioned_247 (code : Nat) :
    conditionedCredit 247 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 247 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 247 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_247
#print axioms conditioned_247

theorem direction_248 :
    43 = geometricCredits.getD 248 0 ∧
    12 = completedCredit 248 ∧
    16 = conditionalCredit 248 := by decide +kernel

theorem conditioned_248 (code : Nat) :
    conditionedCredit 248 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 248 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 248 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_248
#print axioms conditioned_248

theorem direction_249 :
    5 = geometricCredits.getD 249 0 ∧
    16 = completedCredit 249 ∧
    16 = conditionalCredit 249 := by decide +kernel

theorem conditioned_249 (code : Nat) :
    conditionedCredit 249 code = 0 := by
  have hf : canon ((extensions.getD 249 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 249 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_249
#print axioms conditioned_249

theorem direction_250 :
    10 = geometricCredits.getD 250 0 ∧
    16 = completedCredit 250 ∧
    16 = conditionalCredit 250 := by decide +kernel

theorem conditioned_250 (code : Nat) :
    conditionedCredit 250 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 250 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 250 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_250
#print axioms conditioned_250

theorem direction_251 :
    13 = geometricCredits.getD 251 0 ∧
    0 = completedCredit 251 ∧
    18 = conditionalCredit 251 := by decide +kernel

theorem conditioned_251 (code : Nat) :
    conditionedCredit 251 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 251 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 251 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_251
#print axioms conditioned_251

theorem direction_252 :
    13 = geometricCredits.getD 252 0 ∧
    12 = completedCredit 252 ∧
    16 = conditionalCredit 252 := by decide +kernel

theorem conditioned_252 (code : Nat) :
    conditionedCredit 252 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 252 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 252 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_252
#print axioms conditioned_252

theorem direction_253 :
    13 = geometricCredits.getD 253 0 ∧
    0 = completedCredit 253 ∧
    16 = conditionalCredit 253 := by decide +kernel

theorem conditioned_253 (code : Nat) :
    conditionedCredit 253 code = 0 := by
  have hf : canon ((extensions.getD 253 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 253 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_253
#print axioms conditioned_253

theorem direction_254 :
    13 = geometricCredits.getD 254 0 ∧
    16 = completedCredit 254 ∧
    16 = conditionalCredit 254 := by decide +kernel

theorem conditioned_254 (code : Nat) :
    conditionedCredit 254 code = 0 := by
  have hf : canon ((extensions.getD 254 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 254 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_254
#print axioms conditioned_254

theorem direction_255 :
    13 = geometricCredits.getD 255 0 ∧
    12 = completedCredit 255 ∧
    16 = conditionalCredit 255 := by decide +kernel

theorem conditioned_255 (code : Nat) :
    conditionedCredit 255 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 255 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 255 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_255
#print axioms conditioned_255

end Snake9.Context101
