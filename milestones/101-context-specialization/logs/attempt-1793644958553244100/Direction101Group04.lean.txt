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

theorem direction_256 :
    8 = geometricCredits.getD 256 0 ∧
    0 = completedCredit 256 ∧
    16 = conditionalCredit 256 := by decide +kernel

theorem conditioned_256 (code : Nat) :
    conditionedCredit 256 code = 0 := by
  have hf : canon ((extensions.getD 256 []).drop 3) = [0,1,2,0,3,2] := by decide +kernel
  have hb : canon (((extensions.getD 256 []).drop 3).reverse) = [0,1,2,0,3,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_256
#print axioms conditioned_256

theorem direction_257 :
    18 = geometricCredits.getD 257 0 ∧
    0 = completedCredit 257 ∧
    18 = conditionalCredit 257 := by decide +kernel

theorem conditioned_257 (code : Nat) :
    conditionedCredit 257 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 257 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 257 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_257
#print axioms conditioned_257

theorem direction_258 :
    0 = geometricCredits.getD 258 0 ∧
    0 = completedCredit 258 ∧
    18 = conditionalCredit 258 := by decide +kernel

theorem conditioned_258 (code : Nat) :
    conditionedCredit 258 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 258 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 258 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_258
#print axioms conditioned_258

theorem direction_259 :
    5 = geometricCredits.getD 259 0 ∧
    0 = completedCredit 259 ∧
    16 = conditionalCredit 259 := by decide +kernel

theorem conditioned_259 (code : Nat) :
    conditionedCredit 259 code = 0 := by
  have hf : canon ((extensions.getD 259 []).drop 3) = [0,1,2,0,3,2] := by decide +kernel
  have hb : canon (((extensions.getD 259 []).drop 3).reverse) = [0,1,2,0,3,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_259
#print axioms conditioned_259

theorem direction_260 :
    10 = geometricCredits.getD 260 0 ∧
    0 = completedCredit 260 ∧
    18 = conditionalCredit 260 := by decide +kernel

theorem conditioned_260 (code : Nat) :
    conditionedCredit 260 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 260 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 260 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_260
#print axioms conditioned_260

theorem direction_261 :
    10 = geometricCredits.getD 261 0 ∧
    0 = completedCredit 261 ∧
    18 = conditionalCredit 261 := by decide +kernel

theorem conditioned_261 (code : Nat) :
    conditionedCredit 261 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 261 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 261 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_261
#print axioms conditioned_261

theorem direction_262 :
    10 = geometricCredits.getD 262 0 ∧
    16 = completedCredit 262 ∧
    16 = conditionalCredit 262 := by decide +kernel

theorem conditioned_262 (code : Nat) :
    conditionedCredit 262 code = 0 := by
  have hf : canon ((extensions.getD 262 []).drop 3) = [0,1,2,0,3,1] := by decide +kernel
  have hb : canon (((extensions.getD 262 []).drop 3).reverse) = [0,1,2,3,0,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_262
#print axioms conditioned_262

theorem direction_263 :
    10 = geometricCredits.getD 263 0 ∧
    0 = completedCredit 263 ∧
    18 = conditionalCredit 263 := by decide +kernel

theorem conditioned_263 (code : Nat) :
    conditionedCredit 263 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 263 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 263 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_263
#print axioms conditioned_263

theorem direction_264 :
    0 = geometricCredits.getD 264 0 ∧
    0 = completedCredit 264 ∧
    18 = conditionalCredit 264 := by decide +kernel

theorem conditioned_264 (code : Nat) :
    conditionedCredit 264 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 264 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 264 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_264
#print axioms conditioned_264

theorem direction_265 :
    0 = geometricCredits.getD 265 0 ∧
    12 = completedCredit 265 ∧
    16 = conditionalCredit 265 := by decide +kernel

theorem conditioned_265 (code : Nat) :
    conditionedCredit 265 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 265 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 265 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_265
#print axioms conditioned_265

theorem direction_266 :
    0 = geometricCredits.getD 266 0 ∧
    0 = completedCredit 266 ∧
    16 = conditionalCredit 266 := by decide +kernel

theorem conditioned_266 (code : Nat) :
    conditionedCredit 266 code = 0 := by
  have hf : canon ((extensions.getD 266 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 266 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_266
#print axioms conditioned_266

theorem direction_267 :
    0 = geometricCredits.getD 267 0 ∧
    16 = completedCredit 267 ∧
    16 = conditionalCredit 267 := by decide +kernel

theorem conditioned_267 (code : Nat) :
    conditionedCredit 267 code = 0 := by
  have hf : canon ((extensions.getD 267 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 267 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_267
#print axioms conditioned_267

theorem direction_268 :
    0 = geometricCredits.getD 268 0 ∧
    12 = completedCredit 268 ∧
    16 = conditionalCredit 268 := by decide +kernel

theorem conditioned_268 (code : Nat) :
    conditionedCredit 268 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 268 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 268 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_268
#print axioms conditioned_268

theorem direction_269 :
    0 = geometricCredits.getD 269 0 ∧
    0 = completedCredit 269 ∧
    18 = conditionalCredit 269 := by decide +kernel

theorem conditioned_269 (code : Nat) :
    conditionedCredit 269 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 269 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 269 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_269
#print axioms conditioned_269

theorem direction_270 :
    0 = geometricCredits.getD 270 0 ∧
    12 = completedCredit 270 ∧
    16 = conditionalCredit 270 := by decide +kernel

theorem conditioned_270 (code : Nat) :
    conditionedCredit 270 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 270 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 270 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_270
#print axioms conditioned_270

theorem direction_271 :
    0 = geometricCredits.getD 271 0 ∧
    0 = completedCredit 271 ∧
    16 = conditionalCredit 271 := by decide +kernel

theorem conditioned_271 (code : Nat) :
    conditionedCredit 271 code = 0 := by
  have hf : canon ((extensions.getD 271 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 271 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_271
#print axioms conditioned_271

theorem direction_272 :
    0 = geometricCredits.getD 272 0 ∧
    16 = completedCredit 272 ∧
    16 = conditionalCredit 272 := by decide +kernel

theorem conditioned_272 (code : Nat) :
    conditionedCredit 272 code = 0 := by
  have hf : canon ((extensions.getD 272 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 272 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_272
#print axioms conditioned_272

theorem direction_273 :
    0 = geometricCredits.getD 273 0 ∧
    12 = completedCredit 273 ∧
    16 = conditionalCredit 273 := by decide +kernel

theorem conditioned_273 (code : Nat) :
    conditionedCredit 273 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 273 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 273 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_273
#print axioms conditioned_273

theorem direction_274 :
    12 = geometricCredits.getD 274 0 ∧
    16 = completedCredit 274 ∧
    16 = conditionalCredit 274 := by decide +kernel

theorem conditioned_274 (code : Nat) :
    conditionedCredit 274 code = 0 := by
  have hf : canon ((extensions.getD 274 []).drop 3) = [0,1,2,3,0,2] := by decide +kernel
  have hb : canon (((extensions.getD 274 []).drop 3).reverse) = [0,1,2,0,3,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_274
#print axioms conditioned_274

theorem direction_275 :
    18 = geometricCredits.getD 275 0 ∧
    16 = completedCredit 275 ∧
    16 = conditionalCredit 275 := by decide +kernel

theorem conditioned_275 (code : Nat) :
    conditionedCredit 275 code = 0 := by
  have hf : canon ((extensions.getD 275 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 275 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_275
#print axioms conditioned_275

theorem direction_276 :
    18 = geometricCredits.getD 276 0 ∧
    16 = completedCredit 276 ∧
    16 = conditionalCredit 276 := by decide +kernel

theorem conditioned_276 (code : Nat) :
    conditionedCredit 276 code = 0 := by
  have hf : canon ((extensions.getD 276 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 276 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_276
#print axioms conditioned_276

theorem direction_277 :
    6 = geometricCredits.getD 277 0 ∧
    0 = completedCredit 277 ∧
    16 = conditionalCredit 277 := by decide +kernel

theorem conditioned_277 (code : Nat) :
    conditionedCredit 277 code = 0 := by
  have hf : canon ((extensions.getD 277 []).drop 3) = [0,1,2,3,0,1] := by decide +kernel
  have hb : canon (((extensions.getD 277 []).drop 3).reverse) = [0,1,2,3,0,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_277
#print axioms conditioned_277

theorem direction_278 :
    18 = geometricCredits.getD 278 0 ∧
    16 = completedCredit 278 ∧
    16 = conditionalCredit 278 := by decide +kernel

theorem conditioned_278 (code : Nat) :
    conditionedCredit 278 code = 0 := by
  have hf : canon ((extensions.getD 278 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 278 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_278
#print axioms conditioned_278

theorem direction_279 :
    5 = geometricCredits.getD 279 0 ∧
    16 = completedCredit 279 ∧
    16 = conditionalCredit 279 := by decide +kernel

theorem conditioned_279 (code : Nat) :
    conditionedCredit 279 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 279 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 279 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_279
#print axioms conditioned_279

theorem direction_280 :
    5 = geometricCredits.getD 280 0 ∧
    16 = completedCredit 280 ∧
    16 = conditionalCredit 280 := by decide +kernel

theorem conditioned_280 (code : Nat) :
    conditionedCredit 280 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 280 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 280 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_280
#print axioms conditioned_280

theorem direction_281 :
    0 = geometricCredits.getD 281 0 ∧
    12 = completedCredit 281 ∧
    12 = conditionalCredit 281 := by decide +kernel

theorem conditioned_281 (code : Nat) :
    conditionedCredit 281 code = 0 := by
  have hf : canon ((extensions.getD 281 []).drop 3) = [0,1,2,3,1,0] := by decide +kernel
  have hb : canon (((extensions.getD 281 []).drop 3).reverse) = [0,1,2,3,1,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_281
#print axioms conditioned_281

theorem direction_282 :
    5 = geometricCredits.getD 282 0 ∧
    16 = completedCredit 282 ∧
    16 = conditionalCredit 282 := by decide +kernel

theorem conditioned_282 (code : Nat) :
    conditionedCredit 282 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 282 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 282 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_282
#print axioms conditioned_282

theorem direction_283 :
    0 = geometricCredits.getD 283 0 ∧
    0 = completedCredit 283 ∧
    18 = conditionalCredit 283 := by decide +kernel

theorem conditioned_283 (code : Nat) :
    conditionedCredit 283 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 283 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 283 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_283
#print axioms conditioned_283

theorem direction_284 :
    0 = geometricCredits.getD 284 0 ∧
    12 = completedCredit 284 ∧
    16 = conditionalCredit 284 := by decide +kernel

theorem conditioned_284 (code : Nat) :
    conditionedCredit 284 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 284 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 284 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_284
#print axioms conditioned_284

theorem direction_285 :
    0 = geometricCredits.getD 285 0 ∧
    12 = completedCredit 285 ∧
    16 = conditionalCredit 285 := by decide +kernel

theorem conditioned_285 (code : Nat) :
    conditionedCredit 285 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 285 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 285 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_285
#print axioms conditioned_285

theorem direction_286 :
    0 = geometricCredits.getD 286 0 ∧
    0 = completedCredit 286 ∧
    16 = conditionalCredit 286 := by decide +kernel

theorem conditioned_286 (code : Nat) :
    conditionedCredit 286 code = 0 := by
  have hf : canon ((extensions.getD 286 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 286 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_286
#print axioms conditioned_286

theorem direction_287 :
    0 = geometricCredits.getD 287 0 ∧
    16 = completedCredit 287 ∧
    16 = conditionalCredit 287 := by decide +kernel

theorem conditioned_287 (code : Nat) :
    conditionedCredit 287 code = 0 := by
  have hf : canon ((extensions.getD 287 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 287 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_287
#print axioms conditioned_287

theorem direction_288 :
    0 = geometricCredits.getD 288 0 ∧
    12 = completedCredit 288 ∧
    16 = conditionalCredit 288 := by decide +kernel

theorem conditioned_288 (code : Nat) :
    conditionedCredit 288 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 288 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 288 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_288
#print axioms conditioned_288

theorem direction_289 :
    27 = geometricCredits.getD 289 0 ∧
    0 = completedCredit 289 ∧
    18 = conditionalCredit 289 := by decide +kernel

theorem conditioned_289 (code : Nat) :
    conditionedCredit 289 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 289 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 289 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_289
#print axioms conditioned_289

theorem direction_290 :
    27 = geometricCredits.getD 290 0 ∧
    12 = completedCredit 290 ∧
    16 = conditionalCredit 290 := by decide +kernel

theorem conditioned_290 (code : Nat) :
    conditionedCredit 290 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 290 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 290 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_290
#print axioms conditioned_290

theorem direction_291 :
    33 = geometricCredits.getD 291 0 ∧
    16 = completedCredit 291 ∧
    16 = conditionalCredit 291 := by decide +kernel

theorem conditioned_291 (code : Nat) :
    conditionedCredit 291 code = 0 := by
  have hf : canon ((extensions.getD 291 []).drop 3) = [0,1,2,3,0,2] := by decide +kernel
  have hb : canon (((extensions.getD 291 []).drop 3).reverse) = [0,1,2,0,3,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_291
#print axioms conditioned_291

theorem direction_292 :
    40 = geometricCredits.getD 292 0 ∧
    16 = completedCredit 292 ∧
    16 = conditionalCredit 292 := by decide +kernel

theorem conditioned_292 (code : Nat) :
    conditionedCredit 292 code = 0 := by
  have hf : canon ((extensions.getD 292 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 292 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_292
#print axioms conditioned_292

theorem direction_293 :
    22 = geometricCredits.getD 293 0 ∧
    16 = completedCredit 293 ∧
    16 = conditionalCredit 293 := by decide +kernel

theorem conditioned_293 (code : Nat) :
    conditionedCredit 293 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 293 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 293 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_293
#print axioms conditioned_293

theorem direction_294 :
    12 = geometricCredits.getD 294 0 ∧
    0 = completedCredit 294 ∧
    18 = conditionalCredit 294 := by decide +kernel

theorem conditioned_294 (code : Nat) :
    conditionedCredit 294 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 294 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 294 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_294
#print axioms conditioned_294

theorem direction_295 :
    12 = geometricCredits.getD 295 0 ∧
    12 = completedCredit 295 ∧
    16 = conditionalCredit 295 := by decide +kernel

theorem conditioned_295 (code : Nat) :
    conditionedCredit 295 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 295 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 295 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_295
#print axioms conditioned_295

theorem direction_296 :
    12 = geometricCredits.getD 296 0 ∧
    0 = completedCredit 296 ∧
    16 = conditionalCredit 296 := by decide +kernel

theorem conditioned_296 (code : Nat) :
    conditionedCredit 296 code = 0 := by
  have hf : canon ((extensions.getD 296 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 296 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_296
#print axioms conditioned_296

theorem direction_297 :
    12 = geometricCredits.getD 297 0 ∧
    16 = completedCredit 297 ∧
    16 = conditionalCredit 297 := by decide +kernel

theorem conditioned_297 (code : Nat) :
    conditionedCredit 297 code = 0 := by
  have hf : canon ((extensions.getD 297 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 297 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_297
#print axioms conditioned_297

theorem direction_298 :
    12 = geometricCredits.getD 298 0 ∧
    12 = completedCredit 298 ∧
    16 = conditionalCredit 298 := by decide +kernel

theorem conditioned_298 (code : Nat) :
    conditionedCredit 298 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 298 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 298 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_298
#print axioms conditioned_298

theorem direction_299 :
    5 = geometricCredits.getD 299 0 ∧
    0 = completedCredit 299 ∧
    18 = conditionalCredit 299 := by decide +kernel

theorem conditioned_299 (code : Nat) :
    conditionedCredit 299 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 299 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 299 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_299
#print axioms conditioned_299

theorem direction_300 :
    5 = geometricCredits.getD 300 0 ∧
    12 = completedCredit 300 ∧
    16 = conditionalCredit 300 := by decide +kernel

theorem conditioned_300 (code : Nat) :
    conditionedCredit 300 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 300 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 300 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_300
#print axioms conditioned_300

theorem direction_301 :
    5 = geometricCredits.getD 301 0 ∧
    12 = completedCredit 301 ∧
    16 = conditionalCredit 301 := by decide +kernel

theorem conditioned_301 (code : Nat) :
    conditionedCredit 301 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 301 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 301 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_301
#print axioms conditioned_301

theorem direction_302 :
    5 = geometricCredits.getD 302 0 ∧
    0 = completedCredit 302 ∧
    18 = conditionalCredit 302 := by decide +kernel

theorem conditioned_302 (code : Nat) :
    conditionedCredit 302 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 302 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 302 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_302
#print axioms conditioned_302

theorem direction_303 :
    4 = geometricCredits.getD 303 0 ∧
    0 = completedCredit 303 ∧
    16 = conditionalCredit 303 := by decide +kernel

theorem conditioned_303 (code : Nat) :
    conditionedCredit 303 code = 0 := by
  have hf : canon ((extensions.getD 303 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 303 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_303
#print axioms conditioned_303

theorem direction_304 :
    5 = geometricCredits.getD 304 0 ∧
    16 = completedCredit 304 ∧
    16 = conditionalCredit 304 := by decide +kernel

theorem conditioned_304 (code : Nat) :
    conditionedCredit 304 code = 0 := by
  have hf : canon ((extensions.getD 304 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 304 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_304
#print axioms conditioned_304

theorem direction_305 :
    5 = geometricCredits.getD 305 0 ∧
    12 = completedCredit 305 ∧
    16 = conditionalCredit 305 := by decide +kernel

theorem conditioned_305 (code : Nat) :
    conditionedCredit 305 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 305 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 305 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_305
#print axioms conditioned_305

theorem direction_306 :
    11 = geometricCredits.getD 306 0 ∧
    0 = completedCredit 306 ∧
    16 = conditionalCredit 306 := by decide +kernel

theorem conditioned_306 (code : Nat) :
    conditionedCredit 306 code = 0 := by
  have hf : canon ((extensions.getD 306 []).drop 3) = [0,1,2,0,3,2] := by decide +kernel
  have hb : canon (((extensions.getD 306 []).drop 3).reverse) = [0,1,2,0,3,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_306
#print axioms conditioned_306

theorem direction_307 :
    16 = geometricCredits.getD 307 0 ∧
    0 = completedCredit 307 ∧
    18 = conditionalCredit 307 := by decide +kernel

theorem conditioned_307 (code : Nat) :
    conditionedCredit 307 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 307 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 307 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_307
#print axioms conditioned_307

theorem direction_308 :
    18 = geometricCredits.getD 308 0 ∧
    0 = completedCredit 308 ∧
    18 = conditionalCredit 308 := by decide +kernel

theorem conditioned_308 (code : Nat) :
    conditionedCredit 308 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 308 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 308 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_308
#print axioms conditioned_308

theorem direction_309 :
    13 = geometricCredits.getD 309 0 ∧
    0 = completedCredit 309 ∧
    16 = conditionalCredit 309 := by decide +kernel

theorem conditioned_309 (code : Nat) :
    conditionedCredit 309 code = 0 := by
  have hf : canon ((extensions.getD 309 []).drop 3) = [0,1,2,0,3,2] := by decide +kernel
  have hb : canon (((extensions.getD 309 []).drop 3).reverse) = [0,1,2,0,3,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_309
#print axioms conditioned_309

theorem direction_310 :
    17 = geometricCredits.getD 310 0 ∧
    0 = completedCredit 310 ∧
    18 = conditionalCredit 310 := by decide +kernel

theorem conditioned_310 (code : Nat) :
    conditionedCredit 310 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 310 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 310 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_310
#print axioms conditioned_310

theorem direction_311 :
    16 = geometricCredits.getD 311 0 ∧
    16 = completedCredit 311 ∧
    16 = conditionalCredit 311 := by decide +kernel

theorem conditioned_311 (code : Nat) :
    conditionedCredit 311 code = 0 := by
  have hf : canon ((extensions.getD 311 []).drop 3) = [0,1,2,0,3,1] := by decide +kernel
  have hb : canon (((extensions.getD 311 []).drop 3).reverse) = [0,1,2,3,0,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_311
#print axioms conditioned_311

theorem direction_312 :
    18 = geometricCredits.getD 312 0 ∧
    0 = completedCredit 312 ∧
    18 = conditionalCredit 312 := by decide +kernel

theorem conditioned_312 (code : Nat) :
    conditionedCredit 312 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 312 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 312 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_312
#print axioms conditioned_312

theorem direction_313 :
    12 = geometricCredits.getD 313 0 ∧
    0 = completedCredit 313 ∧
    18 = conditionalCredit 313 := by decide +kernel

theorem conditioned_313 (code : Nat) :
    conditionedCredit 313 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 313 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 313 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_313
#print axioms conditioned_313

theorem direction_314 :
    12 = geometricCredits.getD 314 0 ∧
    12 = completedCredit 314 ∧
    16 = conditionalCredit 314 := by decide +kernel

theorem conditioned_314 (code : Nat) :
    conditionedCredit 314 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 314 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 314 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_314
#print axioms conditioned_314

theorem direction_315 :
    12 = geometricCredits.getD 315 0 ∧
    0 = completedCredit 315 ∧
    16 = conditionalCredit 315 := by decide +kernel

theorem conditioned_315 (code : Nat) :
    conditionedCredit 315 code = 0 := by
  have hf : canon ((extensions.getD 315 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 315 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_315
#print axioms conditioned_315

theorem direction_316 :
    12 = geometricCredits.getD 316 0 ∧
    16 = completedCredit 316 ∧
    16 = conditionalCredit 316 := by decide +kernel

theorem conditioned_316 (code : Nat) :
    conditionedCredit 316 code = 0 := by
  have hf : canon ((extensions.getD 316 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 316 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_316
#print axioms conditioned_316

theorem direction_317 :
    12 = geometricCredits.getD 317 0 ∧
    12 = completedCredit 317 ∧
    16 = conditionalCredit 317 := by decide +kernel

theorem conditioned_317 (code : Nat) :
    conditionedCredit 317 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 317 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 317 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_317
#print axioms conditioned_317

theorem direction_318 :
    29 = geometricCredits.getD 318 0 ∧
    12 = completedCredit 318 ∧
    16 = conditionalCredit 318 := by decide +kernel

theorem conditioned_318 (code : Nat) :
    conditionedCredit 318 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 318 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 318 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_318
#print axioms conditioned_318

theorem direction_319 :
    29 = geometricCredits.getD 319 0 ∧
    0 = completedCredit 319 ∧
    18 = conditionalCredit 319 := by decide +kernel

theorem conditioned_319 (code : Nat) :
    conditionedCredit 319 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 319 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 319 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_319
#print axioms conditioned_319

end Snake9.Context101
