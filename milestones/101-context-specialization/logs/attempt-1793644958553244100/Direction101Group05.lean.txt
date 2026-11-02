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

theorem direction_320 :
    24 = geometricCredits.getD 320 0 ∧
    0 = completedCredit 320 ∧
    16 = conditionalCredit 320 := by decide +kernel

theorem conditioned_320 (code : Nat) :
    conditionedCredit 320 code = 0 := by
  have hf : canon ((extensions.getD 320 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 320 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_320
#print axioms conditioned_320

theorem direction_321 :
    21 = geometricCredits.getD 321 0 ∧
    16 = completedCredit 321 ∧
    16 = conditionalCredit 321 := by decide +kernel

theorem conditioned_321 (code : Nat) :
    conditionedCredit 321 code = 0 := by
  have hf : canon ((extensions.getD 321 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 321 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_321
#print axioms conditioned_321

theorem direction_322 :
    29 = geometricCredits.getD 322 0 ∧
    12 = completedCredit 322 ∧
    16 = conditionalCredit 322 := by decide +kernel

theorem conditioned_322 (code : Nat) :
    conditionedCredit 322 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 322 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 322 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_322
#print axioms conditioned_322

theorem direction_323 :
    44 = geometricCredits.getD 323 0 ∧
    16 = completedCredit 323 ∧
    16 = conditionalCredit 323 := by decide +kernel

theorem conditioned_323 (code : Nat) :
    conditionedCredit 323 code = 0 := by
  have hf : canon ((extensions.getD 323 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 323 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_323
#print axioms conditioned_323

theorem direction_324 :
    37 = geometricCredits.getD 324 0 ∧
    16 = completedCredit 324 ∧
    16 = conditionalCredit 324 := by decide +kernel

theorem conditioned_324 (code : Nat) :
    conditionedCredit 324 code = 0 := by
  have hf : canon ((extensions.getD 324 []).drop 3) = [0,1,2,3,0,2] := by decide +kernel
  have hb : canon (((extensions.getD 324 []).drop 3).reverse) = [0,1,2,0,3,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_324
#print axioms conditioned_324

theorem direction_325 :
    38 = geometricCredits.getD 325 0 ∧
    16 = completedCredit 325 ∧
    16 = conditionalCredit 325 := by decide +kernel

theorem conditioned_325 (code : Nat) :
    conditionedCredit 325 code = 0 := by
  have hf : canon ((extensions.getD 325 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 325 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_325
#print axioms conditioned_325

theorem direction_326 :
    27 = geometricCredits.getD 326 0 ∧
    0 = completedCredit 326 ∧
    16 = conditionalCredit 326 := by decide +kernel

theorem conditioned_326 (code : Nat) :
    conditionedCredit 326 code = 0 := by
  have hf : canon ((extensions.getD 326 []).drop 3) = [0,1,2,3,0,1] := by decide +kernel
  have hb : canon (((extensions.getD 326 []).drop 3).reverse) = [0,1,2,3,0,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_326
#print axioms conditioned_326

theorem direction_327 :
    44 = geometricCredits.getD 327 0 ∧
    16 = completedCredit 327 ∧
    16 = conditionalCredit 327 := by decide +kernel

theorem conditioned_327 (code : Nat) :
    conditionedCredit 327 code = 0 := by
  have hf : canon ((extensions.getD 327 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 327 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_327
#print axioms conditioned_327

theorem direction_328 :
    25 = geometricCredits.getD 328 0 ∧
    16 = completedCredit 328 ∧
    16 = conditionalCredit 328 := by decide +kernel

theorem conditioned_328 (code : Nat) :
    conditionedCredit 328 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 328 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 328 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_328
#print axioms conditioned_328

theorem direction_329 :
    19 = geometricCredits.getD 329 0 ∧
    16 = completedCredit 329 ∧
    16 = conditionalCredit 329 := by decide +kernel

theorem conditioned_329 (code : Nat) :
    conditionedCredit 329 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 329 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 329 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_329
#print axioms conditioned_329

theorem direction_330 :
    18 = geometricCredits.getD 330 0 ∧
    12 = completedCredit 330 ∧
    12 = conditionalCredit 330 := by decide +kernel

theorem conditioned_330 (code : Nat) :
    conditionedCredit 330 code = 0 := by
  have hf : canon ((extensions.getD 330 []).drop 3) = [0,1,2,3,1,0] := by decide +kernel
  have hb : canon (((extensions.getD 330 []).drop 3).reverse) = [0,1,2,3,1,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_330
#print axioms conditioned_330

theorem direction_331 :
    25 = geometricCredits.getD 331 0 ∧
    16 = completedCredit 331 ∧
    16 = conditionalCredit 331 := by decide +kernel

theorem conditioned_331 (code : Nat) :
    conditionedCredit 331 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 331 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 331 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_331
#print axioms conditioned_331

theorem direction_332 :
    12 = geometricCredits.getD 332 0 ∧
    12 = completedCredit 332 ∧
    16 = conditionalCredit 332 := by decide +kernel

theorem conditioned_332 (code : Nat) :
    conditionedCredit 332 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 332 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 332 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_332
#print axioms conditioned_332

theorem direction_333 :
    12 = geometricCredits.getD 333 0 ∧
    0 = completedCredit 333 ∧
    18 = conditionalCredit 333 := by decide +kernel

theorem conditioned_333 (code : Nat) :
    conditionedCredit 333 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 333 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 333 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_333
#print axioms conditioned_333

theorem direction_334 :
    12 = geometricCredits.getD 334 0 ∧
    12 = completedCredit 334 ∧
    16 = conditionalCredit 334 := by decide +kernel

theorem conditioned_334 (code : Nat) :
    conditionedCredit 334 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 334 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 334 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_334
#print axioms conditioned_334

theorem direction_335 :
    12 = geometricCredits.getD 335 0 ∧
    0 = completedCredit 335 ∧
    16 = conditionalCredit 335 := by decide +kernel

theorem conditioned_335 (code : Nat) :
    conditionedCredit 335 code = 0 := by
  have hf : canon ((extensions.getD 335 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 335 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_335
#print axioms conditioned_335

theorem direction_336 :
    12 = geometricCredits.getD 336 0 ∧
    16 = completedCredit 336 ∧
    16 = conditionalCredit 336 := by decide +kernel

theorem conditioned_336 (code : Nat) :
    conditionedCredit 336 code = 0 := by
  have hf : canon ((extensions.getD 336 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 336 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_336
#print axioms conditioned_336

theorem direction_337 :
    12 = geometricCredits.getD 337 0 ∧
    12 = completedCredit 337 ∧
    16 = conditionalCredit 337 := by decide +kernel

theorem conditioned_337 (code : Nat) :
    conditionedCredit 337 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 337 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 337 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_337
#print axioms conditioned_337

theorem direction_338 :
    21 = geometricCredits.getD 338 0 ∧
    0 = completedCredit 338 ∧
    18 = conditionalCredit 338 := by decide +kernel

theorem conditioned_338 (code : Nat) :
    conditionedCredit 338 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 338 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 338 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_338
#print axioms conditioned_338

theorem direction_339 :
    22 = geometricCredits.getD 339 0 ∧
    12 = completedCredit 339 ∧
    16 = conditionalCredit 339 := by decide +kernel

theorem conditioned_339 (code : Nat) :
    conditionedCredit 339 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 339 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 339 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_339
#print axioms conditioned_339

theorem direction_340 :
    14 = geometricCredits.getD 340 0 ∧
    16 = completedCredit 340 ∧
    16 = conditionalCredit 340 := by decide +kernel

theorem conditioned_340 (code : Nat) :
    conditionedCredit 340 code = 0 := by
  have hf : canon ((extensions.getD 340 []).drop 3) = [0,1,2,3,0,2] := by decide +kernel
  have hb : canon (((extensions.getD 340 []).drop 3).reverse) = [0,1,2,0,3,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_340
#print axioms conditioned_340

theorem direction_341 :
    20 = geometricCredits.getD 341 0 ∧
    16 = completedCredit 341 ∧
    16 = conditionalCredit 341 := by decide +kernel

theorem conditioned_341 (code : Nat) :
    conditionedCredit 341 code = 0 := by
  have hf : canon ((extensions.getD 341 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 341 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_341
#print axioms conditioned_341

theorem direction_342 :
    9 = geometricCredits.getD 342 0 ∧
    16 = completedCredit 342 ∧
    16 = conditionalCredit 342 := by decide +kernel

theorem conditioned_342 (code : Nat) :
    conditionedCredit 342 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 342 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 342 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_342
#print axioms conditioned_342

theorem direction_343 :
    9 = geometricCredits.getD 343 0 ∧
    12 = completedCredit 343 ∧
    16 = conditionalCredit 343 := by decide +kernel

theorem conditioned_343 (code : Nat) :
    conditionedCredit 343 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 343 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 343 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_343
#print axioms conditioned_343

theorem direction_344 :
    9 = geometricCredits.getD 344 0 ∧
    0 = completedCredit 344 ∧
    18 = conditionalCredit 344 := by decide +kernel

theorem conditioned_344 (code : Nat) :
    conditionedCredit 344 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 344 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 344 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_344
#print axioms conditioned_344

theorem direction_345 :
    9 = geometricCredits.getD 345 0 ∧
    0 = completedCredit 345 ∧
    16 = conditionalCredit 345 := by decide +kernel

theorem conditioned_345 (code : Nat) :
    conditionedCredit 345 code = 0 := by
  have hf : canon ((extensions.getD 345 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 345 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_345
#print axioms conditioned_345

theorem direction_346 :
    9 = geometricCredits.getD 346 0 ∧
    16 = completedCredit 346 ∧
    16 = conditionalCredit 346 := by decide +kernel

theorem conditioned_346 (code : Nat) :
    conditionedCredit 346 code = 0 := by
  have hf : canon ((extensions.getD 346 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 346 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_346
#print axioms conditioned_346

theorem direction_347 :
    9 = geometricCredits.getD 347 0 ∧
    12 = completedCredit 347 ∧
    16 = conditionalCredit 347 := by decide +kernel

theorem conditioned_347 (code : Nat) :
    conditionedCredit 347 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 347 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 347 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_347
#print axioms conditioned_347

theorem direction_348 :
    0 = geometricCredits.getD 348 0 ∧
    0 = completedCredit 348 ∧
    18 = conditionalCredit 348 := by decide +kernel

theorem conditioned_348 (code : Nat) :
    conditionedCredit 348 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 348 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 348 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_348
#print axioms conditioned_348

theorem direction_349 :
    0 = geometricCredits.getD 349 0 ∧
    12 = completedCredit 349 ∧
    16 = conditionalCredit 349 := by decide +kernel

theorem conditioned_349 (code : Nat) :
    conditionedCredit 349 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 349 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 349 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_349
#print axioms conditioned_349

theorem direction_350 :
    0 = geometricCredits.getD 350 0 ∧
    12 = completedCredit 350 ∧
    16 = conditionalCredit 350 := by decide +kernel

theorem conditioned_350 (code : Nat) :
    conditionedCredit 350 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 350 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 350 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_350
#print axioms conditioned_350

theorem direction_351 :
    0 = geometricCredits.getD 351 0 ∧
    0 = completedCredit 351 ∧
    18 = conditionalCredit 351 := by decide +kernel

theorem conditioned_351 (code : Nat) :
    conditionedCredit 351 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 351 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 351 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_351
#print axioms conditioned_351

theorem direction_352 :
    0 = geometricCredits.getD 352 0 ∧
    0 = completedCredit 352 ∧
    16 = conditionalCredit 352 := by decide +kernel

theorem conditioned_352 (code : Nat) :
    conditionedCredit 352 code = 0 := by
  have hf : canon ((extensions.getD 352 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 352 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_352
#print axioms conditioned_352

theorem direction_353 :
    0 = geometricCredits.getD 353 0 ∧
    16 = completedCredit 353 ∧
    16 = conditionalCredit 353 := by decide +kernel

theorem conditioned_353 (code : Nat) :
    conditionedCredit 353 code = 0 := by
  have hf : canon ((extensions.getD 353 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 353 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_353
#print axioms conditioned_353

theorem direction_354 :
    0 = geometricCredits.getD 354 0 ∧
    12 = completedCredit 354 ∧
    16 = conditionalCredit 354 := by decide +kernel

theorem conditioned_354 (code : Nat) :
    conditionedCredit 354 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 354 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 354 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_354
#print axioms conditioned_354

theorem direction_355 :
    9 = geometricCredits.getD 355 0 ∧
    12 = completedCredit 355 ∧
    16 = conditionalCredit 355 := by decide +kernel

theorem conditioned_355 (code : Nat) :
    conditionedCredit 355 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 355 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 355 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_355
#print axioms conditioned_355

theorem direction_356 :
    9 = geometricCredits.getD 356 0 ∧
    0 = completedCredit 356 ∧
    18 = conditionalCredit 356 := by decide +kernel

theorem conditioned_356 (code : Nat) :
    conditionedCredit 356 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 356 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 356 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_356
#print axioms conditioned_356

theorem direction_357 :
    9 = geometricCredits.getD 357 0 ∧
    0 = completedCredit 357 ∧
    16 = conditionalCredit 357 := by decide +kernel

theorem conditioned_357 (code : Nat) :
    conditionedCredit 357 code = 0 := by
  have hf : canon ((extensions.getD 357 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 357 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_357
#print axioms conditioned_357

theorem direction_358 :
    9 = geometricCredits.getD 358 0 ∧
    16 = completedCredit 358 ∧
    16 = conditionalCredit 358 := by decide +kernel

theorem conditioned_358 (code : Nat) :
    conditionedCredit 358 code = 0 := by
  have hf : canon ((extensions.getD 358 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 358 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_358
#print axioms conditioned_358

theorem direction_359 :
    9 = geometricCredits.getD 359 0 ∧
    12 = completedCredit 359 ∧
    16 = conditionalCredit 359 := by decide +kernel

theorem conditioned_359 (code : Nat) :
    conditionedCredit 359 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 359 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 359 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_359
#print axioms conditioned_359

theorem direction_360 :
    33 = geometricCredits.getD 360 0 ∧
    12 = completedCredit 360 ∧
    16 = conditionalCredit 360 := by decide +kernel

theorem conditioned_360 (code : Nat) :
    conditionedCredit 360 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 360 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 360 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_360
#print axioms conditioned_360

theorem direction_361 :
    32 = geometricCredits.getD 361 0 ∧
    0 = completedCredit 361 ∧
    18 = conditionalCredit 361 := by decide +kernel

theorem conditioned_361 (code : Nat) :
    conditionedCredit 361 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 361 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 361 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_361
#print axioms conditioned_361

theorem direction_362 :
    23 = geometricCredits.getD 362 0 ∧
    0 = completedCredit 362 ∧
    16 = conditionalCredit 362 := by decide +kernel

theorem conditioned_362 (code : Nat) :
    conditionedCredit 362 code = 0 := by
  have hf : canon ((extensions.getD 362 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 362 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_362
#print axioms conditioned_362

theorem direction_363 :
    22 = geometricCredits.getD 363 0 ∧
    16 = completedCredit 363 ∧
    16 = conditionalCredit 363 := by decide +kernel

theorem conditioned_363 (code : Nat) :
    conditionedCredit 363 code = 0 := by
  have hf : canon ((extensions.getD 363 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 363 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_363
#print axioms conditioned_363

theorem direction_364 :
    33 = geometricCredits.getD 364 0 ∧
    12 = completedCredit 364 ∧
    16 = conditionalCredit 364 := by decide +kernel

theorem conditioned_364 (code : Nat) :
    conditionedCredit 364 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 364 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 364 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_364
#print axioms conditioned_364

theorem direction_365 :
    22 = geometricCredits.getD 365 0 ∧
    16 = completedCredit 365 ∧
    16 = conditionalCredit 365 := by decide +kernel

theorem conditioned_365 (code : Nat) :
    conditionedCredit 365 code = 0 := by
  have hf : canon ((extensions.getD 365 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 365 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_365
#print axioms conditioned_365

theorem direction_366 :
    17 = geometricCredits.getD 366 0 ∧
    16 = completedCredit 366 ∧
    16 = conditionalCredit 366 := by decide +kernel

theorem conditioned_366 (code : Nat) :
    conditionedCredit 366 code = 0 := by
  have hf : canon ((extensions.getD 366 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 366 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_366
#print axioms conditioned_366

theorem direction_367 :
    16 = geometricCredits.getD 367 0 ∧
    16 = completedCredit 367 ∧
    16 = conditionalCredit 367 := by decide +kernel

theorem conditioned_367 (code : Nat) :
    conditionedCredit 367 code = 0 := by
  have hf : canon ((extensions.getD 367 []).drop 3) = [0,1,2,3,0,2] := by decide +kernel
  have hb : canon (((extensions.getD 367 []).drop 3).reverse) = [0,1,2,0,3,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_367
#print axioms conditioned_367

theorem direction_368 :
    22 = geometricCredits.getD 368 0 ∧
    16 = completedCredit 368 ∧
    16 = conditionalCredit 368 := by decide +kernel

theorem conditioned_368 (code : Nat) :
    conditionedCredit 368 code = 0 := by
  have hf : canon ((extensions.getD 368 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 368 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_368
#print axioms conditioned_368

theorem direction_369 :
    10 = geometricCredits.getD 369 0 ∧
    16 = completedCredit 369 ∧
    16 = conditionalCredit 369 := by decide +kernel

theorem conditioned_369 (code : Nat) :
    conditionedCredit 369 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 369 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 369 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_369
#print axioms conditioned_369

theorem direction_370 :
    5 = geometricCredits.getD 370 0 ∧
    16 = completedCredit 370 ∧
    16 = conditionalCredit 370 := by decide +kernel

theorem conditioned_370 (code : Nat) :
    conditionedCredit 370 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 370 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 370 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_370
#print axioms conditioned_370

theorem direction_371 :
    10 = geometricCredits.getD 371 0 ∧
    16 = completedCredit 371 ∧
    16 = conditionalCredit 371 := by decide +kernel

theorem conditioned_371 (code : Nat) :
    conditionedCredit 371 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 371 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 371 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_371
#print axioms conditioned_371

theorem direction_372 :
    9 = geometricCredits.getD 372 0 ∧
    12 = completedCredit 372 ∧
    16 = conditionalCredit 372 := by decide +kernel

theorem conditioned_372 (code : Nat) :
    conditionedCredit 372 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 372 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 372 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_372
#print axioms conditioned_372

theorem direction_373 :
    9 = geometricCredits.getD 373 0 ∧
    12 = completedCredit 373 ∧
    16 = conditionalCredit 373 := by decide +kernel

theorem conditioned_373 (code : Nat) :
    conditionedCredit 373 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 373 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 373 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_373
#print axioms conditioned_373

theorem direction_374 :
    9 = geometricCredits.getD 374 0 ∧
    0 = completedCredit 374 ∧
    18 = conditionalCredit 374 := by decide +kernel

theorem conditioned_374 (code : Nat) :
    conditionedCredit 374 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 374 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 374 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_374
#print axioms conditioned_374

theorem direction_375 :
    9 = geometricCredits.getD 375 0 ∧
    0 = completedCredit 375 ∧
    16 = conditionalCredit 375 := by decide +kernel

theorem conditioned_375 (code : Nat) :
    conditionedCredit 375 code = 0 := by
  have hf : canon ((extensions.getD 375 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 375 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_375
#print axioms conditioned_375

theorem direction_376 :
    9 = geometricCredits.getD 376 0 ∧
    16 = completedCredit 376 ∧
    16 = conditionalCredit 376 := by decide +kernel

theorem conditioned_376 (code : Nat) :
    conditionedCredit 376 code = 0 := by
  have hf : canon ((extensions.getD 376 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 376 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_376
#print axioms conditioned_376

theorem direction_377 :
    9 = geometricCredits.getD 377 0 ∧
    12 = completedCredit 377 ∧
    16 = conditionalCredit 377 := by decide +kernel

theorem conditioned_377 (code : Nat) :
    conditionedCredit 377 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 377 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 377 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_377
#print axioms conditioned_377

theorem direction_378 :
    0 = geometricCredits.getD 378 0 ∧
    12 = completedCredit 378 ∧
    16 = conditionalCredit 378 := by decide +kernel

theorem conditioned_378 (code : Nat) :
    conditionedCredit 378 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 378 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 378 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_378
#print axioms conditioned_378

theorem direction_379 :
    0 = geometricCredits.getD 379 0 ∧
    0 = completedCredit 379 ∧
    16 = conditionalCredit 379 := by decide +kernel

theorem conditioned_379 (code : Nat) :
    conditionedCredit 379 code = 0 := by
  have hf : canon ((extensions.getD 379 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 379 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_379
#print axioms conditioned_379

theorem direction_380 :
    0 = geometricCredits.getD 380 0 ∧
    16 = completedCredit 380 ∧
    16 = conditionalCredit 380 := by decide +kernel

theorem conditioned_380 (code : Nat) :
    conditionedCredit 380 code = 0 := by
  have hf : canon ((extensions.getD 380 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 380 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_380
#print axioms conditioned_380

theorem direction_381 :
    0 = geometricCredits.getD 381 0 ∧
    0 = completedCredit 381 ∧
    18 = conditionalCredit 381 := by decide +kernel

theorem conditioned_381 (code : Nat) :
    conditionedCredit 381 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 381 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 381 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_381
#print axioms conditioned_381

theorem direction_382 :
    0 = geometricCredits.getD 382 0 ∧
    12 = completedCredit 382 ∧
    16 = conditionalCredit 382 := by decide +kernel

theorem conditioned_382 (code : Nat) :
    conditionedCredit 382 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 382 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 382 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_382
#print axioms conditioned_382

theorem direction_383 :
    0 = geometricCredits.getD 383 0 ∧
    12 = completedCredit 383 ∧
    16 = conditionalCredit 383 := by decide +kernel

theorem conditioned_383 (code : Nat) :
    conditionedCredit 383 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 383 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 383 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_383
#print axioms conditioned_383

end Snake9.Context101
