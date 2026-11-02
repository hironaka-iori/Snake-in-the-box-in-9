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

theorem direction_384 :
    0 = geometricCredits.getD 384 0 ∧
    0 = completedCredit 384 ∧
    16 = conditionalCredit 384 := by decide +kernel

theorem conditioned_384 (code : Nat) :
    conditionedCredit 384 code = 0 := by
  have hf : canon ((extensions.getD 384 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 384 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_384
#print axioms conditioned_384

theorem direction_385 :
    0 = geometricCredits.getD 385 0 ∧
    16 = completedCredit 385 ∧
    16 = conditionalCredit 385 := by decide +kernel

theorem conditioned_385 (code : Nat) :
    conditionedCredit 385 code = 0 := by
  have hf : canon ((extensions.getD 385 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 385 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_385
#print axioms conditioned_385

theorem direction_386 :
    0 = geometricCredits.getD 386 0 ∧
    0 = completedCredit 386 ∧
    18 = conditionalCredit 386 := by decide +kernel

theorem conditioned_386 (code : Nat) :
    conditionedCredit 386 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 386 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 386 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_386
#print axioms conditioned_386

theorem direction_387 :
    0 = geometricCredits.getD 387 0 ∧
    12 = completedCredit 387 ∧
    16 = conditionalCredit 387 := by decide +kernel

theorem conditioned_387 (code : Nat) :
    conditionedCredit 387 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 387 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 387 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_387
#print axioms conditioned_387

theorem direction_388 :
    18 = geometricCredits.getD 388 0 ∧
    16 = completedCredit 388 ∧
    16 = conditionalCredit 388 := by decide +kernel

theorem conditioned_388 (code : Nat) :
    conditionedCredit 388 code = 0 := by
  have hf : canon ((extensions.getD 388 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 388 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_388
#print axioms conditioned_388

theorem direction_389 :
    18 = geometricCredits.getD 389 0 ∧
    16 = completedCredit 389 ∧
    16 = conditionalCredit 389 := by decide +kernel

theorem conditioned_389 (code : Nat) :
    conditionedCredit 389 code = 0 := by
  have hf : canon ((extensions.getD 389 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 389 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_389
#print axioms conditioned_389

theorem direction_390 :
    6 = geometricCredits.getD 390 0 ∧
    0 = completedCredit 390 ∧
    16 = conditionalCredit 390 := by decide +kernel

theorem conditioned_390 (code : Nat) :
    conditionedCredit 390 code = 0 := by
  have hf : canon ((extensions.getD 390 []).drop 3) = [0,1,2,3,0,1] := by decide +kernel
  have hb : canon (((extensions.getD 390 []).drop 3).reverse) = [0,1,2,3,0,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_390
#print axioms conditioned_390

theorem direction_391 :
    12 = geometricCredits.getD 391 0 ∧
    16 = completedCredit 391 ∧
    16 = conditionalCredit 391 := by decide +kernel

theorem conditioned_391 (code : Nat) :
    conditionedCredit 391 code = 0 := by
  have hf : canon ((extensions.getD 391 []).drop 3) = [0,1,2,3,0,2] := by decide +kernel
  have hb : canon (((extensions.getD 391 []).drop 3).reverse) = [0,1,2,0,3,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_391
#print axioms conditioned_391

theorem direction_392 :
    18 = geometricCredits.getD 392 0 ∧
    16 = completedCredit 392 ∧
    16 = conditionalCredit 392 := by decide +kernel

theorem conditioned_392 (code : Nat) :
    conditionedCredit 392 code = 0 := by
  have hf : canon ((extensions.getD 392 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 392 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_392
#print axioms conditioned_392

theorem direction_393 :
    5 = geometricCredits.getD 393 0 ∧
    16 = completedCredit 393 ∧
    16 = conditionalCredit 393 := by decide +kernel

theorem conditioned_393 (code : Nat) :
    conditionedCredit 393 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 393 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 393 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_393
#print axioms conditioned_393

theorem direction_394 :
    5 = geometricCredits.getD 394 0 ∧
    16 = completedCredit 394 ∧
    16 = conditionalCredit 394 := by decide +kernel

theorem conditioned_394 (code : Nat) :
    conditionedCredit 394 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 394 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 394 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_394
#print axioms conditioned_394

theorem direction_395 :
    0 = geometricCredits.getD 395 0 ∧
    12 = completedCredit 395 ∧
    12 = conditionalCredit 395 := by decide +kernel

theorem conditioned_395 (code : Nat) :
    conditionedCredit 395 code = 0 := by
  have hf : canon ((extensions.getD 395 []).drop 3) = [0,1,2,3,1,0] := by decide +kernel
  have hb : canon (((extensions.getD 395 []).drop 3).reverse) = [0,1,2,3,1,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_395
#print axioms conditioned_395

theorem direction_396 :
    5 = geometricCredits.getD 396 0 ∧
    16 = completedCredit 396 ∧
    16 = conditionalCredit 396 := by decide +kernel

theorem conditioned_396 (code : Nat) :
    conditionedCredit 396 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 396 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 396 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_396
#print axioms conditioned_396

theorem direction_397 :
    0 = geometricCredits.getD 397 0 ∧
    12 = completedCredit 397 ∧
    16 = conditionalCredit 397 := by decide +kernel

theorem conditioned_397 (code : Nat) :
    conditionedCredit 397 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 397 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 397 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_397
#print axioms conditioned_397

theorem direction_398 :
    0 = geometricCredits.getD 398 0 ∧
    12 = completedCredit 398 ∧
    16 = conditionalCredit 398 := by decide +kernel

theorem conditioned_398 (code : Nat) :
    conditionedCredit 398 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 398 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 398 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_398
#print axioms conditioned_398

theorem direction_399 :
    0 = geometricCredits.getD 399 0 ∧
    0 = completedCredit 399 ∧
    16 = conditionalCredit 399 := by decide +kernel

theorem conditioned_399 (code : Nat) :
    conditionedCredit 399 code = 0 := by
  have hf : canon ((extensions.getD 399 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 399 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_399
#print axioms conditioned_399

theorem direction_400 :
    0 = geometricCredits.getD 400 0 ∧
    16 = completedCredit 400 ∧
    16 = conditionalCredit 400 := by decide +kernel

theorem conditioned_400 (code : Nat) :
    conditionedCredit 400 code = 0 := by
  have hf : canon ((extensions.getD 400 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 400 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_400
#print axioms conditioned_400

theorem direction_401 :
    0 = geometricCredits.getD 401 0 ∧
    0 = completedCredit 401 ∧
    18 = conditionalCredit 401 := by decide +kernel

theorem conditioned_401 (code : Nat) :
    conditionedCredit 401 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 401 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 401 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_401
#print axioms conditioned_401

theorem direction_402 :
    0 = geometricCredits.getD 402 0 ∧
    12 = completedCredit 402 ∧
    16 = conditionalCredit 402 := by decide +kernel

theorem conditioned_402 (code : Nat) :
    conditionedCredit 402 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 402 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 402 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_402
#print axioms conditioned_402

theorem direction_403 :
    0 = geometricCredits.getD 403 0 ∧
    12 = completedCredit 403 ∧
    16 = conditionalCredit 403 := by decide +kernel

theorem conditioned_403 (code : Nat) :
    conditionedCredit 403 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 403 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 403 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_403
#print axioms conditioned_403

theorem direction_404 :
    0 = geometricCredits.getD 404 0 ∧
    0 = completedCredit 404 ∧
    16 = conditionalCredit 404 := by decide +kernel

theorem conditioned_404 (code : Nat) :
    conditionedCredit 404 code = 0 := by
  have hf : canon ((extensions.getD 404 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 404 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_404
#print axioms conditioned_404

theorem direction_405 :
    0 = geometricCredits.getD 405 0 ∧
    16 = completedCredit 405 ∧
    16 = conditionalCredit 405 := by decide +kernel

theorem conditioned_405 (code : Nat) :
    conditionedCredit 405 code = 0 := by
  have hf : canon ((extensions.getD 405 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 405 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_405
#print axioms conditioned_405

theorem direction_406 :
    0 = geometricCredits.getD 406 0 ∧
    0 = completedCredit 406 ∧
    18 = conditionalCredit 406 := by decide +kernel

theorem conditioned_406 (code : Nat) :
    conditionedCredit 406 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 406 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 406 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_406
#print axioms conditioned_406

theorem direction_407 :
    0 = geometricCredits.getD 407 0 ∧
    12 = completedCredit 407 ∧
    16 = conditionalCredit 407 := by decide +kernel

theorem conditioned_407 (code : Nat) :
    conditionedCredit 407 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 407 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 407 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_407
#print axioms conditioned_407

theorem direction_408 :
    22 = geometricCredits.getD 408 0 ∧
    12 = completedCredit 408 ∧
    16 = conditionalCredit 408 := by decide +kernel

theorem conditioned_408 (code : Nat) :
    conditionedCredit 408 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 408 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 408 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_408
#print axioms conditioned_408

theorem direction_409 :
    22 = geometricCredits.getD 409 0 ∧
    0 = completedCredit 409 ∧
    16 = conditionalCredit 409 := by decide +kernel

theorem conditioned_409 (code : Nat) :
    conditionedCredit 409 code = 0 := by
  have hf : canon ((extensions.getD 409 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 409 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_409
#print axioms conditioned_409

theorem direction_410 :
    16 = geometricCredits.getD 410 0 ∧
    16 = completedCredit 410 ∧
    16 = conditionalCredit 410 := by decide +kernel

theorem conditioned_410 (code : Nat) :
    conditionedCredit 410 code = 0 := by
  have hf : canon ((extensions.getD 410 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 410 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_410
#print axioms conditioned_410

theorem direction_411 :
    6 = geometricCredits.getD 411 0 ∧
    0 = completedCredit 411 ∧
    18 = conditionalCredit 411 := by decide +kernel

theorem conditioned_411 (code : Nat) :
    conditionedCredit 411 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 411 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 411 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_411
#print axioms conditioned_411

theorem direction_412 :
    22 = geometricCredits.getD 412 0 ∧
    12 = completedCredit 412 ∧
    16 = conditionalCredit 412 := by decide +kernel

theorem conditioned_412 (code : Nat) :
    conditionedCredit 412 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 412 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 412 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_412
#print axioms conditioned_412

theorem direction_413 :
    25 = geometricCredits.getD 413 0 ∧
    16 = completedCredit 413 ∧
    16 = conditionalCredit 413 := by decide +kernel

theorem conditioned_413 (code : Nat) :
    conditionedCredit 413 code = 0 := by
  have hf : canon ((extensions.getD 413 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 413 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_413
#print axioms conditioned_413

theorem direction_414 :
    25 = geometricCredits.getD 414 0 ∧
    16 = completedCredit 414 ∧
    16 = conditionalCredit 414 := by decide +kernel

theorem conditioned_414 (code : Nat) :
    conditionedCredit 414 code = 0 := by
  have hf : canon ((extensions.getD 414 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 414 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_414
#print axioms conditioned_414

theorem direction_415 :
    10 = geometricCredits.getD 415 0 ∧
    0 = completedCredit 415 ∧
    16 = conditionalCredit 415 := by decide +kernel

theorem conditioned_415 (code : Nat) :
    conditionedCredit 415 code = 0 := by
  have hf : canon ((extensions.getD 415 []).drop 3) = [0,1,2,3,0,1] := by decide +kernel
  have hb : canon (((extensions.getD 415 []).drop 3).reverse) = [0,1,2,3,0,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_415
#print axioms conditioned_415

theorem direction_416 :
    15 = geometricCredits.getD 416 0 ∧
    16 = completedCredit 416 ∧
    16 = conditionalCredit 416 := by decide +kernel

theorem conditioned_416 (code : Nat) :
    conditionedCredit 416 code = 0 := by
  have hf : canon ((extensions.getD 416 []).drop 3) = [0,1,2,3,0,2] := by decide +kernel
  have hb : canon (((extensions.getD 416 []).drop 3).reverse) = [0,1,2,0,3,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_416
#print axioms conditioned_416

theorem direction_417 :
    25 = geometricCredits.getD 417 0 ∧
    16 = completedCredit 417 ∧
    16 = conditionalCredit 417 := by decide +kernel

theorem conditioned_417 (code : Nat) :
    conditionedCredit 417 code = 0 := by
  have hf : canon ((extensions.getD 417 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 417 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_417
#print axioms conditioned_417

theorem direction_418 :
    7 = geometricCredits.getD 418 0 ∧
    16 = completedCredit 418 ∧
    16 = conditionalCredit 418 := by decide +kernel

theorem conditioned_418 (code : Nat) :
    conditionedCredit 418 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 418 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 418 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_418
#print axioms conditioned_418

theorem direction_419 :
    7 = geometricCredits.getD 419 0 ∧
    16 = completedCredit 419 ∧
    16 = conditionalCredit 419 := by decide +kernel

theorem conditioned_419 (code : Nat) :
    conditionedCredit 419 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 419 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 419 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_419
#print axioms conditioned_419

theorem direction_420 :
    0 = geometricCredits.getD 420 0 ∧
    12 = completedCredit 420 ∧
    12 = conditionalCredit 420 := by decide +kernel

theorem conditioned_420 (code : Nat) :
    conditionedCredit 420 code = 0 := by
  have hf : canon ((extensions.getD 420 []).drop 3) = [0,1,2,3,1,0] := by decide +kernel
  have hb : canon (((extensions.getD 420 []).drop 3).reverse) = [0,1,2,3,1,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_420
#print axioms conditioned_420

theorem direction_421 :
    7 = geometricCredits.getD 421 0 ∧
    16 = completedCredit 421 ∧
    16 = conditionalCredit 421 := by decide +kernel

theorem conditioned_421 (code : Nat) :
    conditionedCredit 421 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 421 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 421 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_421
#print axioms conditioned_421

theorem direction_422 :
    0 = geometricCredits.getD 422 0 ∧
    12 = completedCredit 422 ∧
    16 = conditionalCredit 422 := by decide +kernel

theorem conditioned_422 (code : Nat) :
    conditionedCredit 422 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 422 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 422 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_422
#print axioms conditioned_422

theorem direction_423 :
    0 = geometricCredits.getD 423 0 ∧
    12 = completedCredit 423 ∧
    16 = conditionalCredit 423 := by decide +kernel

theorem conditioned_423 (code : Nat) :
    conditionedCredit 423 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 423 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 423 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_423
#print axioms conditioned_423

theorem direction_424 :
    0 = geometricCredits.getD 424 0 ∧
    0 = completedCredit 424 ∧
    16 = conditionalCredit 424 := by decide +kernel

theorem conditioned_424 (code : Nat) :
    conditionedCredit 424 code = 0 := by
  have hf : canon ((extensions.getD 424 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 424 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_424
#print axioms conditioned_424

theorem direction_425 :
    0 = geometricCredits.getD 425 0 ∧
    16 = completedCredit 425 ∧
    16 = conditionalCredit 425 := by decide +kernel

theorem conditioned_425 (code : Nat) :
    conditionedCredit 425 code = 0 := by
  have hf : canon ((extensions.getD 425 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 425 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_425
#print axioms conditioned_425

theorem direction_426 :
    0 = geometricCredits.getD 426 0 ∧
    0 = completedCredit 426 ∧
    18 = conditionalCredit 426 := by decide +kernel

theorem conditioned_426 (code : Nat) :
    conditionedCredit 426 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 426 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 426 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_426
#print axioms conditioned_426

theorem direction_427 :
    0 = geometricCredits.getD 427 0 ∧
    12 = completedCredit 427 ∧
    16 = conditionalCredit 427 := by decide +kernel

theorem conditioned_427 (code : Nat) :
    conditionedCredit 427 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 427 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 427 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_427
#print axioms conditioned_427

theorem direction_428 :
    13 = geometricCredits.getD 428 0 ∧
    12 = completedCredit 428 ∧
    16 = conditionalCredit 428 := by decide +kernel

theorem conditioned_428 (code : Nat) :
    conditionedCredit 428 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 428 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 428 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_428
#print axioms conditioned_428

theorem direction_429 :
    13 = geometricCredits.getD 429 0 ∧
    0 = completedCredit 429 ∧
    16 = conditionalCredit 429 := by decide +kernel

theorem conditioned_429 (code : Nat) :
    conditionedCredit 429 code = 0 := by
  have hf : canon ((extensions.getD 429 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 429 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_429
#print axioms conditioned_429

theorem direction_430 :
    13 = geometricCredits.getD 430 0 ∧
    16 = completedCredit 430 ∧
    16 = conditionalCredit 430 := by decide +kernel

theorem conditioned_430 (code : Nat) :
    conditionedCredit 430 code = 0 := by
  have hf : canon ((extensions.getD 430 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 430 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_430
#print axioms conditioned_430

theorem direction_431 :
    13 = geometricCredits.getD 431 0 ∧
    0 = completedCredit 431 ∧
    18 = conditionalCredit 431 := by decide +kernel

theorem conditioned_431 (code : Nat) :
    conditionedCredit 431 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 431 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 431 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_431
#print axioms conditioned_431

theorem direction_432 :
    13 = geometricCredits.getD 432 0 ∧
    12 = completedCredit 432 ∧
    16 = conditionalCredit 432 := by decide +kernel

theorem conditioned_432 (code : Nat) :
    conditionedCredit 432 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 432 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 432 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_432
#print axioms conditioned_432

theorem direction_433 :
    54 = geometricCredits.getD 433 0 ∧
    12 = completedCredit 433 ∧
    16 = conditionalCredit 433 := by decide +kernel

theorem conditioned_433 (code : Nat) :
    conditionedCredit 433 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 433 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 433 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_433
#print axioms conditioned_433

theorem direction_434 :
    45 = geometricCredits.getD 434 0 ∧
    0 = completedCredit 434 ∧
    16 = conditionalCredit 434 := by decide +kernel

theorem conditioned_434 (code : Nat) :
    conditionedCredit 434 code = 0 := by
  have hf : canon ((extensions.getD 434 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 434 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_434
#print axioms conditioned_434

theorem direction_435 :
    43 = geometricCredits.getD 435 0 ∧
    16 = completedCredit 435 ∧
    16 = conditionalCredit 435 := by decide +kernel

theorem conditioned_435 (code : Nat) :
    conditionedCredit 435 code = 0 := by
  have hf : canon ((extensions.getD 435 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 435 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_435
#print axioms conditioned_435

theorem direction_436 :
    33 = geometricCredits.getD 436 0 ∧
    0 = completedCredit 436 ∧
    18 = conditionalCredit 436 := by decide +kernel

theorem conditioned_436 (code : Nat) :
    conditionedCredit 436 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 436 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 436 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_436
#print axioms conditioned_436

theorem direction_437 :
    54 = geometricCredits.getD 437 0 ∧
    12 = completedCredit 437 ∧
    16 = conditionalCredit 437 := by decide +kernel

theorem conditioned_437 (code : Nat) :
    conditionedCredit 437 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 437 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 437 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_437
#print axioms conditioned_437

theorem direction_438 :
    6 = geometricCredits.getD 438 0 ∧
    16 = completedCredit 438 ∧
    16 = conditionalCredit 438 := by decide +kernel

theorem conditioned_438 (code : Nat) :
    conditionedCredit 438 code = 0 := by
  have hf : canon ((extensions.getD 438 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 438 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_438
#print axioms conditioned_438

theorem direction_439 :
    6 = geometricCredits.getD 439 0 ∧
    16 = completedCredit 439 ∧
    16 = conditionalCredit 439 := by decide +kernel

theorem conditioned_439 (code : Nat) :
    conditionedCredit 439 code = 0 := by
  have hf : canon ((extensions.getD 439 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 439 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_439
#print axioms conditioned_439

theorem direction_440 :
    6 = geometricCredits.getD 440 0 ∧
    16 = completedCredit 440 ∧
    16 = conditionalCredit 440 := by decide +kernel

theorem conditioned_440 (code : Nat) :
    conditionedCredit 440 code = 0 := by
  have hf : canon ((extensions.getD 440 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 440 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_440
#print axioms conditioned_440

theorem direction_441 :
    11 = geometricCredits.getD 441 0 ∧
    16 = completedCredit 441 ∧
    16 = conditionalCredit 441 := by decide +kernel

theorem conditioned_441 (code : Nat) :
    conditionedCredit 441 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 441 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 441 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_441
#print axioms conditioned_441

theorem direction_442 :
    11 = geometricCredits.getD 442 0 ∧
    16 = completedCredit 442 ∧
    16 = conditionalCredit 442 := by decide +kernel

theorem conditioned_442 (code : Nat) :
    conditionedCredit 442 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 442 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 442 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_442
#print axioms conditioned_442

theorem direction_443 :
    11 = geometricCredits.getD 443 0 ∧
    16 = completedCredit 443 ∧
    16 = conditionalCredit 443 := by decide +kernel

theorem conditioned_443 (code : Nat) :
    conditionedCredit 443 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 443 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 443 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_443
#print axioms conditioned_443

theorem direction_444 :
    13 = geometricCredits.getD 444 0 ∧
    12 = completedCredit 444 ∧
    16 = conditionalCredit 444 := by decide +kernel

theorem conditioned_444 (code : Nat) :
    conditionedCredit 444 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 444 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 444 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_444
#print axioms conditioned_444

theorem direction_445 :
    13 = geometricCredits.getD 445 0 ∧
    12 = completedCredit 445 ∧
    16 = conditionalCredit 445 := by decide +kernel

theorem conditioned_445 (code : Nat) :
    conditionedCredit 445 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 445 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 445 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_445
#print axioms conditioned_445

theorem direction_446 :
    13 = geometricCredits.getD 446 0 ∧
    0 = completedCredit 446 ∧
    16 = conditionalCredit 446 := by decide +kernel

theorem conditioned_446 (code : Nat) :
    conditionedCredit 446 code = 0 := by
  have hf : canon ((extensions.getD 446 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 446 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_446
#print axioms conditioned_446

theorem direction_447 :
    13 = geometricCredits.getD 447 0 ∧
    16 = completedCredit 447 ∧
    16 = conditionalCredit 447 := by decide +kernel

theorem conditioned_447 (code : Nat) :
    conditionedCredit 447 code = 0 := by
  have hf : canon ((extensions.getD 447 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 447 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_447
#print axioms conditioned_447

end Snake9.Context101
