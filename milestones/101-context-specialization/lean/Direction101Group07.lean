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

theorem direction_448 :
    13 = geometricCredits.getD 448 0 ∧
    0 = completedCredit 448 ∧
    18 = conditionalCredit 448 := by decide +kernel

theorem conditioned_448 (code : Nat) :
    conditionedCredit 448 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 448 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 448 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_448
#print axioms conditioned_448

theorem direction_449 :
    13 = geometricCredits.getD 449 0 ∧
    12 = completedCredit 449 ∧
    16 = conditionalCredit 449 := by decide +kernel

theorem conditioned_449 (code : Nat) :
    conditionedCredit 449 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 449 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 449 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_449
#print axioms conditioned_449

theorem direction_450 :
    10 = geometricCredits.getD 450 0 ∧
    0 = completedCredit 450 ∧
    18 = conditionalCredit 450 := by decide +kernel

theorem conditioned_450 (code : Nat) :
    conditionedCredit 450 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 450 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 450 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_450
#print axioms conditioned_450

theorem direction_451 :
    10 = geometricCredits.getD 451 0 ∧
    0 = completedCredit 451 ∧
    18 = conditionalCredit 451 := by decide +kernel

theorem conditioned_451 (code : Nat) :
    conditionedCredit 451 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 451 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 451 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_451
#print axioms conditioned_451

theorem direction_452 :
    10 = geometricCredits.getD 452 0 ∧
    16 = completedCredit 452 ∧
    16 = conditionalCredit 452 := by decide +kernel

theorem conditioned_452 (code : Nat) :
    conditionedCredit 452 code = 0 := by
  have hf : canon ((extensions.getD 452 []).drop 3) = [0,1,2,0,3,1] := by decide +kernel
  have hb : canon (((extensions.getD 452 []).drop 3).reverse) = [0,1,2,3,0,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_452
#print axioms conditioned_452

theorem direction_453 :
    5 = geometricCredits.getD 453 0 ∧
    0 = completedCredit 453 ∧
    16 = conditionalCredit 453 := by decide +kernel

theorem conditioned_453 (code : Nat) :
    conditionedCredit 453 code = 0 := by
  have hf : canon ((extensions.getD 453 []).drop 3) = [0,1,2,0,3,2] := by decide +kernel
  have hb : canon (((extensions.getD 453 []).drop 3).reverse) = [0,1,2,0,3,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_453
#print axioms conditioned_453

theorem direction_454 :
    10 = geometricCredits.getD 454 0 ∧
    0 = completedCredit 454 ∧
    18 = conditionalCredit 454 := by decide +kernel

theorem conditioned_454 (code : Nat) :
    conditionedCredit 454 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 454 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 454 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_454
#print axioms conditioned_454

theorem direction_455 :
    28 = geometricCredits.getD 455 0 ∧
    0 = completedCredit 455 ∧
    18 = conditionalCredit 455 := by decide +kernel

theorem conditioned_455 (code : Nat) :
    conditionedCredit 455 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 455 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 455 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_455
#print axioms conditioned_455

theorem direction_456 :
    19 = geometricCredits.getD 456 0 ∧
    0 = completedCredit 456 ∧
    18 = conditionalCredit 456 := by decide +kernel

theorem conditioned_456 (code : Nat) :
    conditionedCredit 456 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 456 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 456 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_456
#print axioms conditioned_456

theorem direction_457 :
    24 = geometricCredits.getD 457 0 ∧
    16 = completedCredit 457 ∧
    16 = conditionalCredit 457 := by decide +kernel

theorem conditioned_457 (code : Nat) :
    conditionedCredit 457 code = 0 := by
  have hf : canon ((extensions.getD 457 []).drop 3) = [0,1,2,0,3,1] := by decide +kernel
  have hb : canon (((extensions.getD 457 []).drop 3).reverse) = [0,1,2,3,0,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_457
#print axioms conditioned_457

theorem direction_458 :
    18 = geometricCredits.getD 458 0 ∧
    0 = completedCredit 458 ∧
    16 = conditionalCredit 458 := by decide +kernel

theorem conditioned_458 (code : Nat) :
    conditionedCredit 458 code = 0 := by
  have hf : canon ((extensions.getD 458 []).drop 3) = [0,1,2,0,3,2] := by decide +kernel
  have hb : canon (((extensions.getD 458 []).drop 3).reverse) = [0,1,2,0,3,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_458
#print axioms conditioned_458

theorem direction_459 :
    28 = geometricCredits.getD 459 0 ∧
    0 = completedCredit 459 ∧
    18 = conditionalCredit 459 := by decide +kernel

theorem conditioned_459 (code : Nat) :
    conditionedCredit 459 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 459 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 459 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_459
#print axioms conditioned_459

theorem direction_460 :
    0 = geometricCredits.getD 460 0 ∧
    0 = completedCredit 460 ∧
    18 = conditionalCredit 460 := by decide +kernel

theorem conditioned_460 (code : Nat) :
    conditionedCredit 460 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 460 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 460 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_460
#print axioms conditioned_460

theorem direction_461 :
    0 = geometricCredits.getD 461 0 ∧
    0 = completedCredit 461 ∧
    18 = conditionalCredit 461 := by decide +kernel

theorem conditioned_461 (code : Nat) :
    conditionedCredit 461 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 461 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 461 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_461
#print axioms conditioned_461

theorem direction_462 :
    0 = geometricCredits.getD 462 0 ∧
    0 = completedCredit 462 ∧
    18 = conditionalCredit 462 := by decide +kernel

theorem conditioned_462 (code : Nat) :
    conditionedCredit 462 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 462 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 462 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_462
#print axioms conditioned_462

theorem direction_463 :
    10 = geometricCredits.getD 463 0 ∧
    0 = completedCredit 463 ∧
    18 = conditionalCredit 463 := by decide +kernel

theorem conditioned_463 (code : Nat) :
    conditionedCredit 463 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 463 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 463 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_463
#print axioms conditioned_463

theorem direction_464 :
    10 = geometricCredits.getD 464 0 ∧
    0 = completedCredit 464 ∧
    18 = conditionalCredit 464 := by decide +kernel

theorem conditioned_464 (code : Nat) :
    conditionedCredit 464 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 464 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 464 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_464
#print axioms conditioned_464

theorem direction_465 :
    10 = geometricCredits.getD 465 0 ∧
    0 = completedCredit 465 ∧
    18 = conditionalCredit 465 := by decide +kernel

theorem conditioned_465 (code : Nat) :
    conditionedCredit 465 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 465 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 465 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_465
#print axioms conditioned_465

theorem direction_466 :
    10 = geometricCredits.getD 466 0 ∧
    16 = completedCredit 466 ∧
    16 = conditionalCredit 466 := by decide +kernel

theorem conditioned_466 (code : Nat) :
    conditionedCredit 466 code = 0 := by
  have hf : canon ((extensions.getD 466 []).drop 3) = [0,1,2,0,3,1] := by decide +kernel
  have hb : canon (((extensions.getD 466 []).drop 3).reverse) = [0,1,2,3,0,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_466
#print axioms conditioned_466

theorem direction_467 :
    5 = geometricCredits.getD 467 0 ∧
    0 = completedCredit 467 ∧
    16 = conditionalCredit 467 := by decide +kernel

theorem conditioned_467 (code : Nat) :
    conditionedCredit 467 code = 0 := by
  have hf : canon ((extensions.getD 467 []).drop 3) = [0,1,2,0,3,2] := by decide +kernel
  have hb : canon (((extensions.getD 467 []).drop 3).reverse) = [0,1,2,0,3,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_467
#print axioms conditioned_467

theorem direction_468 :
    10 = geometricCredits.getD 468 0 ∧
    0 = completedCredit 468 ∧
    18 = conditionalCredit 468 := by decide +kernel

theorem conditioned_468 (code : Nat) :
    conditionedCredit 468 code = (if code%7776 = 7106 then 96 else 0) := by
  have hf : canon ((extensions.getD 468 []).drop 3) = [0,1,2,0,3,4] := by decide +kernel
  have hb : canon (((extensions.getD 468 []).drop 3).reverse) = [0,1,2,3,4,2] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_468
#print axioms conditioned_468

theorem direction_469 :
    0 = geometricCredits.getD 469 0 ∧
    12 = completedCredit 469 ∧
    16 = conditionalCredit 469 := by decide +kernel

theorem conditioned_469 (code : Nat) :
    conditionedCredit 469 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 469 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 469 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_469
#print axioms conditioned_469

theorem direction_470 :
    0 = geometricCredits.getD 470 0 ∧
    12 = completedCredit 470 ∧
    16 = conditionalCredit 470 := by decide +kernel

theorem conditioned_470 (code : Nat) :
    conditionedCredit 470 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 470 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 470 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_470
#print axioms conditioned_470

theorem direction_471 :
    0 = geometricCredits.getD 471 0 ∧
    0 = completedCredit 471 ∧
    16 = conditionalCredit 471 := by decide +kernel

theorem conditioned_471 (code : Nat) :
    conditionedCredit 471 code = 0 := by
  have hf : canon ((extensions.getD 471 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 471 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_471
#print axioms conditioned_471

theorem direction_472 :
    0 = geometricCredits.getD 472 0 ∧
    16 = completedCredit 472 ∧
    16 = conditionalCredit 472 := by decide +kernel

theorem conditioned_472 (code : Nat) :
    conditionedCredit 472 code = 0 := by
  have hf : canon ((extensions.getD 472 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 472 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_472
#print axioms conditioned_472

theorem direction_473 :
    0 = geometricCredits.getD 473 0 ∧
    0 = completedCredit 473 ∧
    18 = conditionalCredit 473 := by decide +kernel

theorem conditioned_473 (code : Nat) :
    conditionedCredit 473 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 473 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 473 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_473
#print axioms conditioned_473

theorem direction_474 :
    0 = geometricCredits.getD 474 0 ∧
    12 = completedCredit 474 ∧
    16 = conditionalCredit 474 := by decide +kernel

theorem conditioned_474 (code : Nat) :
    conditionedCredit 474 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 474 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 474 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_474
#print axioms conditioned_474

theorem direction_475 :
    0 = geometricCredits.getD 475 0 ∧
    12 = completedCredit 475 ∧
    16 = conditionalCredit 475 := by decide +kernel

theorem conditioned_475 (code : Nat) :
    conditionedCredit 475 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 475 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 475 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_475
#print axioms conditioned_475

theorem direction_476 :
    0 = geometricCredits.getD 476 0 ∧
    12 = completedCredit 476 ∧
    16 = conditionalCredit 476 := by decide +kernel

theorem conditioned_476 (code : Nat) :
    conditionedCredit 476 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 476 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 476 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_476
#print axioms conditioned_476

theorem direction_477 :
    0 = geometricCredits.getD 477 0 ∧
    0 = completedCredit 477 ∧
    16 = conditionalCredit 477 := by decide +kernel

theorem conditioned_477 (code : Nat) :
    conditionedCredit 477 code = 0 := by
  have hf : canon ((extensions.getD 477 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 477 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_477
#print axioms conditioned_477

theorem direction_478 :
    0 = geometricCredits.getD 478 0 ∧
    16 = completedCredit 478 ∧
    16 = conditionalCredit 478 := by decide +kernel

theorem conditioned_478 (code : Nat) :
    conditionedCredit 478 code = 0 := by
  have hf : canon ((extensions.getD 478 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 478 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_478
#print axioms conditioned_478

theorem direction_479 :
    0 = geometricCredits.getD 479 0 ∧
    0 = completedCredit 479 ∧
    18 = conditionalCredit 479 := by decide +kernel

theorem conditioned_479 (code : Nat) :
    conditionedCredit 479 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 479 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 479 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_479
#print axioms conditioned_479

theorem direction_480 :
    0 = geometricCredits.getD 480 0 ∧
    12 = completedCredit 480 ∧
    16 = conditionalCredit 480 := by decide +kernel

theorem conditioned_480 (code : Nat) :
    conditionedCredit 480 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 480 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 480 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_480
#print axioms conditioned_480

theorem direction_481 :
    0 = geometricCredits.getD 481 0 ∧
    12 = completedCredit 481 ∧
    16 = conditionalCredit 481 := by decide +kernel

theorem conditioned_481 (code : Nat) :
    conditionedCredit 481 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 481 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 481 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_481
#print axioms conditioned_481

theorem direction_482 :
    0 = geometricCredits.getD 482 0 ∧
    12 = completedCredit 482 ∧
    16 = conditionalCredit 482 := by decide +kernel

theorem conditioned_482 (code : Nat) :
    conditionedCredit 482 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 482 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 482 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_482
#print axioms conditioned_482

theorem direction_483 :
    0 = geometricCredits.getD 483 0 ∧
    0 = completedCredit 483 ∧
    16 = conditionalCredit 483 := by decide +kernel

theorem conditioned_483 (code : Nat) :
    conditionedCredit 483 code = 0 := by
  have hf : canon ((extensions.getD 483 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 483 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_483
#print axioms conditioned_483

theorem direction_484 :
    0 = geometricCredits.getD 484 0 ∧
    16 = completedCredit 484 ∧
    16 = conditionalCredit 484 := by decide +kernel

theorem conditioned_484 (code : Nat) :
    conditionedCredit 484 code = 0 := by
  have hf : canon ((extensions.getD 484 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 484 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_484
#print axioms conditioned_484

theorem direction_485 :
    0 = geometricCredits.getD 485 0 ∧
    0 = completedCredit 485 ∧
    18 = conditionalCredit 485 := by decide +kernel

theorem conditioned_485 (code : Nat) :
    conditionedCredit 485 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 485 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 485 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_485
#print axioms conditioned_485

theorem direction_486 :
    0 = geometricCredits.getD 486 0 ∧
    12 = completedCredit 486 ∧
    16 = conditionalCredit 486 := by decide +kernel

theorem conditioned_486 (code : Nat) :
    conditionedCredit 486 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 486 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 486 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_486
#print axioms conditioned_486

theorem direction_487 :
    18 = geometricCredits.getD 487 0 ∧
    16 = completedCredit 487 ∧
    16 = conditionalCredit 487 := by decide +kernel

theorem conditioned_487 (code : Nat) :
    conditionedCredit 487 code = 0 := by
  have hf : canon ((extensions.getD 487 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 487 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_487
#print axioms conditioned_487

theorem direction_488 :
    18 = geometricCredits.getD 488 0 ∧
    16 = completedCredit 488 ∧
    16 = conditionalCredit 488 := by decide +kernel

theorem conditioned_488 (code : Nat) :
    conditionedCredit 488 code = 0 := by
  have hf : canon ((extensions.getD 488 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 488 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_488
#print axioms conditioned_488

theorem direction_489 :
    18 = geometricCredits.getD 489 0 ∧
    16 = completedCredit 489 ∧
    16 = conditionalCredit 489 := by decide +kernel

theorem conditioned_489 (code : Nat) :
    conditionedCredit 489 code = 0 := by
  have hf : canon ((extensions.getD 489 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 489 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_489
#print axioms conditioned_489

theorem direction_490 :
    6 = geometricCredits.getD 490 0 ∧
    0 = completedCredit 490 ∧
    16 = conditionalCredit 490 := by decide +kernel

theorem conditioned_490 (code : Nat) :
    conditionedCredit 490 code = 0 := by
  have hf : canon ((extensions.getD 490 []).drop 3) = [0,1,2,3,0,1] := by decide +kernel
  have hb : canon (((extensions.getD 490 []).drop 3).reverse) = [0,1,2,3,0,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_490
#print axioms conditioned_490

theorem direction_491 :
    12 = geometricCredits.getD 491 0 ∧
    16 = completedCredit 491 ∧
    16 = conditionalCredit 491 := by decide +kernel

theorem conditioned_491 (code : Nat) :
    conditionedCredit 491 code = 0 := by
  have hf : canon ((extensions.getD 491 []).drop 3) = [0,1,2,3,0,2] := by decide +kernel
  have hb : canon (((extensions.getD 491 []).drop 3).reverse) = [0,1,2,0,3,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_491
#print axioms conditioned_491

theorem direction_492 :
    18 = geometricCredits.getD 492 0 ∧
    16 = completedCredit 492 ∧
    16 = conditionalCredit 492 := by decide +kernel

theorem conditioned_492 (code : Nat) :
    conditionedCredit 492 code = 0 := by
  have hf : canon ((extensions.getD 492 []).drop 3) = [0,1,2,3,0,4] := by decide +kernel
  have hb : canon (((extensions.getD 492 []).drop 3).reverse) = [0,1,2,3,4,1] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_492
#print axioms conditioned_492

theorem direction_493 :
    5 = geometricCredits.getD 493 0 ∧
    16 = completedCredit 493 ∧
    16 = conditionalCredit 493 := by decide +kernel

theorem conditioned_493 (code : Nat) :
    conditionedCredit 493 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 493 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 493 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_493
#print axioms conditioned_493

theorem direction_494 :
    5 = geometricCredits.getD 494 0 ∧
    16 = completedCredit 494 ∧
    16 = conditionalCredit 494 := by decide +kernel

theorem conditioned_494 (code : Nat) :
    conditionedCredit 494 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 494 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 494 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_494
#print axioms conditioned_494

theorem direction_495 :
    5 = geometricCredits.getD 495 0 ∧
    16 = completedCredit 495 ∧
    16 = conditionalCredit 495 := by decide +kernel

theorem conditioned_495 (code : Nat) :
    conditionedCredit 495 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 495 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 495 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_495
#print axioms conditioned_495

theorem direction_496 :
    0 = geometricCredits.getD 496 0 ∧
    12 = completedCredit 496 ∧
    12 = conditionalCredit 496 := by decide +kernel

theorem conditioned_496 (code : Nat) :
    conditionedCredit 496 code = 0 := by
  have hf : canon ((extensions.getD 496 []).drop 3) = [0,1,2,3,1,0] := by decide +kernel
  have hb : canon (((extensions.getD 496 []).drop 3).reverse) = [0,1,2,3,1,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_496
#print axioms conditioned_496

theorem direction_497 :
    5 = geometricCredits.getD 497 0 ∧
    16 = completedCredit 497 ∧
    16 = conditionalCredit 497 := by decide +kernel

theorem conditioned_497 (code : Nat) :
    conditionedCredit 497 code = (if code%7776 = 3130 ∨ code%7776 = 6350 then 48 else 0) := by
  have hf : canon ((extensions.getD 497 []).drop 3) = [0,1,2,3,1,4] := by decide +kernel
  have hb : canon (((extensions.getD 497 []).drop 3).reverse) = [0,1,2,3,1,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_497
#print axioms conditioned_497

theorem direction_498 :
    0 = geometricCredits.getD 498 0 ∧
    12 = completedCredit 498 ∧
    16 = conditionalCredit 498 := by decide +kernel

theorem conditioned_498 (code : Nat) :
    conditionedCredit 498 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 498 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 498 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_498
#print axioms conditioned_498

theorem direction_499 :
    0 = geometricCredits.getD 499 0 ∧
    12 = completedCredit 499 ∧
    16 = conditionalCredit 499 := by decide +kernel

theorem conditioned_499 (code : Nat) :
    conditionedCredit 499 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 499 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 499 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_499
#print axioms conditioned_499

theorem direction_500 :
    0 = geometricCredits.getD 500 0 ∧
    12 = completedCredit 500 ∧
    16 = conditionalCredit 500 := by decide +kernel

theorem conditioned_500 (code : Nat) :
    conditionedCredit 500 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 500 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 500 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_500
#print axioms conditioned_500

theorem direction_501 :
    0 = geometricCredits.getD 501 0 ∧
    0 = completedCredit 501 ∧
    16 = conditionalCredit 501 := by decide +kernel

theorem conditioned_501 (code : Nat) :
    conditionedCredit 501 code = 0 := by
  have hf : canon ((extensions.getD 501 []).drop 3) = [0,1,2,3,4,0] := by decide +kernel
  have hb : canon (((extensions.getD 501 []).drop 3).reverse) = [0,1,2,3,4,0] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_501
#print axioms conditioned_501

theorem direction_502 :
    0 = geometricCredits.getD 502 0 ∧
    16 = completedCredit 502 ∧
    16 = conditionalCredit 502 := by decide +kernel

theorem conditioned_502 (code : Nat) :
    conditionedCredit 502 code = 0 := by
  have hf : canon ((extensions.getD 502 []).drop 3) = [0,1,2,3,4,1] := by decide +kernel
  have hb : canon (((extensions.getD 502 []).drop 3).reverse) = [0,1,2,3,0,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_502
#print axioms conditioned_502

theorem direction_503 :
    0 = geometricCredits.getD 503 0 ∧
    0 = completedCredit 503 ∧
    18 = conditionalCredit 503 := by decide +kernel

theorem conditioned_503 (code : Nat) :
    conditionedCredit 503 code = (if code%7776 = 3221 then 96 else 0) := by
  have hf : canon ((extensions.getD 503 []).drop 3) = [0,1,2,3,4,2] := by decide +kernel
  have hb : canon (((extensions.getD 503 []).drop 3).reverse) = [0,1,2,0,3,4] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_503
#print axioms conditioned_503

theorem direction_504 :
    0 = geometricCredits.getD 504 0 ∧
    12 = completedCredit 504 ∧
    16 = conditionalCredit 504 := by decide +kernel

theorem conditioned_504 (code : Nat) :
    conditionedCredit 504 code = max (if code%7776 = 3725 ∨ code%7776 = 6980 then 96 else 0) (max (if code%7776 = 5021 ∨ code%7776 = 6981 then 96 else 0) ((if code%7776 = 4871 ∨ code%7776 = 6831 then 120 else 0))) := by
  have hf : canon ((extensions.getD 504 []).drop 3) = [0,1,2,3,4,5] := by decide +kernel
  have hb : canon (((extensions.getD 504 []).drop 3).reverse) = [0,1,2,3,4,5] := by decide +kernel
  simp only [conditionedCredit, ruleCredit, hf, hb]
  norm_num [encodeCounts]

#print axioms direction_504
#print axioms conditioned_504

end Snake9.Context101
