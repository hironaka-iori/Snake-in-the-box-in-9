import E112166Semantics
import B112E166Inputs
namespace Snake9.Regrowth.E112166
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause449 (q : Nat → Bool) : valuationOf q 1331 = false ∨ valuationOf q 1380 = false ∨ valuationOf q 1399 = true := by
  have hs : count1394 q = (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) + (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (l₂ := [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1331)) (literal (valuationOf q) (1380)) (literal (valuationOf q) (1399)) (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) (count1394 q) 5 1 (meaning1331 q) (meaning1380 q) (meaning1399 q) hs
  change valuationOf q 1331 = false ∨ valuationOf q 1380 = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 1331 = false ∨ valuation q 1380 = false ∨ valuation q 1399 = true := counterClause449 (baseVal q)

theorem counterClause450 (q : Nat → Bool) : valuationOf q 1331 = false ∨ valuationOf q 1381 = false ∨ valuationOf q 1400 = true := by
  have hs : count1394 q = (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) + (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (l₂ := [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1331)) (literal (valuationOf q) (1381)) (literal (valuationOf q) (1400)) (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) (count1394 q) 5 2 (meaning1331 q) (meaning1381 q) (meaning1400 q) hs
  change valuationOf q 1331 = false ∨ valuationOf q 1381 = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 1331 = false ∨ valuation q 1381 = false ∨ valuation q 1400 = true := counterClause450 (baseVal q)

theorem counterClause451 (q : Nat → Bool) : valuationOf q 1331 = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1401 = true := by
  have hs : count1394 q = (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) + (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (l₂ := [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1331)) (literal (valuationOf q) (1382)) (literal (valuationOf q) (1401)) (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) (count1394 q) 5 3 (meaning1331 q) (meaning1382 q) (meaning1401 q) hs
  change valuationOf q 1331 = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 1331 = false ∨ valuation q 1382 = false ∨ valuation q 1401 = true := counterClause451 (baseVal q)

theorem counterClause452 (q : Nat → Bool) : valuationOf q 1331 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1402 = true := by
  have hs : count1394 q = (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) + (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (l₂ := [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1331)) (literal (valuationOf q) (1383)) (literal (valuationOf q) (1402)) (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) (count1394 q) 5 4 (meaning1331 q) (meaning1383 q) (meaning1402 q) hs
  change valuationOf q 1331 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 1331 = false ∨ valuation q 1383 = false ∨ valuation q 1402 = true := counterClause452 (baseVal q)

theorem counterClause453 (q : Nat → Bool) : valuationOf q 1332 = false ∨ valuationOf q 1380 = false ∨ valuationOf q 1400 = true := by
  have hs : count1394 q = (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) + (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (l₂ := [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1332)) (literal (valuationOf q) (1380)) (literal (valuationOf q) (1400)) (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) (count1394 q) 6 1 (meaning1332 q) (meaning1380 q) (meaning1400 q) hs
  change valuationOf q 1332 = false ∨ valuationOf q 1380 = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 1332 = false ∨ valuation q 1380 = false ∨ valuation q 1400 = true := counterClause453 (baseVal q)

theorem counterClause454 (q : Nat → Bool) : valuationOf q 1332 = false ∨ valuationOf q 1381 = false ∨ valuationOf q 1401 = true := by
  have hs : count1394 q = (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) + (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (l₂ := [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1332)) (literal (valuationOf q) (1381)) (literal (valuationOf q) (1401)) (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) (count1394 q) 6 2 (meaning1332 q) (meaning1381 q) (meaning1401 q) hs
  change valuationOf q 1332 = false ∨ valuationOf q 1381 = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 1332 = false ∨ valuation q 1381 = false ∨ valuation q 1401 = true := counterClause454 (baseVal q)

theorem counterClause455 (q : Nat → Bool) : valuationOf q 1333 = false ∨ valuationOf q 1380 = false ∨ valuationOf q 1401 = true := by
  have hs : count1394 q = (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) + (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (l₂ := [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1333)) (literal (valuationOf q) (1380)) (literal (valuationOf q) (1401)) (countLit q [-2, -3, -5, -7, -8, -11, -13, -14, -17, -19, -21, -22, -24]) (countLit q [-25, -28, -29, -32, -34, -36, -37, -39, -40, -44, -45, -47, -50, -52]) (count1394 q) 7 1 (meaning1333 q) (meaning1380 q) (meaning1401 q) hs
  change valuationOf q 1333 = false ∨ valuationOf q 1380 = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 1333 = false ∨ valuation q 1380 = false ∨ valuation q 1401 = true := counterClause455 (baseVal q)

theorem counterClause456 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1409 = true := by
  have hs : count1409 q = (countLit q [-56]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-58])
  have hm := merge_right (literal (valuationOf q) (-58)) (literal (valuationOf q) (1409)) (countLit q [-56]) (countLit q [-58]) (count1409 q) 1 (meaningNeg58 q) (meaning1409 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1409 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1409 = true := counterClause456 (baseVal q)

theorem counterClause457 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1409 = true := by
  have hs : count1409 q = (countLit q [-56]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-58])
  have hm := merge_left (literal (valuationOf q) (-56)) (literal (valuationOf q) (1409)) (countLit q [-56]) (countLit q [-58]) (count1409 q) 1 (meaningNeg56 q) (meaning1409 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1409 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1409 = true := counterClause457 (baseVal q)

theorem counterClause458 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 58 = true ∨ valuationOf q 1410 = true := by
  have hs : count1409 q = (countLit q [-56]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-58])
  have hm := merge_two (literal (valuationOf q) (-56)) (literal (valuationOf q) (-58)) (literal (valuationOf q) (1410)) (countLit q [-56]) (countLit q [-58]) (count1409 q) 1 1 (meaningNeg56 q) (meaningNeg58 q) (meaning1410 q) hs
  change (! (valuationOf q 56)) = false ∨ (! (valuationOf q 58)) = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 58 = true ∨ valuation q 1410 = true := counterClause458 (baseVal q)

theorem counterClause459 (q : Nat → Bool) : valuationOf q 1409 = false ∨ valuationOf q 1411 = true := by
  have hs : count1411 q = (countLit q [-53]) + (countLit q [-56, -58]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-56, -58])
  have hm := merge_right (literal (valuationOf q) (1409)) (literal (valuationOf q) (1411)) (countLit q [-53]) (countLit q [-56, -58]) (count1411 q) 1 (meaning1409 q) (meaning1411 q) hs
  change valuationOf q 1409 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 1409 = false ∨ valuation q 1411 = true := counterClause459 (baseVal q)

theorem counterClause460 (q : Nat → Bool) : valuationOf q 1410 = false ∨ valuationOf q 1412 = true := by
  have hs : count1411 q = (countLit q [-53]) + (countLit q [-56, -58]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-56, -58])
  have hm := merge_right (literal (valuationOf q) (1410)) (literal (valuationOf q) (1412)) (countLit q [-53]) (countLit q [-56, -58]) (count1411 q) 2 (meaning1410 q) (meaning1412 q) hs
  change valuationOf q 1410 = false ∨ valuationOf q 1412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 1410 = false ∨ valuation q 1412 = true := counterClause460 (baseVal q)

theorem counterClause461 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 1411 = true := by
  have hs : count1411 q = (countLit q [-53]) + (countLit q [-56, -58]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-56, -58])
  have hm := merge_left (literal (valuationOf q) (-53)) (literal (valuationOf q) (1411)) (countLit q [-53]) (countLit q [-56, -58]) (count1411 q) 1 (meaningNeg53 q) (meaning1411 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 1411 = true := counterClause461 (baseVal q)

theorem counterClause462 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 1409 = false ∨ valuationOf q 1412 = true := by
  have hs : count1411 q = (countLit q [-53]) + (countLit q [-56, -58]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-56, -58])
  have hm := merge_two (literal (valuationOf q) (-53)) (literal (valuationOf q) (1409)) (literal (valuationOf q) (1412)) (countLit q [-53]) (countLit q [-56, -58]) (count1411 q) 1 1 (meaningNeg53 q) (meaning1409 q) (meaning1412 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 1409 = false ∨ valuationOf q 1412 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 1409 = false ∨ valuation q 1412 = true := counterClause462 (baseVal q)

theorem counterClause463 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 1410 = false ∨ valuationOf q 1413 = true := by
  have hs : count1411 q = (countLit q [-53]) + (countLit q [-56, -58]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-56, -58])
  have hm := merge_two (literal (valuationOf q) (-53)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1413)) (countLit q [-53]) (countLit q [-56, -58]) (count1411 q) 1 2 (meaningNeg53 q) (meaning1410 q) (meaning1413 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1413 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 1410 = false ∨ valuation q 1413 = true := counterClause463 (baseVal q)

theorem counterClause464 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 1414 = true := by
  have hs : count1414 q = (countLit q [-59]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-62])
  have hm := merge_right (literal (valuationOf q) (-62)) (literal (valuationOf q) (1414)) (countLit q [-59]) (countLit q [-62]) (count1414 q) 1 (meaningNeg62 q) (meaning1414 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 1414 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1414 = true := counterClause464 (baseVal q)

theorem counterClause465 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1414 = true := by
  have hs : count1414 q = (countLit q [-59]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-62])
  have hm := merge_left (literal (valuationOf q) (-59)) (literal (valuationOf q) (1414)) (countLit q [-59]) (countLit q [-62]) (count1414 q) 1 (meaningNeg59 q) (meaning1414 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1414 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1414 = true := counterClause465 (baseVal q)

theorem counterClause466 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 62 = true ∨ valuationOf q 1415 = true := by
  have hs : count1414 q = (countLit q [-59]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-62])
  have hm := merge_two (literal (valuationOf q) (-59)) (literal (valuationOf q) (-62)) (literal (valuationOf q) (1415)) (countLit q [-59]) (countLit q [-62]) (count1414 q) 1 1 (meaningNeg59 q) (meaningNeg62 q) (meaning1415 q) hs
  change (! (valuationOf q 59)) = false ∨ (! (valuationOf q 62)) = false ∨ valuationOf q 1415 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 62 = true ∨ valuation q 1415 = true := counterClause466 (baseVal q)

theorem counterClause467 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1416 = true := by
  have hs : count1416 q = (countLit q [-63]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-66])
  have hm := merge_right (literal (valuationOf q) (-66)) (literal (valuationOf q) (1416)) (countLit q [-63]) (countLit q [-66]) (count1416 q) 1 (meaningNeg66 q) (meaning1416 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1416 = true := counterClause467 (baseVal q)

theorem counterClause468 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1416 = true := by
  have hs : count1416 q = (countLit q [-63]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-66])
  have hm := merge_left (literal (valuationOf q) (-63)) (literal (valuationOf q) (1416)) (countLit q [-63]) (countLit q [-66]) (count1416 q) 1 (meaningNeg63 q) (meaning1416 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1416 = true := counterClause468 (baseVal q)

theorem counterClause469 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 66 = true ∨ valuationOf q 1417 = true := by
  have hs : count1416 q = (countLit q [-63]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-66])
  have hm := merge_two (literal (valuationOf q) (-63)) (literal (valuationOf q) (-66)) (literal (valuationOf q) (1417)) (countLit q [-63]) (countLit q [-66]) (count1416 q) 1 1 (meaningNeg63 q) (meaningNeg66 q) (meaning1417 q) hs
  change (! (valuationOf q 63)) = false ∨ (! (valuationOf q 66)) = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 66 = true ∨ valuation q 1417 = true := counterClause469 (baseVal q)

theorem counterClause470 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1418 = true := by
  have hs : count1418 q = (countLit q [-59, -62]) + (countLit q [-63, -66]) := List.countP_append (p := literal q) (l₁ := [-59, -62]) (l₂ := [-63, -66])
  have hm := merge_right (literal (valuationOf q) (1416)) (literal (valuationOf q) (1418)) (countLit q [-59, -62]) (countLit q [-63, -66]) (count1418 q) 1 (meaning1416 q) (meaning1418 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1418 = true := counterClause470 (baseVal q)

theorem counterClause471 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1419 = true := by
  have hs : count1418 q = (countLit q [-59, -62]) + (countLit q [-63, -66]) := List.countP_append (p := literal q) (l₁ := [-59, -62]) (l₂ := [-63, -66])
  have hm := merge_right (literal (valuationOf q) (1417)) (literal (valuationOf q) (1419)) (countLit q [-59, -62]) (countLit q [-63, -66]) (count1418 q) 2 (meaning1417 q) (meaning1419 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1419 = true := counterClause471 (baseVal q)

theorem counterClause472 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1418 = true := by
  have hs : count1418 q = (countLit q [-59, -62]) + (countLit q [-63, -66]) := List.countP_append (p := literal q) (l₁ := [-59, -62]) (l₂ := [-63, -66])
  have hm := merge_left (literal (valuationOf q) (1414)) (literal (valuationOf q) (1418)) (countLit q [-59, -62]) (countLit q [-63, -66]) (count1418 q) 1 (meaning1414 q) (meaning1418 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1418 = true := counterClause472 (baseVal q)

theorem counterClause473 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1416 = false ∨ valuationOf q 1419 = true := by
  have hs : count1418 q = (countLit q [-59, -62]) + (countLit q [-63, -66]) := List.countP_append (p := literal q) (l₁ := [-59, -62]) (l₂ := [-63, -66])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1416)) (literal (valuationOf q) (1419)) (countLit q [-59, -62]) (countLit q [-63, -66]) (count1418 q) 1 1 (meaning1414 q) (meaning1416 q) (meaning1419 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1416 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1416 = false ∨ valuation q 1419 = true := counterClause473 (baseVal q)

theorem counterClause474 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1420 = true := by
  have hs : count1418 q = (countLit q [-59, -62]) + (countLit q [-63, -66]) := List.countP_append (p := literal q) (l₁ := [-59, -62]) (l₂ := [-63, -66])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1417)) (literal (valuationOf q) (1420)) (countLit q [-59, -62]) (countLit q [-63, -66]) (count1418 q) 1 2 (meaning1414 q) (meaning1417 q) (meaning1420 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1417 = false ∨ valuation q 1420 = true := counterClause474 (baseVal q)

theorem counterClause475 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1419 = true := by
  have hs : count1418 q = (countLit q [-59, -62]) + (countLit q [-63, -66]) := List.countP_append (p := literal q) (l₁ := [-59, -62]) (l₂ := [-63, -66])
  have hm := merge_left (literal (valuationOf q) (1415)) (literal (valuationOf q) (1419)) (countLit q [-59, -62]) (countLit q [-63, -66]) (count1418 q) 2 (meaning1415 q) (meaning1419 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1419 = true := counterClause475 (baseVal q)

theorem counterClause476 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1416 = false ∨ valuationOf q 1420 = true := by
  have hs : count1418 q = (countLit q [-59, -62]) + (countLit q [-63, -66]) := List.countP_append (p := literal q) (l₁ := [-59, -62]) (l₂ := [-63, -66])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1416)) (literal (valuationOf q) (1420)) (countLit q [-59, -62]) (countLit q [-63, -66]) (count1418 q) 2 1 (meaning1415 q) (meaning1416 q) (meaning1420 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1416 = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1416 = false ∨ valuation q 1420 = true := counterClause476 (baseVal q)

theorem counterClause477 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1422 = true := by
  have hs : count1422 q = (countLit q [-53, -56, -58]) + (countLit q [-59, -62, -63, -66]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58]) (l₂ := [-59, -62, -63, -66])
  have hm := merge_right (literal (valuationOf q) (1418)) (literal (valuationOf q) (1422)) (countLit q [-53, -56, -58]) (countLit q [-59, -62, -63, -66]) (count1422 q) 1 (meaning1418 q) (meaning1422 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1422 = true := counterClause477 (baseVal q)

theorem counterClause478 (q : Nat → Bool) : valuationOf q 1419 = false ∨ valuationOf q 1423 = true := by
  have hs : count1422 q = (countLit q [-53, -56, -58]) + (countLit q [-59, -62, -63, -66]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58]) (l₂ := [-59, -62, -63, -66])
  have hm := merge_right (literal (valuationOf q) (1419)) (literal (valuationOf q) (1423)) (countLit q [-53, -56, -58]) (countLit q [-59, -62, -63, -66]) (count1422 q) 2 (meaning1419 q) (meaning1423 q) hs
  change valuationOf q 1419 = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 1419 = false ∨ valuation q 1423 = true := counterClause478 (baseVal q)

theorem counterClause479 (q : Nat → Bool) : valuationOf q 1420 = false ∨ valuationOf q 1424 = true := by
  have hs : count1422 q = (countLit q [-53, -56, -58]) + (countLit q [-59, -62, -63, -66]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58]) (l₂ := [-59, -62, -63, -66])
  have hm := merge_right (literal (valuationOf q) (1420)) (literal (valuationOf q) (1424)) (countLit q [-53, -56, -58]) (countLit q [-59, -62, -63, -66]) (count1422 q) 3 (meaning1420 q) (meaning1424 q) hs
  change valuationOf q 1420 = false ∨ valuationOf q 1424 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 1420 = false ∨ valuation q 1424 = true := counterClause479 (baseVal q)

theorem counterClause480 (q : Nat → Bool) : valuationOf q 1411 = false ∨ valuationOf q 1422 = true := by
  have hs : count1422 q = (countLit q [-53, -56, -58]) + (countLit q [-59, -62, -63, -66]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58]) (l₂ := [-59, -62, -63, -66])
  have hm := merge_left (literal (valuationOf q) (1411)) (literal (valuationOf q) (1422)) (countLit q [-53, -56, -58]) (countLit q [-59, -62, -63, -66]) (count1422 q) 1 (meaning1411 q) (meaning1422 q) hs
  change valuationOf q 1411 = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 1411 = false ∨ valuation q 1422 = true := counterClause480 (baseVal q)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E166.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112166
