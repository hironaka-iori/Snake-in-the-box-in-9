import E112058Semantics
import B112E058Inputs
namespace Snake9.Regrowth.E112058
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause417 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1470 = true := by
  have hs : count1468 q = (countLit q [-33, -34, -35]) + (countLit q [-37, -39, -42, -43]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -35]) (l₂ := [-37, -39, -42, -43])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1464)) (literal (valuationOf q) (1470)) (countLit q [-33, -34, -35]) (countLit q [-37, -39, -42, -43]) (count1468 q) 2 1 (meaning1458 q) (meaning1464 q) (meaning1470 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1464 = false ∨ valuation q 1470 = true := counterClause417 (baseVal q)

theorem counterClause418 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1471 = true := by
  have hs : count1468 q = (countLit q [-33, -34, -35]) + (countLit q [-37, -39, -42, -43]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -35]) (l₂ := [-37, -39, -42, -43])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1465)) (literal (valuationOf q) (1471)) (countLit q [-33, -34, -35]) (countLit q [-37, -39, -42, -43]) (count1468 q) 2 2 (meaning1458 q) (meaning1465 q) (meaning1471 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1465 = false ∨ valuation q 1471 = true := counterClause418 (baseVal q)

theorem counterClause419 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1472 = true := by
  have hs : count1468 q = (countLit q [-33, -34, -35]) + (countLit q [-37, -39, -42, -43]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -35]) (l₂ := [-37, -39, -42, -43])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1466)) (literal (valuationOf q) (1472)) (countLit q [-33, -34, -35]) (countLit q [-37, -39, -42, -43]) (count1468 q) 2 3 (meaning1458 q) (meaning1466 q) (meaning1472 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1466 = false ∨ valuation q 1472 = true := counterClause419 (baseVal q)

theorem counterClause420 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1471 = true := by
  have hs : count1468 q = (countLit q [-33, -34, -35]) + (countLit q [-37, -39, -42, -43]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -35]) (l₂ := [-37, -39, -42, -43])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1464)) (literal (valuationOf q) (1471)) (countLit q [-33, -34, -35]) (countLit q [-37, -39, -42, -43]) (count1468 q) 3 1 (meaning1459 q) (meaning1464 q) (meaning1471 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1464 = false ∨ valuation q 1471 = true := counterClause420 (baseVal q)

theorem counterClause421 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1472 = true := by
  have hs : count1468 q = (countLit q [-33, -34, -35]) + (countLit q [-37, -39, -42, -43]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -35]) (l₂ := [-37, -39, -42, -43])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1465)) (literal (valuationOf q) (1472)) (countLit q [-33, -34, -35]) (countLit q [-37, -39, -42, -43]) (count1468 q) 3 2 (meaning1459 q) (meaning1465 q) (meaning1472 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1465 = false ∨ valuation q 1472 = true := counterClause421 (baseVal q)

theorem counterClause422 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 1475 = true := by
  have hs : count1475 q = (countLit q [-48]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-49])
  have hm := merge_right (literal (valuationOf q) (-49)) (literal (valuationOf q) (1475)) (countLit q [-48]) (countLit q [-49]) (count1475 q) 1 (meaningNeg49 q) (meaning1475 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 1475 = true := counterClause422 (baseVal q)

theorem counterClause423 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 1475 = true := by
  have hs : count1475 q = (countLit q [-48]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-49])
  have hm := merge_left (literal (valuationOf q) (-48)) (literal (valuationOf q) (1475)) (countLit q [-48]) (countLit q [-49]) (count1475 q) 1 (meaningNeg48 q) (meaning1475 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 1475 = true := counterClause423 (baseVal q)

theorem counterClause424 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 49 = true ∨ valuationOf q 1476 = true := by
  have hs : count1475 q = (countLit q [-48]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-49])
  have hm := merge_two (literal (valuationOf q) (-48)) (literal (valuationOf q) (-49)) (literal (valuationOf q) (1476)) (countLit q [-48]) (countLit q [-49]) (count1475 q) 1 1 (meaningNeg48 q) (meaningNeg49 q) (meaning1476 q) hs
  change (! (valuationOf q 48)) = false ∨ (! (valuationOf q 49)) = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 49 = true ∨ valuation q 1476 = true := counterClause424 (baseVal q)

theorem counterClause425 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1477 = true := by
  have hs : count1477 q = (countLit q [-46]) + (countLit q [-48, -49]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-48, -49])
  have hm := merge_right (literal (valuationOf q) (1475)) (literal (valuationOf q) (1477)) (countLit q [-46]) (countLit q [-48, -49]) (count1477 q) 1 (meaning1475 q) (meaning1477 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1477 = true := counterClause425 (baseVal q)

theorem counterClause426 (q : Nat → Bool) : valuationOf q 1476 = false ∨ valuationOf q 1478 = true := by
  have hs : count1477 q = (countLit q [-46]) + (countLit q [-48, -49]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-48, -49])
  have hm := merge_right (literal (valuationOf q) (1476)) (literal (valuationOf q) (1478)) (countLit q [-46]) (countLit q [-48, -49]) (count1477 q) 2 (meaning1476 q) (meaning1478 q) hs
  change valuationOf q 1476 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1478 = true := counterClause426 (baseVal q)

theorem counterClause427 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1477 = true := by
  have hs : count1477 q = (countLit q [-46]) + (countLit q [-48, -49]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-48, -49])
  have hm := merge_left (literal (valuationOf q) (-46)) (literal (valuationOf q) (1477)) (countLit q [-46]) (countLit q [-48, -49]) (count1477 q) 1 (meaningNeg46 q) (meaning1477 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1477 = true := counterClause427 (baseVal q)

theorem counterClause428 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1475 = false ∨ valuationOf q 1478 = true := by
  have hs : count1477 q = (countLit q [-46]) + (countLit q [-48, -49]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-48, -49])
  have hm := merge_two (literal (valuationOf q) (-46)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1478)) (countLit q [-46]) (countLit q [-48, -49]) (count1477 q) 1 1 (meaningNeg46 q) (meaning1475 q) (meaning1478 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1475 = false ∨ valuation q 1478 = true := counterClause428 (baseVal q)

theorem counterClause429 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1476 = false ∨ valuationOf q 1479 = true := by
  have hs : count1477 q = (countLit q [-46]) + (countLit q [-48, -49]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-48, -49])
  have hm := merge_two (literal (valuationOf q) (-46)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1479)) (countLit q [-46]) (countLit q [-48, -49]) (count1477 q) 1 2 (meaningNeg46 q) (meaning1476 q) (meaning1479 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1476 = false ∨ valuation q 1479 = true := counterClause429 (baseVal q)

theorem counterClause430 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1480 = true := by
  have hs : count1480 q = (countLit q [-51]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-52])
  have hm := merge_right (literal (valuationOf q) (-52)) (literal (valuationOf q) (1480)) (countLit q [-51]) (countLit q [-52]) (count1480 q) 1 (meaningNeg52 q) (meaning1480 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1480 = true := counterClause430 (baseVal q)

theorem counterClause431 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 1480 = true := by
  have hs : count1480 q = (countLit q [-51]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-52])
  have hm := merge_left (literal (valuationOf q) (-51)) (literal (valuationOf q) (1480)) (countLit q [-51]) (countLit q [-52]) (count1480 q) 1 (meaningNeg51 q) (meaning1480 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 1480 = true := counterClause431 (baseVal q)

theorem counterClause432 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 52 = true ∨ valuationOf q 1481 = true := by
  have hs : count1480 q = (countLit q [-51]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-52])
  have hm := merge_two (literal (valuationOf q) (-51)) (literal (valuationOf q) (-52)) (literal (valuationOf q) (1481)) (countLit q [-51]) (countLit q [-52]) (count1480 q) 1 1 (meaningNeg51 q) (meaningNeg52 q) (meaning1481 q) hs
  change (! (valuationOf q 51)) = false ∨ (! (valuationOf q 52)) = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 52 = true ∨ valuation q 1481 = true := counterClause432 (baseVal q)

theorem counterClause433 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1482 = true := by
  have hs : count1482 q = (countLit q [-56]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-57])
  have hm := merge_right (literal (valuationOf q) (-57)) (literal (valuationOf q) (1482)) (countLit q [-56]) (countLit q [-57]) (count1482 q) 1 (meaningNeg57 q) (meaning1482 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1482 = true := counterClause433 (baseVal q)

theorem counterClause434 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1482 = true := by
  have hs : count1482 q = (countLit q [-56]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-57])
  have hm := merge_left (literal (valuationOf q) (-56)) (literal (valuationOf q) (1482)) (countLit q [-56]) (countLit q [-57]) (count1482 q) 1 (meaningNeg56 q) (meaning1482 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1482 = true := counterClause434 (baseVal q)

theorem counterClause435 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 57 = true ∨ valuationOf q 1483 = true := by
  have hs : count1482 q = (countLit q [-56]) + (countLit q [-57]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-57])
  have hm := merge_two (literal (valuationOf q) (-56)) (literal (valuationOf q) (-57)) (literal (valuationOf q) (1483)) (countLit q [-56]) (countLit q [-57]) (count1482 q) 1 1 (meaningNeg56 q) (meaningNeg57 q) (meaning1483 q) hs
  change (! (valuationOf q 56)) = false ∨ (! (valuationOf q 57)) = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 57 = true ∨ valuation q 1483 = true := counterClause435 (baseVal q)

theorem counterClause436 (q : Nat → Bool) : valuationOf q 1482 = false ∨ valuationOf q 1484 = true := by
  have hs : count1484 q = (countLit q [-51, -52]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-51, -52]) (l₂ := [-56, -57])
  have hm := merge_right (literal (valuationOf q) (1482)) (literal (valuationOf q) (1484)) (countLit q [-51, -52]) (countLit q [-56, -57]) (count1484 q) 1 (meaning1482 q) (meaning1484 q) hs
  change valuationOf q 1482 = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1484 = true := counterClause436 (baseVal q)

theorem counterClause437 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1484 = true := by
  have hs : count1484 q = (countLit q [-51, -52]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-51, -52]) (l₂ := [-56, -57])
  have hm := merge_left (literal (valuationOf q) (1480)) (literal (valuationOf q) (1484)) (countLit q [-51, -52]) (countLit q [-56, -57]) (count1484 q) 1 (meaning1480 q) (meaning1484 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1484 = true := counterClause437 (baseVal q)

theorem counterClause438 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1485 = true := by
  have hs : count1484 q = (countLit q [-51, -52]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-51, -52]) (l₂ := [-56, -57])
  have hm := merge_two (literal (valuationOf q) (1480)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1485)) (countLit q [-51, -52]) (countLit q [-56, -57]) (count1484 q) 1 1 (meaning1480 q) (meaning1482 q) (meaning1485 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1482 = false ∨ valuation q 1485 = true := counterClause438 (baseVal q)

theorem counterClause439 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1486 = true := by
  have hs : count1484 q = (countLit q [-51, -52]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-51, -52]) (l₂ := [-56, -57])
  have hm := merge_two (literal (valuationOf q) (1480)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1486)) (countLit q [-51, -52]) (countLit q [-56, -57]) (count1484 q) 1 2 (meaning1480 q) (meaning1483 q) (meaning1486 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1483 = false ∨ valuation q 1486 = true := counterClause439 (baseVal q)

theorem counterClause440 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1485 = true := by
  have hs : count1484 q = (countLit q [-51, -52]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-51, -52]) (l₂ := [-56, -57])
  have hm := merge_left (literal (valuationOf q) (1481)) (literal (valuationOf q) (1485)) (countLit q [-51, -52]) (countLit q [-56, -57]) (count1484 q) 2 (meaning1481 q) (meaning1485 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1485 = true := counterClause440 (baseVal q)

theorem counterClause441 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1486 = true := by
  have hs : count1484 q = (countLit q [-51, -52]) + (countLit q [-56, -57]) := List.countP_append (p := literal q) (l₁ := [-51, -52]) (l₂ := [-56, -57])
  have hm := merge_two (literal (valuationOf q) (1481)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1486)) (countLit q [-51, -52]) (countLit q [-56, -57]) (count1484 q) 2 1 (meaning1481 q) (meaning1482 q) (meaning1486 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1482 = false ∨ valuation q 1486 = true := counterClause441 (baseVal q)

theorem counterClause442 (q : Nat → Bool) : valuationOf q 1484 = false ∨ valuationOf q 1488 = true := by
  have hs : count1488 q = (countLit q [-46, -48, -49]) + (countLit q [-51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49]) (l₂ := [-51, -52, -56, -57])
  have hm := merge_right (literal (valuationOf q) (1484)) (literal (valuationOf q) (1488)) (countLit q [-46, -48, -49]) (countLit q [-51, -52, -56, -57]) (count1488 q) 1 (meaning1484 q) (meaning1488 q) hs
  change valuationOf q 1484 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 1484 = false ∨ valuation q 1488 = true := counterClause442 (baseVal q)

theorem counterClause443 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1489 = true := by
  have hs : count1488 q = (countLit q [-46, -48, -49]) + (countLit q [-51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49]) (l₂ := [-51, -52, -56, -57])
  have hm := merge_right (literal (valuationOf q) (1485)) (literal (valuationOf q) (1489)) (countLit q [-46, -48, -49]) (countLit q [-51, -52, -56, -57]) (count1488 q) 2 (meaning1485 q) (meaning1489 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1489 = true := counterClause443 (baseVal q)

theorem counterClause444 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1490 = true := by
  have hs : count1488 q = (countLit q [-46, -48, -49]) + (countLit q [-51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49]) (l₂ := [-51, -52, -56, -57])
  have hm := merge_right (literal (valuationOf q) (1486)) (literal (valuationOf q) (1490)) (countLit q [-46, -48, -49]) (countLit q [-51, -52, -56, -57]) (count1488 q) 3 (meaning1486 q) (meaning1490 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1490 = true := counterClause444 (baseVal q)

theorem counterClause445 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1488 = true := by
  have hs : count1488 q = (countLit q [-46, -48, -49]) + (countLit q [-51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49]) (l₂ := [-51, -52, -56, -57])
  have hm := merge_left (literal (valuationOf q) (1477)) (literal (valuationOf q) (1488)) (countLit q [-46, -48, -49]) (countLit q [-51, -52, -56, -57]) (count1488 q) 1 (meaning1477 q) (meaning1488 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1488 = true := counterClause445 (baseVal q)

theorem counterClause446 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1489 = true := by
  have hs : count1488 q = (countLit q [-46, -48, -49]) + (countLit q [-51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49]) (l₂ := [-51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1477)) (literal (valuationOf q) (1484)) (literal (valuationOf q) (1489)) (countLit q [-46, -48, -49]) (countLit q [-51, -52, -56, -57]) (count1488 q) 1 1 (meaning1477 q) (meaning1484 q) (meaning1489 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1484 = false ∨ valuation q 1489 = true := counterClause446 (baseVal q)

theorem counterClause447 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1485 = false ∨ valuationOf q 1490 = true := by
  have hs : count1488 q = (countLit q [-46, -48, -49]) + (countLit q [-51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49]) (l₂ := [-51, -52, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1477)) (literal (valuationOf q) (1485)) (literal (valuationOf q) (1490)) (countLit q [-46, -48, -49]) (countLit q [-51, -52, -56, -57]) (count1488 q) 1 2 (meaning1477 q) (meaning1485 q) (meaning1490 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1485 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1485 = false ∨ valuation q 1490 = true := counterClause447 (baseVal q)

theorem counterClause448 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1489 = true := by
  have hs : count1488 q = (countLit q [-46, -48, -49]) + (countLit q [-51, -52, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49]) (l₂ := [-51, -52, -56, -57])
  have hm := merge_left (literal (valuationOf q) (1478)) (literal (valuationOf q) (1489)) (countLit q [-46, -48, -49]) (countLit q [-51, -52, -56, -57]) (count1488 q) 2 (meaning1478 q) (meaning1489 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1489 = true := counterClause448 (baseVal q)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E058.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112058
