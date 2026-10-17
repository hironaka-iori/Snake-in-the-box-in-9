import E112120Semantics
import B112E120Inputs
namespace Snake9.Regrowth.E112120
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause545 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1471 = true := by
  have hs : count1468 q = (countLit q [-31, -33, -37]) + (countLit q [-38, -39, -40, -44]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -37]) (l₂ := [-38, -39, -40, -44])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1466)) (literal (valuationOf q) (1471)) (countLit q [-31, -33, -37]) (countLit q [-38, -39, -40, -44]) (count1468 q) 1 3 (meaning1457 q) (meaning1466 q) (meaning1471 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1466 = false ∨ valuation q 1471 = true := counterClause545 (baseVal q)

theorem counterClause546 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1471 = true := by
  have hs : count1468 q = (countLit q [-31, -33, -37]) + (countLit q [-38, -39, -40, -44]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -37]) (l₂ := [-38, -39, -40, -44])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1465)) (literal (valuationOf q) (1471)) (countLit q [-31, -33, -37]) (countLit q [-38, -39, -40, -44]) (count1468 q) 2 2 (meaning1458 q) (meaning1465 q) (meaning1471 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1465 = false ∨ valuation q 1471 = true := counterClause546 (baseVal q)

theorem counterClause547 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 1475 = true := by
  have hs : count1475 q = (countLit q [-47]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-48])
  have hm := merge_right (literal (valuationOf q) (-48)) (literal (valuationOf q) (1475)) (countLit q [-47]) (countLit q [-48]) (count1475 q) 1 (meaningNeg48 q) (meaning1475 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 1475 = true := counterClause547 (baseVal q)

theorem counterClause548 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 1475 = true := by
  have hs : count1475 q = (countLit q [-47]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-48])
  have hm := merge_left (literal (valuationOf q) (-47)) (literal (valuationOf q) (1475)) (countLit q [-47]) (countLit q [-48]) (count1475 q) 1 (meaningNeg47 q) (meaning1475 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 1475 = true := counterClause548 (baseVal q)

theorem counterClause549 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 48 = true ∨ valuationOf q 1476 = true := by
  have hs : count1475 q = (countLit q [-47]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-48])
  have hm := merge_two (literal (valuationOf q) (-47)) (literal (valuationOf q) (-48)) (literal (valuationOf q) (1476)) (countLit q [-47]) (countLit q [-48]) (count1475 q) 1 1 (meaningNeg47 q) (meaningNeg48 q) (meaning1476 q) hs
  change (! (valuationOf q 47)) = false ∨ (! (valuationOf q 48)) = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 48 = true ∨ valuation q 1476 = true := counterClause549 (baseVal q)

theorem counterClause550 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1477 = true := by
  have hs : count1477 q = (countLit q [-46]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-47, -48])
  have hm := merge_right (literal (valuationOf q) (1475)) (literal (valuationOf q) (1477)) (countLit q [-46]) (countLit q [-47, -48]) (count1477 q) 1 (meaning1475 q) (meaning1477 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1477 = true := counterClause550 (baseVal q)

theorem counterClause551 (q : Nat → Bool) : valuationOf q 1476 = false ∨ valuationOf q 1478 = true := by
  have hs : count1477 q = (countLit q [-46]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-47, -48])
  have hm := merge_right (literal (valuationOf q) (1476)) (literal (valuationOf q) (1478)) (countLit q [-46]) (countLit q [-47, -48]) (count1477 q) 2 (meaning1476 q) (meaning1478 q) hs
  change valuationOf q 1476 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1478 = true := counterClause551 (baseVal q)

theorem counterClause552 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1477 = true := by
  have hs : count1477 q = (countLit q [-46]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-47, -48])
  have hm := merge_left (literal (valuationOf q) (-46)) (literal (valuationOf q) (1477)) (countLit q [-46]) (countLit q [-47, -48]) (count1477 q) 1 (meaningNeg46 q) (meaning1477 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1477 = true := counterClause552 (baseVal q)

theorem counterClause553 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1475 = false ∨ valuationOf q 1478 = true := by
  have hs : count1477 q = (countLit q [-46]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-47, -48])
  have hm := merge_two (literal (valuationOf q) (-46)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1478)) (countLit q [-46]) (countLit q [-47, -48]) (count1477 q) 1 1 (meaningNeg46 q) (meaning1475 q) (meaning1478 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1475 = false ∨ valuation q 1478 = true := counterClause553 (baseVal q)

theorem counterClause554 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1476 = false ∨ valuationOf q 1479 = true := by
  have hs : count1477 q = (countLit q [-46]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-47, -48])
  have hm := merge_two (literal (valuationOf q) (-46)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1479)) (countLit q [-46]) (countLit q [-47, -48]) (count1477 q) 1 2 (meaningNeg46 q) (meaning1476 q) (meaning1479 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1476 = false ∨ valuation q 1479 = true := counterClause554 (baseVal q)

theorem counterClause555 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 1480 = true := by
  have hs : count1480 q = (countLit q [-50]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-53])
  have hm := merge_right (literal (valuationOf q) (-53)) (literal (valuationOf q) (1480)) (countLit q [-50]) (countLit q [-53]) (count1480 q) 1 (meaningNeg53 q) (meaning1480 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 1480 = true := counterClause555 (baseVal q)

theorem counterClause556 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 1480 = true := by
  have hs : count1480 q = (countLit q [-50]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-53])
  have hm := merge_left (literal (valuationOf q) (-50)) (literal (valuationOf q) (1480)) (countLit q [-50]) (countLit q [-53]) (count1480 q) 1 (meaningNeg50 q) (meaning1480 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 1480 = true := counterClause556 (baseVal q)

theorem counterClause557 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 53 = true ∨ valuationOf q 1481 = true := by
  have hs : count1480 q = (countLit q [-50]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-53])
  have hm := merge_two (literal (valuationOf q) (-50)) (literal (valuationOf q) (-53)) (literal (valuationOf q) (1481)) (countLit q [-50]) (countLit q [-53]) (count1480 q) 1 1 (meaningNeg50 q) (meaningNeg53 q) (meaning1481 q) hs
  change (! (valuationOf q 50)) = false ∨ (! (valuationOf q 53)) = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 53 = true ∨ valuation q 1481 = true := counterClause557 (baseVal q)

theorem counterClause558 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1482 = true := by
  have hs : count1482 q = (countLit q [-55]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-56])
  have hm := merge_right (literal (valuationOf q) (-56)) (literal (valuationOf q) (1482)) (countLit q [-55]) (countLit q [-56]) (count1482 q) 1 (meaningNeg56 q) (meaning1482 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1482 = true := counterClause558 (baseVal q)

theorem counterClause559 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 1482 = true := by
  have hs : count1482 q = (countLit q [-55]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-56])
  have hm := merge_left (literal (valuationOf q) (-55)) (literal (valuationOf q) (1482)) (countLit q [-55]) (countLit q [-56]) (count1482 q) 1 (meaningNeg55 q) (meaning1482 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 1482 = true := counterClause559 (baseVal q)

theorem counterClause560 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 56 = true ∨ valuationOf q 1483 = true := by
  have hs : count1482 q = (countLit q [-55]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-56])
  have hm := merge_two (literal (valuationOf q) (-55)) (literal (valuationOf q) (-56)) (literal (valuationOf q) (1483)) (countLit q [-55]) (countLit q [-56]) (count1482 q) 1 1 (meaningNeg55 q) (meaningNeg56 q) (meaning1483 q) hs
  change (! (valuationOf q 55)) = false ∨ (! (valuationOf q 56)) = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 56 = true ∨ valuation q 1483 = true := counterClause560 (baseVal q)

theorem counterClause561 (q : Nat → Bool) : valuationOf q 1482 = false ∨ valuationOf q 1484 = true := by
  have hs : count1484 q = (countLit q [-50, -53]) + (countLit q [-55, -56]) := List.countP_append (p := literal q) (l₁ := [-50, -53]) (l₂ := [-55, -56])
  have hm := merge_right (literal (valuationOf q) (1482)) (literal (valuationOf q) (1484)) (countLit q [-50, -53]) (countLit q [-55, -56]) (count1484 q) 1 (meaning1482 q) (meaning1484 q) hs
  change valuationOf q 1482 = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1484 = true := counterClause561 (baseVal q)

theorem counterClause562 (q : Nat → Bool) : valuationOf q 1483 = false ∨ valuationOf q 1485 = true := by
  have hs : count1484 q = (countLit q [-50, -53]) + (countLit q [-55, -56]) := List.countP_append (p := literal q) (l₁ := [-50, -53]) (l₂ := [-55, -56])
  have hm := merge_right (literal (valuationOf q) (1483)) (literal (valuationOf q) (1485)) (countLit q [-50, -53]) (countLit q [-55, -56]) (count1484 q) 2 (meaning1483 q) (meaning1485 q) hs
  change valuationOf q 1483 = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 1483 = false ∨ valuation q 1485 = true := counterClause562 (baseVal q)

theorem counterClause563 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1484 = true := by
  have hs : count1484 q = (countLit q [-50, -53]) + (countLit q [-55, -56]) := List.countP_append (p := literal q) (l₁ := [-50, -53]) (l₂ := [-55, -56])
  have hm := merge_left (literal (valuationOf q) (1480)) (literal (valuationOf q) (1484)) (countLit q [-50, -53]) (countLit q [-55, -56]) (count1484 q) 1 (meaning1480 q) (meaning1484 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1484 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1484 = true := counterClause563 (baseVal q)

theorem counterClause564 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1485 = true := by
  have hs : count1484 q = (countLit q [-50, -53]) + (countLit q [-55, -56]) := List.countP_append (p := literal q) (l₁ := [-50, -53]) (l₂ := [-55, -56])
  have hm := merge_two (literal (valuationOf q) (1480)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1485)) (countLit q [-50, -53]) (countLit q [-55, -56]) (count1484 q) 1 1 (meaning1480 q) (meaning1482 q) (meaning1485 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1482 = false ∨ valuation q 1485 = true := counterClause564 (baseVal q)

theorem counterClause565 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1486 = true := by
  have hs : count1484 q = (countLit q [-50, -53]) + (countLit q [-55, -56]) := List.countP_append (p := literal q) (l₁ := [-50, -53]) (l₂ := [-55, -56])
  have hm := merge_two (literal (valuationOf q) (1480)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1486)) (countLit q [-50, -53]) (countLit q [-55, -56]) (count1484 q) 1 2 (meaning1480 q) (meaning1483 q) (meaning1486 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1483 = false ∨ valuation q 1486 = true := counterClause565 (baseVal q)

theorem counterClause566 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1485 = true := by
  have hs : count1484 q = (countLit q [-50, -53]) + (countLit q [-55, -56]) := List.countP_append (p := literal q) (l₁ := [-50, -53]) (l₂ := [-55, -56])
  have hm := merge_left (literal (valuationOf q) (1481)) (literal (valuationOf q) (1485)) (countLit q [-50, -53]) (countLit q [-55, -56]) (count1484 q) 2 (meaning1481 q) (meaning1485 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1485 = true := counterClause566 (baseVal q)

theorem counterClause567 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1486 = true := by
  have hs : count1484 q = (countLit q [-50, -53]) + (countLit q [-55, -56]) := List.countP_append (p := literal q) (l₁ := [-50, -53]) (l₂ := [-55, -56])
  have hm := merge_two (literal (valuationOf q) (1481)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1486)) (countLit q [-50, -53]) (countLit q [-55, -56]) (count1484 q) 2 1 (meaning1481 q) (meaning1482 q) (meaning1486 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1482 = false ∨ valuation q 1486 = true := counterClause567 (baseVal q)

theorem counterClause568 (q : Nat → Bool) : valuationOf q 1484 = false ∨ valuationOf q 1488 = true := by
  have hs : count1488 q = (countLit q [-46, -47, -48]) + (countLit q [-50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -48]) (l₂ := [-50, -53, -55, -56])
  have hm := merge_right (literal (valuationOf q) (1484)) (literal (valuationOf q) (1488)) (countLit q [-46, -47, -48]) (countLit q [-50, -53, -55, -56]) (count1488 q) 1 (meaning1484 q) (meaning1488 q) hs
  change valuationOf q 1484 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 1484 = false ∨ valuation q 1488 = true := counterClause568 (baseVal q)

theorem counterClause569 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1489 = true := by
  have hs : count1488 q = (countLit q [-46, -47, -48]) + (countLit q [-50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -48]) (l₂ := [-50, -53, -55, -56])
  have hm := merge_right (literal (valuationOf q) (1485)) (literal (valuationOf q) (1489)) (countLit q [-46, -47, -48]) (countLit q [-50, -53, -55, -56]) (count1488 q) 2 (meaning1485 q) (meaning1489 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1489 = true := counterClause569 (baseVal q)

theorem counterClause570 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1490 = true := by
  have hs : count1488 q = (countLit q [-46, -47, -48]) + (countLit q [-50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -48]) (l₂ := [-50, -53, -55, -56])
  have hm := merge_right (literal (valuationOf q) (1486)) (literal (valuationOf q) (1490)) (countLit q [-46, -47, -48]) (countLit q [-50, -53, -55, -56]) (count1488 q) 3 (meaning1486 q) (meaning1490 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1490 = true := counterClause570 (baseVal q)

theorem counterClause571 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1488 = true := by
  have hs : count1488 q = (countLit q [-46, -47, -48]) + (countLit q [-50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -48]) (l₂ := [-50, -53, -55, -56])
  have hm := merge_left (literal (valuationOf q) (1477)) (literal (valuationOf q) (1488)) (countLit q [-46, -47, -48]) (countLit q [-50, -53, -55, -56]) (count1488 q) 1 (meaning1477 q) (meaning1488 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1488 = true := counterClause571 (baseVal q)

theorem counterClause572 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1489 = true := by
  have hs : count1488 q = (countLit q [-46, -47, -48]) + (countLit q [-50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -48]) (l₂ := [-50, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1477)) (literal (valuationOf q) (1484)) (literal (valuationOf q) (1489)) (countLit q [-46, -47, -48]) (countLit q [-50, -53, -55, -56]) (count1488 q) 1 1 (meaning1477 q) (meaning1484 q) (meaning1489 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1484 = false ∨ valuation q 1489 = true := counterClause572 (baseVal q)

theorem counterClause573 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1485 = false ∨ valuationOf q 1490 = true := by
  have hs : count1488 q = (countLit q [-46, -47, -48]) + (countLit q [-50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -48]) (l₂ := [-50, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1477)) (literal (valuationOf q) (1485)) (literal (valuationOf q) (1490)) (countLit q [-46, -47, -48]) (countLit q [-50, -53, -55, -56]) (count1488 q) 1 2 (meaning1477 q) (meaning1485 q) (meaning1490 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1485 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1485 = false ∨ valuation q 1490 = true := counterClause573 (baseVal q)

theorem counterClause574 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1489 = true := by
  have hs : count1488 q = (countLit q [-46, -47, -48]) + (countLit q [-50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -48]) (l₂ := [-50, -53, -55, -56])
  have hm := merge_left (literal (valuationOf q) (1478)) (literal (valuationOf q) (1489)) (countLit q [-46, -47, -48]) (countLit q [-50, -53, -55, -56]) (count1488 q) 2 (meaning1478 q) (meaning1489 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1489 = true := counterClause574 (baseVal q)

theorem counterClause575 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1490 = true := by
  have hs : count1488 q = (countLit q [-46, -47, -48]) + (countLit q [-50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -48]) (l₂ := [-50, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1478)) (literal (valuationOf q) (1484)) (literal (valuationOf q) (1490)) (countLit q [-46, -47, -48]) (countLit q [-50, -53, -55, -56]) (count1488 q) 2 1 (meaning1478 q) (meaning1484 q) (meaning1490 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1484 = false ∨ valuation q 1490 = true := counterClause575 (baseVal q)

theorem counterClause576 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1490 = true := by
  have hs : count1488 q = (countLit q [-46, -47, -48]) + (countLit q [-50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -48]) (l₂ := [-50, -53, -55, -56])
  have hm := merge_left (literal (valuationOf q) (1479)) (literal (valuationOf q) (1490)) (countLit q [-46, -47, -48]) (countLit q [-50, -53, -55, -56]) (count1488 q) 3 (meaning1479 q) (meaning1490 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1490 = true := counterClause576 (baseVal q)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E120.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112120
