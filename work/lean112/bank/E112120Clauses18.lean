import E112120Semantics
import B112E120Inputs
namespace Snake9.Regrowth.E112120
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause577 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1491 = true := by
  have hs : count1488 q = (countLit q [-46, -47, -48]) + (countLit q [-50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -48]) (l₂ := [-50, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1479)) (literal (valuationOf q) (1484)) (literal (valuationOf q) (1491)) (countLit q [-46, -47, -48]) (countLit q [-50, -53, -55, -56]) (count1488 q) 3 1 (meaning1479 q) (meaning1484 q) (meaning1491 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1484 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1484 = false ∨ valuation q 1491 = true := counterClause577 (baseVal q)

theorem counterClause578 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1496 = true := by
  have hs : count1495 q = (countLit q [-31, -33, -37, -38, -39, -40, -44]) + (countLit q [-46, -47, -48, -50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -37, -38, -39, -40, -44]) (l₂ := [-46, -47, -48, -50, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1488)) (literal (valuationOf q) (1496)) (countLit q [-31, -33, -37, -38, -39, -40, -44]) (countLit q [-46, -47, -48, -50, -53, -55, -56]) (count1495 q) 1 1 (meaning1468 q) (meaning1488 q) (meaning1496 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1488 = false ∨ valuation q 1496 = true := counterClause578 (baseVal q)

theorem counterClause579 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1497 = true := by
  have hs : count1495 q = (countLit q [-31, -33, -37, -38, -39, -40, -44]) + (countLit q [-46, -47, -48, -50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -37, -38, -39, -40, -44]) (l₂ := [-46, -47, -48, -50, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1489)) (literal (valuationOf q) (1497)) (countLit q [-31, -33, -37, -38, -39, -40, -44]) (countLit q [-46, -47, -48, -50, -53, -55, -56]) (count1495 q) 1 2 (meaning1468 q) (meaning1489 q) (meaning1497 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1489 = false ∨ valuation q 1497 = true := counterClause579 (baseVal q)

theorem counterClause580 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1498 = true := by
  have hs : count1495 q = (countLit q [-31, -33, -37, -38, -39, -40, -44]) + (countLit q [-46, -47, -48, -50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -37, -38, -39, -40, -44]) (l₂ := [-46, -47, -48, -50, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1490)) (literal (valuationOf q) (1498)) (countLit q [-31, -33, -37, -38, -39, -40, -44]) (countLit q [-46, -47, -48, -50, -53, -55, -56]) (count1495 q) 1 3 (meaning1468 q) (meaning1490 q) (meaning1498 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1490 = false ∨ valuation q 1498 = true := counterClause580 (baseVal q)

theorem counterClause581 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1499 = true := by
  have hs : count1495 q = (countLit q [-31, -33, -37, -38, -39, -40, -44]) + (countLit q [-46, -47, -48, -50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -37, -38, -39, -40, -44]) (l₂ := [-46, -47, -48, -50, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1491)) (literal (valuationOf q) (1499)) (countLit q [-31, -33, -37, -38, -39, -40, -44]) (countLit q [-46, -47, -48, -50, -53, -55, -56]) (count1495 q) 1 4 (meaning1468 q) (meaning1491 q) (meaning1499 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1491 = false ∨ valuation q 1499 = true := counterClause581 (baseVal q)

theorem counterClause582 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1497 = true := by
  have hs : count1495 q = (countLit q [-31, -33, -37, -38, -39, -40, -44]) + (countLit q [-46, -47, -48, -50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -37, -38, -39, -40, -44]) (l₂ := [-46, -47, -48, -50, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1469)) (literal (valuationOf q) (1488)) (literal (valuationOf q) (1497)) (countLit q [-31, -33, -37, -38, -39, -40, -44]) (countLit q [-46, -47, -48, -50, -53, -55, -56]) (count1495 q) 2 1 (meaning1469 q) (meaning1488 q) (meaning1497 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1488 = false ∨ valuation q 1497 = true := counterClause582 (baseVal q)

theorem counterClause583 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1498 = true := by
  have hs : count1495 q = (countLit q [-31, -33, -37, -38, -39, -40, -44]) + (countLit q [-46, -47, -48, -50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -37, -38, -39, -40, -44]) (l₂ := [-46, -47, -48, -50, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1469)) (literal (valuationOf q) (1489)) (literal (valuationOf q) (1498)) (countLit q [-31, -33, -37, -38, -39, -40, -44]) (countLit q [-46, -47, -48, -50, -53, -55, -56]) (count1495 q) 2 2 (meaning1469 q) (meaning1489 q) (meaning1498 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1489 = false ∨ valuation q 1498 = true := counterClause583 (baseVal q)

theorem counterClause584 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1499 = true := by
  have hs : count1495 q = (countLit q [-31, -33, -37, -38, -39, -40, -44]) + (countLit q [-46, -47, -48, -50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -37, -38, -39, -40, -44]) (l₂ := [-46, -47, -48, -50, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1469)) (literal (valuationOf q) (1490)) (literal (valuationOf q) (1499)) (countLit q [-31, -33, -37, -38, -39, -40, -44]) (countLit q [-46, -47, -48, -50, -53, -55, -56]) (count1495 q) 2 3 (meaning1469 q) (meaning1490 q) (meaning1499 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1490 = false ∨ valuation q 1499 = true := counterClause584 (baseVal q)

theorem counterClause585 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1498 = true := by
  have hs : count1495 q = (countLit q [-31, -33, -37, -38, -39, -40, -44]) + (countLit q [-46, -47, -48, -50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -37, -38, -39, -40, -44]) (l₂ := [-46, -47, -48, -50, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1470)) (literal (valuationOf q) (1488)) (literal (valuationOf q) (1498)) (countLit q [-31, -33, -37, -38, -39, -40, -44]) (countLit q [-46, -47, -48, -50, -53, -55, -56]) (count1495 q) 3 1 (meaning1470 q) (meaning1488 q) (meaning1498 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1488 = false ∨ valuation q 1498 = true := counterClause585 (baseVal q)

theorem counterClause586 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1499 = true := by
  have hs : count1495 q = (countLit q [-31, -33, -37, -38, -39, -40, -44]) + (countLit q [-46, -47, -48, -50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -37, -38, -39, -40, -44]) (l₂ := [-46, -47, -48, -50, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1470)) (literal (valuationOf q) (1489)) (literal (valuationOf q) (1499)) (countLit q [-31, -33, -37, -38, -39, -40, -44]) (countLit q [-46, -47, -48, -50, -53, -55, -56]) (count1495 q) 3 2 (meaning1470 q) (meaning1489 q) (meaning1499 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1489 = false ∨ valuation q 1499 = true := counterClause586 (baseVal q)

theorem counterClause587 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1500 = true := by
  have hs : count1495 q = (countLit q [-31, -33, -37, -38, -39, -40, -44]) + (countLit q [-46, -47, -48, -50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -37, -38, -39, -40, -44]) (l₂ := [-46, -47, -48, -50, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1470)) (literal (valuationOf q) (1490)) (literal (valuationOf q) (1500)) (countLit q [-31, -33, -37, -38, -39, -40, -44]) (countLit q [-46, -47, -48, -50, -53, -55, -56]) (count1495 q) 3 3 (meaning1470 q) (meaning1490 q) (meaning1500 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1490 = false ∨ valuation q 1500 = true := counterClause587 (baseVal q)

theorem counterClause588 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1498 = true := by
  have hs : count1495 q = (countLit q [-31, -33, -37, -38, -39, -40, -44]) + (countLit q [-46, -47, -48, -50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -37, -38, -39, -40, -44]) (l₂ := [-46, -47, -48, -50, -53, -55, -56])
  have hm := merge_left (literal (valuationOf q) (1471)) (literal (valuationOf q) (1498)) (countLit q [-31, -33, -37, -38, -39, -40, -44]) (countLit q [-46, -47, -48, -50, -53, -55, -56]) (count1495 q) 4 (meaning1471 q) (meaning1498 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1498 = true := counterClause588 (baseVal q)

theorem counterClause589 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1499 = true := by
  have hs : count1495 q = (countLit q [-31, -33, -37, -38, -39, -40, -44]) + (countLit q [-46, -47, -48, -50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -37, -38, -39, -40, -44]) (l₂ := [-46, -47, -48, -50, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1471)) (literal (valuationOf q) (1488)) (literal (valuationOf q) (1499)) (countLit q [-31, -33, -37, -38, -39, -40, -44]) (countLit q [-46, -47, -48, -50, -53, -55, -56]) (count1495 q) 4 1 (meaning1471 q) (meaning1488 q) (meaning1499 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1488 = false ∨ valuation q 1499 = true := counterClause589 (baseVal q)

theorem counterClause590 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1500 = true := by
  have hs : count1495 q = (countLit q [-31, -33, -37, -38, -39, -40, -44]) + (countLit q [-46, -47, -48, -50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -37, -38, -39, -40, -44]) (l₂ := [-46, -47, -48, -50, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1471)) (literal (valuationOf q) (1489)) (literal (valuationOf q) (1500)) (countLit q [-31, -33, -37, -38, -39, -40, -44]) (countLit q [-46, -47, -48, -50, -53, -55, -56]) (count1495 q) 4 2 (meaning1471 q) (meaning1489 q) (meaning1500 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1489 = false ∨ valuation q 1500 = true := counterClause590 (baseVal q)

theorem counterClause591 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1512 = true := by
  have hs : count1509 q = (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) + (countLit q [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) (l₂ := [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1441)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1512)) (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) (countLit q [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) (count1509 q) 1 3 (meaning1441 q) (meaning1497 q) (meaning1512 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1497 = false ∨ valuation q 1512 = true := counterClause591 (baseVal q)

theorem counterClause592 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1512 = true := by
  have hs : count1509 q = (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) + (countLit q [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) (l₂ := [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1512)) (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) (countLit q [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) (count1509 q) 2 2 (meaning1442 q) (meaning1496 q) (meaning1512 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1496 = false ∨ valuation q 1512 = true := counterClause592 (baseVal q)

theorem counterClause593 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1513 = true := by
  have hs : count1509 q = (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) + (countLit q [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) (l₂ := [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1513)) (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) (countLit q [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) (count1509 q) 2 3 (meaning1442 q) (meaning1497 q) (meaning1513 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1497 = false ∨ valuation q 1513 = true := counterClause593 (baseVal q)

theorem counterClause594 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1514 = true := by
  have hs : count1509 q = (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) + (countLit q [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) (l₂ := [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1498)) (literal (valuationOf q) (1514)) (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) (countLit q [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) (count1509 q) 2 4 (meaning1442 q) (meaning1498 q) (meaning1514 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1498 = false ∨ valuation q 1514 = true := counterClause594 (baseVal q)

theorem counterClause595 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1515 = true := by
  have hs : count1509 q = (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) + (countLit q [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) (l₂ := [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1499)) (literal (valuationOf q) (1515)) (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) (countLit q [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) (count1509 q) 2 5 (meaning1442 q) (meaning1499 q) (meaning1515 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1499 = false ∨ valuation q 1515 = true := counterClause595 (baseVal q)

theorem counterClause596 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1513 = true := by
  have hs : count1509 q = (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) + (countLit q [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) (l₂ := [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1513)) (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) (countLit q [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) (count1509 q) 3 2 (meaning1443 q) (meaning1496 q) (meaning1513 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1496 = false ∨ valuation q 1513 = true := counterClause596 (baseVal q)

theorem counterClause597 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1514 = true := by
  have hs : count1509 q = (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) + (countLit q [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) (l₂ := [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1514)) (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) (countLit q [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) (count1509 q) 3 3 (meaning1443 q) (meaning1497 q) (meaning1514 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1497 = false ∨ valuation q 1514 = true := counterClause597 (baseVal q)

theorem counterClause598 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1515 = true := by
  have hs : count1509 q = (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) + (countLit q [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) (l₂ := [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1498)) (literal (valuationOf q) (1515)) (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) (countLit q [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) (count1509 q) 3 4 (meaning1443 q) (meaning1498 q) (meaning1515 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1498 = false ∨ valuation q 1515 = true := counterClause598 (baseVal q)

theorem counterClause599 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1516 = true := by
  have hs : count1509 q = (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) + (countLit q [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) (l₂ := [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1499)) (literal (valuationOf q) (1516)) (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) (countLit q [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) (count1509 q) 3 5 (meaning1443 q) (meaning1499 q) (meaning1516 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1499 = false ∨ valuation q 1516 = true := counterClause599 (baseVal q)

theorem counterClause600 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1517 = true := by
  have hs : count1509 q = (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) + (countLit q [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) (l₂ := [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1500)) (literal (valuationOf q) (1517)) (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) (countLit q [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) (count1509 q) 3 6 (meaning1443 q) (meaning1500 q) (meaning1517 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1500 = false ∨ valuation q 1517 = true := counterClause600 (baseVal q)

theorem counterClause601 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1514 = true := by
  have hs : count1509 q = (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) + (countLit q [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) (l₂ := [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1444)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1514)) (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) (countLit q [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) (count1509 q) 4 2 (meaning1444 q) (meaning1496 q) (meaning1514 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1496 = false ∨ valuation q 1514 = true := counterClause601 (baseVal q)

theorem counterClause602 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1515 = true := by
  have hs : count1509 q = (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) + (countLit q [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) (l₂ := [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1444)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1515)) (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) (countLit q [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) (count1509 q) 4 3 (meaning1444 q) (meaning1497 q) (meaning1515 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1497 = false ∨ valuation q 1515 = true := counterClause602 (baseVal q)

theorem counterClause603 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1516 = true := by
  have hs : count1509 q = (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) + (countLit q [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) (l₂ := [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1444)) (literal (valuationOf q) (1498)) (literal (valuationOf q) (1516)) (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) (countLit q [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) (count1509 q) 4 4 (meaning1444 q) (meaning1498 q) (meaning1516 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1498 = false ∨ valuation q 1516 = true := counterClause603 (baseVal q)

theorem counterClause604 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1517 = true := by
  have hs : count1509 q = (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) + (countLit q [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) (l₂ := [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1444)) (literal (valuationOf q) (1499)) (literal (valuationOf q) (1517)) (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) (countLit q [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) (count1509 q) 4 5 (meaning1444 q) (meaning1499 q) (meaning1517 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1499 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1499 = false ∨ valuation q 1517 = true := counterClause604 (baseVal q)

theorem counterClause605 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1516 = true := by
  have hs : count1509 q = (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) + (countLit q [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) (l₂ := [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1516)) (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) (countLit q [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) (count1509 q) 5 3 (meaning1445 q) (meaning1497 q) (meaning1516 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1497 = false ∨ valuation q 1516 = true := counterClause605 (baseVal q)

theorem counterClause606 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1517 = true := by
  have hs : count1509 q = (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) + (countLit q [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) (l₂ := [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1498)) (literal (valuationOf q) (1517)) (countLit q [-1, -2, -5, -8, -10, -14, -15, -16, -19, -21, -24, -25, -28, -30]) (countLit q [-31, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56]) (count1509 q) 5 4 (meaning1445 q) (meaning1498 q) (meaning1517 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1498 = false ∨ valuation q 1517 = true := counterClause606 (baseVal q)

theorem counterClause607 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1526 = true := by
  have hs : count1526 q = (countLit q [-62]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63])
  have hm := merge_right (literal (valuationOf q) (-63)) (literal (valuationOf q) (1526)) (countLit q [-62]) (countLit q [-63]) (count1526 q) 1 (meaningNeg63 q) (meaning1526 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1526 = true := counterClause607 (baseVal q)

theorem counterClause608 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 63 = true ∨ valuationOf q 1527 = true := by
  have hs : count1526 q = (countLit q [-62]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63])
  have hm := merge_two (literal (valuationOf q) (-62)) (literal (valuationOf q) (-63)) (literal (valuationOf q) (1527)) (countLit q [-62]) (countLit q [-63]) (count1526 q) 1 1 (meaningNeg62 q) (meaningNeg63 q) (meaning1527 q) hs
  change (! (valuationOf q 62)) = false ∨ (! (valuationOf q 63)) = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 63 = true ∨ valuation q 1527 = true := counterClause608 (baseVal q)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E120.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112120
