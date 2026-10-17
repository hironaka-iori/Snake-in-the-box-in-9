import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec44 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1409 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1556 = true := by
  have hs : count1549 q = (countLit q [-2, -5, -8, -9, -10, -11, -13]) + (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13]) (l₂ := [-14, -15, -18, -22, -24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1556)) (countLit q [-2, -5, -8, -9, -10, -11, -13]) (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) (count1549 q) 4 4 (meaning1521 q) (meaning1544 q) (meaning1556 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1409 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1544 = false ∨ valuation q 1556 = true := counterClause1409 (baseVal q)

theorem counterClause1410 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1554 = true := by
  have hs : count1549 q = (countLit q [-2, -5, -8, -9, -10, -11, -13]) + (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13]) (l₂ := [-14, -15, -18, -22, -24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1554)) (countLit q [-2, -5, -8, -9, -10, -11, -13]) (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) (count1549 q) 5 1 (meaning1522 q) (meaning1541 q) (meaning1554 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1410 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1541 = false ∨ valuation q 1554 = true := counterClause1410 (baseVal q)

theorem counterClause1411 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1555 = true := by
  have hs : count1549 q = (countLit q [-2, -5, -8, -9, -10, -11, -13]) + (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13]) (l₂ := [-14, -15, -18, -22, -24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1555)) (countLit q [-2, -5, -8, -9, -10, -11, -13]) (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) (count1549 q) 5 2 (meaning1522 q) (meaning1542 q) (meaning1555 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1411 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1542 = false ∨ valuation q 1555 = true := counterClause1411 (baseVal q)

theorem counterClause1412 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1556 = true := by
  have hs : count1549 q = (countLit q [-2, -5, -8, -9, -10, -11, -13]) + (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13]) (l₂ := [-14, -15, -18, -22, -24, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1556)) (countLit q [-2, -5, -8, -9, -10, -11, -13]) (countLit q [-14, -15, -18, -22, -24, -25, -27, -29]) (count1549 q) 5 3 (meaning1522 q) (meaning1543 q) (meaning1556 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1412 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1543 = false ∨ valuation q 1556 = true := counterClause1412 (baseVal q)

theorem counterClause1413 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1564 = true := by
  have hs : count1564 q = (countLit q [-31]) + (countLit q [-32]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-32])
  have hm := merge_right (literal (valuationOf q) (-32)) (literal (valuationOf q) (1564)) (countLit q [-31]) (countLit q [-32]) (count1564 q) 1 (meaningNeg32 q) (meaning1564 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1413 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1564 = true := counterClause1413 (baseVal q)

theorem counterClause1414 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1564 = true := by
  have hs : count1564 q = (countLit q [-31]) + (countLit q [-32]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-32])
  have hm := merge_left (literal (valuationOf q) (-31)) (literal (valuationOf q) (1564)) (countLit q [-31]) (countLit q [-32]) (count1564 q) 1 (meaningNeg31 q) (meaning1564 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1414 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1564 = true := counterClause1414 (baseVal q)

theorem counterClause1415 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 32 = true ∨ valuationOf q 1565 = true := by
  have hs : count1564 q = (countLit q [-31]) + (countLit q [-32]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-32])
  have hm := merge_two (literal (valuationOf q) (-31)) (literal (valuationOf q) (-32)) (literal (valuationOf q) (1565)) (countLit q [-31]) (countLit q [-32]) (count1564 q) 1 1 (meaningNeg31 q) (meaningNeg32 q) (meaning1565 q) hs
  change (! (valuationOf q 31)) = false ∨ (! (valuationOf q 32)) = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1415 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 32 = true ∨ valuation q 1565 = true := counterClause1415 (baseVal q)

theorem counterClause1416 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1566 = true := by
  have hs : count1566 q = (countLit q [-34]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-39])
  have hm := merge_right (literal (valuationOf q) (-39)) (literal (valuationOf q) (1566)) (countLit q [-34]) (countLit q [-39]) (count1566 q) 1 (meaningNeg39 q) (meaning1566 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1416 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1566 = true := counterClause1416 (baseVal q)

theorem counterClause1417 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 1566 = true := by
  have hs : count1566 q = (countLit q [-34]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-39])
  have hm := merge_left (literal (valuationOf q) (-34)) (literal (valuationOf q) (1566)) (countLit q [-34]) (countLit q [-39]) (count1566 q) 1 (meaningNeg34 q) (meaning1566 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1417 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 1566 = true := counterClause1417 (baseVal q)

theorem counterClause1418 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 39 = true ∨ valuationOf q 1567 = true := by
  have hs : count1566 q = (countLit q [-34]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-39])
  have hm := merge_two (literal (valuationOf q) (-34)) (literal (valuationOf q) (-39)) (literal (valuationOf q) (1567)) (countLit q [-34]) (countLit q [-39]) (count1566 q) 1 1 (meaningNeg34 q) (meaningNeg39 q) (meaning1567 q) hs
  change (! (valuationOf q 34)) = false ∨ (! (valuationOf q 39)) = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1418 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 39 = true ∨ valuation q 1567 = true := counterClause1418 (baseVal q)

theorem counterClause1419 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1568 = true := by
  have hs : count1568 q = (countLit q [-31, -32]) + (countLit q [-34, -39]) := List.countP_append (p := literal q) (l₁ := [-31, -32]) (l₂ := [-34, -39])
  have hm := merge_right (literal (valuationOf q) (1566)) (literal (valuationOf q) (1568)) (countLit q [-31, -32]) (countLit q [-34, -39]) (count1568 q) 1 (meaning1566 q) (meaning1568 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1419 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1568 = true := counterClause1419 (baseVal q)

theorem counterClause1420 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1569 = true := by
  have hs : count1568 q = (countLit q [-31, -32]) + (countLit q [-34, -39]) := List.countP_append (p := literal q) (l₁ := [-31, -32]) (l₂ := [-34, -39])
  have hm := merge_right (literal (valuationOf q) (1567)) (literal (valuationOf q) (1569)) (countLit q [-31, -32]) (countLit q [-34, -39]) (count1568 q) 2 (meaning1567 q) (meaning1569 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1420 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1569 = true := counterClause1420 (baseVal q)

theorem counterClause1421 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1568 = true := by
  have hs : count1568 q = (countLit q [-31, -32]) + (countLit q [-34, -39]) := List.countP_append (p := literal q) (l₁ := [-31, -32]) (l₂ := [-34, -39])
  have hm := merge_left (literal (valuationOf q) (1564)) (literal (valuationOf q) (1568)) (countLit q [-31, -32]) (countLit q [-34, -39]) (count1568 q) 1 (meaning1564 q) (meaning1568 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1421 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1568 = true := counterClause1421 (baseVal q)

theorem counterClause1422 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1569 = true := by
  have hs : count1568 q = (countLit q [-31, -32]) + (countLit q [-34, -39]) := List.countP_append (p := literal q) (l₁ := [-31, -32]) (l₂ := [-34, -39])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1566)) (literal (valuationOf q) (1569)) (countLit q [-31, -32]) (countLit q [-34, -39]) (count1568 q) 1 1 (meaning1564 q) (meaning1566 q) (meaning1569 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1422 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1566 = false ∨ valuation q 1569 = true := counterClause1422 (baseVal q)

theorem counterClause1423 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1570 = true := by
  have hs : count1568 q = (countLit q [-31, -32]) + (countLit q [-34, -39]) := List.countP_append (p := literal q) (l₁ := [-31, -32]) (l₂ := [-34, -39])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1567)) (literal (valuationOf q) (1570)) (countLit q [-31, -32]) (countLit q [-34, -39]) (count1568 q) 1 2 (meaning1564 q) (meaning1567 q) (meaning1570 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1423 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1567 = false ∨ valuation q 1570 = true := counterClause1423 (baseVal q)

theorem counterClause1424 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1569 = true := by
  have hs : count1568 q = (countLit q [-31, -32]) + (countLit q [-34, -39]) := List.countP_append (p := literal q) (l₁ := [-31, -32]) (l₂ := [-34, -39])
  have hm := merge_left (literal (valuationOf q) (1565)) (literal (valuationOf q) (1569)) (countLit q [-31, -32]) (countLit q [-34, -39]) (count1568 q) 2 (meaning1565 q) (meaning1569 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1424 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1569 = true := counterClause1424 (baseVal q)

theorem counterClause1425 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1570 = true := by
  have hs : count1568 q = (countLit q [-31, -32]) + (countLit q [-34, -39]) := List.countP_append (p := literal q) (l₁ := [-31, -32]) (l₂ := [-34, -39])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1566)) (literal (valuationOf q) (1570)) (countLit q [-31, -32]) (countLit q [-34, -39]) (count1568 q) 2 1 (meaning1565 q) (meaning1566 q) (meaning1570 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1425 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1566 = false ∨ valuation q 1570 = true := counterClause1425 (baseVal q)

theorem counterClause1426 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1571 = true := by
  have hs : count1568 q = (countLit q [-31, -32]) + (countLit q [-34, -39]) := List.countP_append (p := literal q) (l₁ := [-31, -32]) (l₂ := [-34, -39])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1567)) (literal (valuationOf q) (1571)) (countLit q [-31, -32]) (countLit q [-34, -39]) (count1568 q) 2 2 (meaning1565 q) (meaning1567 q) (meaning1571 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1426 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1567 = false ∨ valuation q 1571 = true := counterClause1426 (baseVal q)

theorem counterClause1427 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1572 = true := by
  have hs : count1572 q = (countLit q [-41]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-42])
  have hm := merge_right (literal (valuationOf q) (-42)) (literal (valuationOf q) (1572)) (countLit q [-41]) (countLit q [-42]) (count1572 q) 1 (meaningNeg42 q) (meaning1572 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1427 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1572 = true := counterClause1427 (baseVal q)

theorem counterClause1428 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 1572 = true := by
  have hs : count1572 q = (countLit q [-41]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-42])
  have hm := merge_left (literal (valuationOf q) (-41)) (literal (valuationOf q) (1572)) (countLit q [-41]) (countLit q [-42]) (count1572 q) 1 (meaningNeg41 q) (meaning1572 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1428 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1572 = true := counterClause1428 (baseVal q)

theorem counterClause1429 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 42 = true ∨ valuationOf q 1573 = true := by
  have hs : count1572 q = (countLit q [-41]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-42])
  have hm := merge_two (literal (valuationOf q) (-41)) (literal (valuationOf q) (-42)) (literal (valuationOf q) (1573)) (countLit q [-41]) (countLit q [-42]) (count1572 q) 1 1 (meaningNeg41 q) (meaningNeg42 q) (meaning1573 q) hs
  change (! (valuationOf q 41)) = false ∨ (! (valuationOf q 42)) = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1429 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 42 = true ∨ valuation q 1573 = true := counterClause1429 (baseVal q)

theorem counterClause1430 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 1574 = true := by
  have hs : count1574 q = (countLit q [-44]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-45])
  have hm := merge_right (literal (valuationOf q) (-45)) (literal (valuationOf q) (1574)) (countLit q [-44]) (countLit q [-45]) (count1574 q) 1 (meaningNeg45 q) (meaning1574 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1430 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1574 = true := counterClause1430 (baseVal q)

theorem counterClause1431 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1574 = true := by
  have hs : count1574 q = (countLit q [-44]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-45])
  have hm := merge_left (literal (valuationOf q) (-44)) (literal (valuationOf q) (1574)) (countLit q [-44]) (countLit q [-45]) (count1574 q) 1 (meaningNeg44 q) (meaning1574 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1431 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1574 = true := counterClause1431 (baseVal q)

theorem counterClause1432 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 45 = true ∨ valuationOf q 1575 = true := by
  have hs : count1574 q = (countLit q [-44]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-45])
  have hm := merge_two (literal (valuationOf q) (-44)) (literal (valuationOf q) (-45)) (literal (valuationOf q) (1575)) (countLit q [-44]) (countLit q [-45]) (count1574 q) 1 1 (meaningNeg44 q) (meaningNeg45 q) (meaning1575 q) hs
  change (! (valuationOf q 44)) = false ∨ (! (valuationOf q 45)) = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1432 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 45 = true ∨ valuation q 1575 = true := counterClause1432 (baseVal q)

theorem counterClause1433 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1576 = true := by
  have hs : count1576 q = (countLit q [-41, -42]) + (countLit q [-44, -45]) := List.countP_append (p := literal q) (l₁ := [-41, -42]) (l₂ := [-44, -45])
  have hm := merge_right (literal (valuationOf q) (1574)) (literal (valuationOf q) (1576)) (countLit q [-41, -42]) (countLit q [-44, -45]) (count1576 q) 1 (meaning1574 q) (meaning1576 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1433 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1576 = true := counterClause1433 (baseVal q)

theorem counterClause1434 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1577 = true := by
  have hs : count1576 q = (countLit q [-41, -42]) + (countLit q [-44, -45]) := List.countP_append (p := literal q) (l₁ := [-41, -42]) (l₂ := [-44, -45])
  have hm := merge_right (literal (valuationOf q) (1575)) (literal (valuationOf q) (1577)) (countLit q [-41, -42]) (countLit q [-44, -45]) (count1576 q) 2 (meaning1575 q) (meaning1577 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1434 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1577 = true := counterClause1434 (baseVal q)

theorem counterClause1435 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1576 = true := by
  have hs : count1576 q = (countLit q [-41, -42]) + (countLit q [-44, -45]) := List.countP_append (p := literal q) (l₁ := [-41, -42]) (l₂ := [-44, -45])
  have hm := merge_left (literal (valuationOf q) (1572)) (literal (valuationOf q) (1576)) (countLit q [-41, -42]) (countLit q [-44, -45]) (count1576 q) 1 (meaning1572 q) (meaning1576 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1435 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1576 = true := counterClause1435 (baseVal q)

theorem counterClause1436 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1577 = true := by
  have hs : count1576 q = (countLit q [-41, -42]) + (countLit q [-44, -45]) := List.countP_append (p := literal q) (l₁ := [-41, -42]) (l₂ := [-44, -45])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1574)) (literal (valuationOf q) (1577)) (countLit q [-41, -42]) (countLit q [-44, -45]) (count1576 q) 1 1 (meaning1572 q) (meaning1574 q) (meaning1577 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1436 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1574 = false ∨ valuation q 1577 = true := counterClause1436 (baseVal q)

theorem counterClause1437 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1578 = true := by
  have hs : count1576 q = (countLit q [-41, -42]) + (countLit q [-44, -45]) := List.countP_append (p := literal q) (l₁ := [-41, -42]) (l₂ := [-44, -45])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1575)) (literal (valuationOf q) (1578)) (countLit q [-41, -42]) (countLit q [-44, -45]) (count1576 q) 1 2 (meaning1572 q) (meaning1575 q) (meaning1578 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1437 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1575 = false ∨ valuation q 1578 = true := counterClause1437 (baseVal q)

theorem counterClause1438 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1577 = true := by
  have hs : count1576 q = (countLit q [-41, -42]) + (countLit q [-44, -45]) := List.countP_append (p := literal q) (l₁ := [-41, -42]) (l₂ := [-44, -45])
  have hm := merge_left (literal (valuationOf q) (1573)) (literal (valuationOf q) (1577)) (countLit q [-41, -42]) (countLit q [-44, -45]) (count1576 q) 2 (meaning1573 q) (meaning1577 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1438 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1577 = true := counterClause1438 (baseVal q)

theorem counterClause1439 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1578 = true := by
  have hs : count1576 q = (countLit q [-41, -42]) + (countLit q [-44, -45]) := List.countP_append (p := literal q) (l₁ := [-41, -42]) (l₂ := [-44, -45])
  have hm := merge_two (literal (valuationOf q) (1573)) (literal (valuationOf q) (1574)) (literal (valuationOf q) (1578)) (countLit q [-41, -42]) (countLit q [-44, -45]) (count1576 q) 2 1 (meaning1573 q) (meaning1574 q) (meaning1578 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1439 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1574 = false ∨ valuation q 1578 = true := counterClause1439 (baseVal q)

theorem counterClause1440 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1579 = true := by
  have hs : count1576 q = (countLit q [-41, -42]) + (countLit q [-44, -45]) := List.countP_append (p := literal q) (l₁ := [-41, -42]) (l₂ := [-44, -45])
  have hm := merge_two (literal (valuationOf q) (1573)) (literal (valuationOf q) (1575)) (literal (valuationOf q) (1579)) (countLit q [-41, -42]) (countLit q [-44, -45]) (count1576 q) 2 2 (meaning1573 q) (meaning1575 q) (meaning1579 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1440 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1575 = false ∨ valuation q 1579 = true := counterClause1440 (baseVal q)

theorem block44 (q : Snake 81) (h : Conditions q) : B112E089.Block44 (valuation q) :=
  ⟨clause1409 q h, clause1410 q h, clause1411 q h, clause1412 q h, clause1413 q h, clause1414 q h, clause1415 q h, clause1416 q h, clause1417 q h, clause1418 q h, clause1419 q h, clause1420 q h, clause1421 q h, clause1422 q h, clause1423 q h, clause1424 q h, clause1425 q h, clause1426 q h, clause1427 q h, clause1428 q h, clause1429 q h, clause1430 q h, clause1431 q h, clause1432 q h, clause1433 q h, clause1434 q h, clause1435 q h, clause1436 q h, clause1437 q h, clause1438 q h, clause1439 q h, clause1440 q h⟩

end
end Snake9.Regrowth.E112089
