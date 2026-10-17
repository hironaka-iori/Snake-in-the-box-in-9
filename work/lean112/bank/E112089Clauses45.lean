import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec45 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1441 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1580 = true := by
  have hs : count1580 q = (countLit q [-31, -32, -34, -39]) + (countLit q [-41, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39]) (l₂ := [-41, -42, -44, -45])
  have hm := merge_right (literal (valuationOf q) (1576)) (literal (valuationOf q) (1580)) (countLit q [-31, -32, -34, -39]) (countLit q [-41, -42, -44, -45]) (count1580 q) 1 (meaning1576 q) (meaning1580 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1441 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1580 = true := counterClause1441 (baseVal q)

theorem counterClause1442 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1581 = true := by
  have hs : count1580 q = (countLit q [-31, -32, -34, -39]) + (countLit q [-41, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39]) (l₂ := [-41, -42, -44, -45])
  have hm := merge_right (literal (valuationOf q) (1577)) (literal (valuationOf q) (1581)) (countLit q [-31, -32, -34, -39]) (countLit q [-41, -42, -44, -45]) (count1580 q) 2 (meaning1577 q) (meaning1581 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1442 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1581 = true := counterClause1442 (baseVal q)

theorem counterClause1443 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1582 = true := by
  have hs : count1580 q = (countLit q [-31, -32, -34, -39]) + (countLit q [-41, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39]) (l₂ := [-41, -42, -44, -45])
  have hm := merge_right (literal (valuationOf q) (1578)) (literal (valuationOf q) (1582)) (countLit q [-31, -32, -34, -39]) (countLit q [-41, -42, -44, -45]) (count1580 q) 3 (meaning1578 q) (meaning1582 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1443 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1582 = true := counterClause1443 (baseVal q)

theorem counterClause1444 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1583 = true := by
  have hs : count1580 q = (countLit q [-31, -32, -34, -39]) + (countLit q [-41, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39]) (l₂ := [-41, -42, -44, -45])
  have hm := merge_right (literal (valuationOf q) (1579)) (literal (valuationOf q) (1583)) (countLit q [-31, -32, -34, -39]) (countLit q [-41, -42, -44, -45]) (count1580 q) 4 (meaning1579 q) (meaning1583 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1444 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1583 = true := counterClause1444 (baseVal q)

theorem counterClause1445 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1580 = true := by
  have hs : count1580 q = (countLit q [-31, -32, -34, -39]) + (countLit q [-41, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39]) (l₂ := [-41, -42, -44, -45])
  have hm := merge_left (literal (valuationOf q) (1568)) (literal (valuationOf q) (1580)) (countLit q [-31, -32, -34, -39]) (countLit q [-41, -42, -44, -45]) (count1580 q) 1 (meaning1568 q) (meaning1580 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1445 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1580 = true := counterClause1445 (baseVal q)

theorem counterClause1446 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1581 = true := by
  have hs : count1580 q = (countLit q [-31, -32, -34, -39]) + (countLit q [-41, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39]) (l₂ := [-41, -42, -44, -45])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1581)) (countLit q [-31, -32, -34, -39]) (countLit q [-41, -42, -44, -45]) (count1580 q) 1 1 (meaning1568 q) (meaning1576 q) (meaning1581 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1446 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1576 = false ∨ valuation q 1581 = true := counterClause1446 (baseVal q)

theorem counterClause1447 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1582 = true := by
  have hs : count1580 q = (countLit q [-31, -32, -34, -39]) + (countLit q [-41, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39]) (l₂ := [-41, -42, -44, -45])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1582)) (countLit q [-31, -32, -34, -39]) (countLit q [-41, -42, -44, -45]) (count1580 q) 1 2 (meaning1568 q) (meaning1577 q) (meaning1582 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1447 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1577 = false ∨ valuation q 1582 = true := counterClause1447 (baseVal q)

theorem counterClause1448 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1583 = true := by
  have hs : count1580 q = (countLit q [-31, -32, -34, -39]) + (countLit q [-41, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39]) (l₂ := [-41, -42, -44, -45])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1578)) (literal (valuationOf q) (1583)) (countLit q [-31, -32, -34, -39]) (countLit q [-41, -42, -44, -45]) (count1580 q) 1 3 (meaning1568 q) (meaning1578 q) (meaning1583 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1448 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1578 = false ∨ valuation q 1583 = true := counterClause1448 (baseVal q)

theorem counterClause1449 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1584 = true := by
  have hs : count1580 q = (countLit q [-31, -32, -34, -39]) + (countLit q [-41, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39]) (l₂ := [-41, -42, -44, -45])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1579)) (literal (valuationOf q) (1584)) (countLit q [-31, -32, -34, -39]) (countLit q [-41, -42, -44, -45]) (count1580 q) 1 4 (meaning1568 q) (meaning1579 q) (meaning1584 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1449 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1579 = false ∨ valuation q 1584 = true := counterClause1449 (baseVal q)

theorem counterClause1450 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1581 = true := by
  have hs : count1580 q = (countLit q [-31, -32, -34, -39]) + (countLit q [-41, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39]) (l₂ := [-41, -42, -44, -45])
  have hm := merge_left (literal (valuationOf q) (1569)) (literal (valuationOf q) (1581)) (countLit q [-31, -32, -34, -39]) (countLit q [-41, -42, -44, -45]) (count1580 q) 2 (meaning1569 q) (meaning1581 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1450 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1581 = true := counterClause1450 (baseVal q)

theorem counterClause1451 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1582 = true := by
  have hs : count1580 q = (countLit q [-31, -32, -34, -39]) + (countLit q [-41, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39]) (l₂ := [-41, -42, -44, -45])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1582)) (countLit q [-31, -32, -34, -39]) (countLit q [-41, -42, -44, -45]) (count1580 q) 2 1 (meaning1569 q) (meaning1576 q) (meaning1582 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1451 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1576 = false ∨ valuation q 1582 = true := counterClause1451 (baseVal q)

theorem counterClause1452 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1583 = true := by
  have hs : count1580 q = (countLit q [-31, -32, -34, -39]) + (countLit q [-41, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39]) (l₂ := [-41, -42, -44, -45])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1583)) (countLit q [-31, -32, -34, -39]) (countLit q [-41, -42, -44, -45]) (count1580 q) 2 2 (meaning1569 q) (meaning1577 q) (meaning1583 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1452 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1577 = false ∨ valuation q 1583 = true := counterClause1452 (baseVal q)

theorem counterClause1453 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1584 = true := by
  have hs : count1580 q = (countLit q [-31, -32, -34, -39]) + (countLit q [-41, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39]) (l₂ := [-41, -42, -44, -45])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1578)) (literal (valuationOf q) (1584)) (countLit q [-31, -32, -34, -39]) (countLit q [-41, -42, -44, -45]) (count1580 q) 2 3 (meaning1569 q) (meaning1578 q) (meaning1584 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1453 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1578 = false ∨ valuation q 1584 = true := counterClause1453 (baseVal q)

theorem counterClause1454 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1585 = true := by
  have hs : count1580 q = (countLit q [-31, -32, -34, -39]) + (countLit q [-41, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39]) (l₂ := [-41, -42, -44, -45])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1579)) (literal (valuationOf q) (1585)) (countLit q [-31, -32, -34, -39]) (countLit q [-41, -42, -44, -45]) (count1580 q) 2 4 (meaning1569 q) (meaning1579 q) (meaning1585 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1454 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1579 = false ∨ valuation q 1585 = true := counterClause1454 (baseVal q)

theorem counterClause1455 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1582 = true := by
  have hs : count1580 q = (countLit q [-31, -32, -34, -39]) + (countLit q [-41, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39]) (l₂ := [-41, -42, -44, -45])
  have hm := merge_left (literal (valuationOf q) (1570)) (literal (valuationOf q) (1582)) (countLit q [-31, -32, -34, -39]) (countLit q [-41, -42, -44, -45]) (count1580 q) 3 (meaning1570 q) (meaning1582 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1455 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1582 = true := counterClause1455 (baseVal q)

theorem counterClause1456 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1583 = true := by
  have hs : count1580 q = (countLit q [-31, -32, -34, -39]) + (countLit q [-41, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39]) (l₂ := [-41, -42, -44, -45])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1583)) (countLit q [-31, -32, -34, -39]) (countLit q [-41, -42, -44, -45]) (count1580 q) 3 1 (meaning1570 q) (meaning1576 q) (meaning1583 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1456 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1576 = false ∨ valuation q 1583 = true := counterClause1456 (baseVal q)

theorem counterClause1457 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1584 = true := by
  have hs : count1580 q = (countLit q [-31, -32, -34, -39]) + (countLit q [-41, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39]) (l₂ := [-41, -42, -44, -45])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1584)) (countLit q [-31, -32, -34, -39]) (countLit q [-41, -42, -44, -45]) (count1580 q) 3 2 (meaning1570 q) (meaning1577 q) (meaning1584 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1457 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1577 = false ∨ valuation q 1584 = true := counterClause1457 (baseVal q)

theorem counterClause1458 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1585 = true := by
  have hs : count1580 q = (countLit q [-31, -32, -34, -39]) + (countLit q [-41, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39]) (l₂ := [-41, -42, -44, -45])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1578)) (literal (valuationOf q) (1585)) (countLit q [-31, -32, -34, -39]) (countLit q [-41, -42, -44, -45]) (count1580 q) 3 3 (meaning1570 q) (meaning1578 q) (meaning1585 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1458 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1578 = false ∨ valuation q 1585 = true := counterClause1458 (baseVal q)

theorem counterClause1459 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1585 = true := by
  have hs : count1580 q = (countLit q [-31, -32, -34, -39]) + (countLit q [-41, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39]) (l₂ := [-41, -42, -44, -45])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1585)) (countLit q [-31, -32, -34, -39]) (countLit q [-41, -42, -44, -45]) (count1580 q) 4 2 (meaning1571 q) (meaning1577 q) (meaning1585 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1459 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1577 = false ∨ valuation q 1585 = true := counterClause1459 (baseVal q)

theorem counterClause1460 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1586 = true := by
  have hs : count1580 q = (countLit q [-31, -32, -34, -39]) + (countLit q [-41, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39]) (l₂ := [-41, -42, -44, -45])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1578)) (literal (valuationOf q) (1586)) (countLit q [-31, -32, -34, -39]) (countLit q [-41, -42, -44, -45]) (count1580 q) 4 3 (meaning1571 q) (meaning1578 q) (meaning1586 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1460 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1578 = false ∨ valuation q 1586 = true := counterClause1460 (baseVal q)

theorem counterClause1461 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 1588 = true := by
  have hs : count1588 q = (countLit q [-46]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-47])
  have hm := merge_right (literal (valuationOf q) (-47)) (literal (valuationOf q) (1588)) (countLit q [-46]) (countLit q [-47]) (count1588 q) 1 (meaningNeg47 q) (meaning1588 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1461 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 1588 = true := counterClause1461 (baseVal q)

theorem counterClause1462 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1588 = true := by
  have hs : count1588 q = (countLit q [-46]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-47])
  have hm := merge_left (literal (valuationOf q) (-46)) (literal (valuationOf q) (1588)) (countLit q [-46]) (countLit q [-47]) (count1588 q) 1 (meaningNeg46 q) (meaning1588 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1462 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1588 = true := counterClause1462 (baseVal q)

theorem counterClause1463 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 47 = true ∨ valuationOf q 1589 = true := by
  have hs : count1588 q = (countLit q [-46]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-47])
  have hm := merge_two (literal (valuationOf q) (-46)) (literal (valuationOf q) (-47)) (literal (valuationOf q) (1589)) (countLit q [-46]) (countLit q [-47]) (count1588 q) 1 1 (meaningNeg46 q) (meaningNeg47 q) (meaning1589 q) hs
  change (! (valuationOf q 46)) = false ∨ (! (valuationOf q 47)) = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1463 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 47 = true ∨ valuation q 1589 = true := counterClause1463 (baseVal q)

theorem counterClause1464 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 1590 = true := by
  have hs : count1590 q = (countLit q [-50]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-51])
  have hm := merge_right (literal (valuationOf q) (-51)) (literal (valuationOf q) (1590)) (countLit q [-50]) (countLit q [-51]) (count1590 q) 1 (meaningNeg51 q) (meaning1590 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1464 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 1590 = true := counterClause1464 (baseVal q)

theorem counterClause1465 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 1590 = true := by
  have hs : count1590 q = (countLit q [-50]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-51])
  have hm := merge_left (literal (valuationOf q) (-50)) (literal (valuationOf q) (1590)) (countLit q [-50]) (countLit q [-51]) (count1590 q) 1 (meaningNeg50 q) (meaning1590 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1465 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 1590 = true := counterClause1465 (baseVal q)

theorem counterClause1466 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 51 = true ∨ valuationOf q 1591 = true := by
  have hs : count1590 q = (countLit q [-50]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-51])
  have hm := merge_two (literal (valuationOf q) (-50)) (literal (valuationOf q) (-51)) (literal (valuationOf q) (1591)) (countLit q [-50]) (countLit q [-51]) (count1590 q) 1 1 (meaningNeg50 q) (meaningNeg51 q) (meaning1591 q) hs
  change (! (valuationOf q 50)) = false ∨ (! (valuationOf q 51)) = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1466 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 51 = true ∨ valuation q 1591 = true := counterClause1466 (baseVal q)

theorem counterClause1467 (q : Nat → Bool) : valuationOf q 1590 = false ∨ valuationOf q 1592 = true := by
  have hs : count1592 q = (countLit q [-46, -47]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-50, -51])
  have hm := merge_right (literal (valuationOf q) (1590)) (literal (valuationOf q) (1592)) (countLit q [-46, -47]) (countLit q [-50, -51]) (count1592 q) 1 (meaning1590 q) (meaning1592 q) hs
  change valuationOf q 1590 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1467 (q : Snake 81) (h : Conditions q) : valuation q 1590 = false ∨ valuation q 1592 = true := counterClause1467 (baseVal q)

theorem counterClause1468 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1593 = true := by
  have hs : count1592 q = (countLit q [-46, -47]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-50, -51])
  have hm := merge_right (literal (valuationOf q) (1591)) (literal (valuationOf q) (1593)) (countLit q [-46, -47]) (countLit q [-50, -51]) (count1592 q) 2 (meaning1591 q) (meaning1593 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1468 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1593 = true := counterClause1468 (baseVal q)

theorem counterClause1469 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1592 = true := by
  have hs : count1592 q = (countLit q [-46, -47]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-50, -51])
  have hm := merge_left (literal (valuationOf q) (1588)) (literal (valuationOf q) (1592)) (countLit q [-46, -47]) (countLit q [-50, -51]) (count1592 q) 1 (meaning1588 q) (meaning1592 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1469 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1592 = true := counterClause1469 (baseVal q)

theorem counterClause1470 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1593 = true := by
  have hs : count1592 q = (countLit q [-46, -47]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-50, -51])
  have hm := merge_two (literal (valuationOf q) (1588)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1593)) (countLit q [-46, -47]) (countLit q [-50, -51]) (count1592 q) 1 1 (meaning1588 q) (meaning1590 q) (meaning1593 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1470 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1590 = false ∨ valuation q 1593 = true := counterClause1470 (baseVal q)

theorem counterClause1471 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1594 = true := by
  have hs : count1592 q = (countLit q [-46, -47]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-50, -51])
  have hm := merge_two (literal (valuationOf q) (1588)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1594)) (countLit q [-46, -47]) (countLit q [-50, -51]) (count1592 q) 1 2 (meaning1588 q) (meaning1591 q) (meaning1594 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1471 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1591 = false ∨ valuation q 1594 = true := counterClause1471 (baseVal q)

theorem counterClause1472 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1593 = true := by
  have hs : count1592 q = (countLit q [-46, -47]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-50, -51])
  have hm := merge_left (literal (valuationOf q) (1589)) (literal (valuationOf q) (1593)) (countLit q [-46, -47]) (countLit q [-50, -51]) (count1592 q) 2 (meaning1589 q) (meaning1593 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1472 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1593 = true := counterClause1472 (baseVal q)

theorem block45 (q : Snake 81) (h : Conditions q) : B112E089.Block45 (valuation q) :=
  ⟨clause1441 q h, clause1442 q h, clause1443 q h, clause1444 q h, clause1445 q h, clause1446 q h, clause1447 q h, clause1448 q h, clause1449 q h, clause1450 q h, clause1451 q h, clause1452 q h, clause1453 q h, clause1454 q h, clause1455 q h, clause1456 q h, clause1457 q h, clause1458 q h, clause1459 q h, clause1460 q h, clause1461 q h, clause1462 q h, clause1463 q h, clause1464 q h, clause1465 q h, clause1466 q h, clause1467 q h, clause1468 q h, clause1469 q h, clause1470 q h, clause1471 q h, clause1472 q h⟩

end
end Snake9.Regrowth.E112089
