import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec46 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1473 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1594 = true := by
  have hs : count1592 q = (countLit q [-46, -47]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-50, -51])
  have hm := merge_two (literal (valuationOf q) (1589)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1594)) (countLit q [-46, -47]) (countLit q [-50, -51]) (count1592 q) 2 1 (meaning1589 q) (meaning1590 q) (meaning1594 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1473 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1590 = false ∨ valuation q 1594 = true := counterClause1473 (baseVal q)

theorem counterClause1474 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1595 = true := by
  have hs : count1592 q = (countLit q [-46, -47]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-50, -51])
  have hm := merge_two (literal (valuationOf q) (1589)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1595)) (countLit q [-46, -47]) (countLit q [-50, -51]) (count1592 q) 2 2 (meaning1589 q) (meaning1591 q) (meaning1595 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1474 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1591 = false ∨ valuation q 1595 = true := counterClause1474 (baseVal q)

theorem counterClause1475 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1596 = true := by
  have hs : count1596 q = (countLit q [-54]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-56])
  have hm := merge_right (literal (valuationOf q) (-56)) (literal (valuationOf q) (1596)) (countLit q [-54]) (countLit q [-56]) (count1596 q) 1 (meaningNeg56 q) (meaning1596 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1475 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1596 = true := counterClause1475 (baseVal q)

theorem counterClause1476 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1596 = true := by
  have hs : count1596 q = (countLit q [-54]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-56])
  have hm := merge_left (literal (valuationOf q) (-54)) (literal (valuationOf q) (1596)) (countLit q [-54]) (countLit q [-56]) (count1596 q) 1 (meaningNeg54 q) (meaning1596 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1476 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1596 = true := counterClause1476 (baseVal q)

theorem counterClause1477 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 56 = true ∨ valuationOf q 1597 = true := by
  have hs : count1596 q = (countLit q [-54]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-56])
  have hm := merge_two (literal (valuationOf q) (-54)) (literal (valuationOf q) (-56)) (literal (valuationOf q) (1597)) (countLit q [-54]) (countLit q [-56]) (count1596 q) 1 1 (meaningNeg54 q) (meaningNeg56 q) (meaning1597 q) hs
  change (! (valuationOf q 54)) = false ∨ (! (valuationOf q 56)) = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1477 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 56 = true ∨ valuation q 1597 = true := counterClause1477 (baseVal q)

theorem counterClause1478 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 1598 = true := by
  have hs : count1598 q = (countLit q [-57]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-61])
  have hm := merge_right (literal (valuationOf q) (-61)) (literal (valuationOf q) (1598)) (countLit q [-57]) (countLit q [-61]) (count1598 q) 1 (meaningNeg61 q) (meaning1598 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1478 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1598 = true := counterClause1478 (baseVal q)

theorem counterClause1479 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1598 = true := by
  have hs : count1598 q = (countLit q [-57]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-61])
  have hm := merge_left (literal (valuationOf q) (-57)) (literal (valuationOf q) (1598)) (countLit q [-57]) (countLit q [-61]) (count1598 q) 1 (meaningNeg57 q) (meaning1598 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1479 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1598 = true := counterClause1479 (baseVal q)

theorem counterClause1480 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 61 = true ∨ valuationOf q 1599 = true := by
  have hs : count1598 q = (countLit q [-57]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-61])
  have hm := merge_two (literal (valuationOf q) (-57)) (literal (valuationOf q) (-61)) (literal (valuationOf q) (1599)) (countLit q [-57]) (countLit q [-61]) (count1598 q) 1 1 (meaningNeg57 q) (meaningNeg61 q) (meaning1599 q) hs
  change (! (valuationOf q 57)) = false ∨ (! (valuationOf q 61)) = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1480 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 61 = true ∨ valuation q 1599 = true := counterClause1480 (baseVal q)

theorem counterClause1481 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1600 = true := by
  have hs : count1600 q = (countLit q [-54, -56]) + (countLit q [-57, -61]) := List.countP_append (p := literal q) (l₁ := [-54, -56]) (l₂ := [-57, -61])
  have hm := merge_right (literal (valuationOf q) (1598)) (literal (valuationOf q) (1600)) (countLit q [-54, -56]) (countLit q [-57, -61]) (count1600 q) 1 (meaning1598 q) (meaning1600 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1481 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1600 = true := counterClause1481 (baseVal q)

theorem counterClause1482 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1601 = true := by
  have hs : count1600 q = (countLit q [-54, -56]) + (countLit q [-57, -61]) := List.countP_append (p := literal q) (l₁ := [-54, -56]) (l₂ := [-57, -61])
  have hm := merge_right (literal (valuationOf q) (1599)) (literal (valuationOf q) (1601)) (countLit q [-54, -56]) (countLit q [-57, -61]) (count1600 q) 2 (meaning1599 q) (meaning1601 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1482 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1601 = true := counterClause1482 (baseVal q)

theorem counterClause1483 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1600 = true := by
  have hs : count1600 q = (countLit q [-54, -56]) + (countLit q [-57, -61]) := List.countP_append (p := literal q) (l₁ := [-54, -56]) (l₂ := [-57, -61])
  have hm := merge_left (literal (valuationOf q) (1596)) (literal (valuationOf q) (1600)) (countLit q [-54, -56]) (countLit q [-57, -61]) (count1600 q) 1 (meaning1596 q) (meaning1600 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1483 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1600 = true := counterClause1483 (baseVal q)

theorem counterClause1484 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1601 = true := by
  have hs : count1600 q = (countLit q [-54, -56]) + (countLit q [-57, -61]) := List.countP_append (p := literal q) (l₁ := [-54, -56]) (l₂ := [-57, -61])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1598)) (literal (valuationOf q) (1601)) (countLit q [-54, -56]) (countLit q [-57, -61]) (count1600 q) 1 1 (meaning1596 q) (meaning1598 q) (meaning1601 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1484 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1598 = false ∨ valuation q 1601 = true := counterClause1484 (baseVal q)

theorem counterClause1485 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1602 = true := by
  have hs : count1600 q = (countLit q [-54, -56]) + (countLit q [-57, -61]) := List.countP_append (p := literal q) (l₁ := [-54, -56]) (l₂ := [-57, -61])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1602)) (countLit q [-54, -56]) (countLit q [-57, -61]) (count1600 q) 1 2 (meaning1596 q) (meaning1599 q) (meaning1602 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1485 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1599 = false ∨ valuation q 1602 = true := counterClause1485 (baseVal q)

theorem counterClause1486 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1601 = true := by
  have hs : count1600 q = (countLit q [-54, -56]) + (countLit q [-57, -61]) := List.countP_append (p := literal q) (l₁ := [-54, -56]) (l₂ := [-57, -61])
  have hm := merge_left (literal (valuationOf q) (1597)) (literal (valuationOf q) (1601)) (countLit q [-54, -56]) (countLit q [-57, -61]) (count1600 q) 2 (meaning1597 q) (meaning1601 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1486 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1601 = true := counterClause1486 (baseVal q)

theorem counterClause1487 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1602 = true := by
  have hs : count1600 q = (countLit q [-54, -56]) + (countLit q [-57, -61]) := List.countP_append (p := literal q) (l₁ := [-54, -56]) (l₂ := [-57, -61])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1598)) (literal (valuationOf q) (1602)) (countLit q [-54, -56]) (countLit q [-57, -61]) (count1600 q) 2 1 (meaning1597 q) (meaning1598 q) (meaning1602 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1487 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1598 = false ∨ valuation q 1602 = true := counterClause1487 (baseVal q)

theorem counterClause1488 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1603 = true := by
  have hs : count1600 q = (countLit q [-54, -56]) + (countLit q [-57, -61]) := List.countP_append (p := literal q) (l₁ := [-54, -56]) (l₂ := [-57, -61])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1603)) (countLit q [-54, -56]) (countLit q [-57, -61]) (count1600 q) 2 2 (meaning1597 q) (meaning1599 q) (meaning1603 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1488 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1599 = false ∨ valuation q 1603 = true := counterClause1488 (baseVal q)

theorem counterClause1489 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1604 = true := by
  have hs : count1604 q = (countLit q [-46, -47, -50, -51]) + (countLit q [-54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -51]) (l₂ := [-54, -56, -57, -61])
  have hm := merge_right (literal (valuationOf q) (1600)) (literal (valuationOf q) (1604)) (countLit q [-46, -47, -50, -51]) (countLit q [-54, -56, -57, -61]) (count1604 q) 1 (meaning1600 q) (meaning1604 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1489 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1604 = true := counterClause1489 (baseVal q)

theorem counterClause1490 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1605 = true := by
  have hs : count1604 q = (countLit q [-46, -47, -50, -51]) + (countLit q [-54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -51]) (l₂ := [-54, -56, -57, -61])
  have hm := merge_right (literal (valuationOf q) (1601)) (literal (valuationOf q) (1605)) (countLit q [-46, -47, -50, -51]) (countLit q [-54, -56, -57, -61]) (count1604 q) 2 (meaning1601 q) (meaning1605 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1490 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1605 = true := counterClause1490 (baseVal q)

theorem counterClause1491 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1606 = true := by
  have hs : count1604 q = (countLit q [-46, -47, -50, -51]) + (countLit q [-54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -51]) (l₂ := [-54, -56, -57, -61])
  have hm := merge_right (literal (valuationOf q) (1602)) (literal (valuationOf q) (1606)) (countLit q [-46, -47, -50, -51]) (countLit q [-54, -56, -57, -61]) (count1604 q) 3 (meaning1602 q) (meaning1606 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1491 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1606 = true := counterClause1491 (baseVal q)

theorem counterClause1492 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1607 = true := by
  have hs : count1604 q = (countLit q [-46, -47, -50, -51]) + (countLit q [-54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -51]) (l₂ := [-54, -56, -57, -61])
  have hm := merge_right (literal (valuationOf q) (1603)) (literal (valuationOf q) (1607)) (countLit q [-46, -47, -50, -51]) (countLit q [-54, -56, -57, -61]) (count1604 q) 4 (meaning1603 q) (meaning1607 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1492 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1607 = true := counterClause1492 (baseVal q)

theorem counterClause1493 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1604 = true := by
  have hs : count1604 q = (countLit q [-46, -47, -50, -51]) + (countLit q [-54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -51]) (l₂ := [-54, -56, -57, -61])
  have hm := merge_left (literal (valuationOf q) (1592)) (literal (valuationOf q) (1604)) (countLit q [-46, -47, -50, -51]) (countLit q [-54, -56, -57, -61]) (count1604 q) 1 (meaning1592 q) (meaning1604 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1493 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1604 = true := counterClause1493 (baseVal q)

theorem counterClause1494 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1605 = true := by
  have hs : count1604 q = (countLit q [-46, -47, -50, -51]) + (countLit q [-54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -51]) (l₂ := [-54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1592)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1605)) (countLit q [-46, -47, -50, -51]) (countLit q [-54, -56, -57, -61]) (count1604 q) 1 1 (meaning1592 q) (meaning1600 q) (meaning1605 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1494 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1600 = false ∨ valuation q 1605 = true := counterClause1494 (baseVal q)

theorem counterClause1495 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1606 = true := by
  have hs : count1604 q = (countLit q [-46, -47, -50, -51]) + (countLit q [-54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -51]) (l₂ := [-54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1592)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1606)) (countLit q [-46, -47, -50, -51]) (countLit q [-54, -56, -57, -61]) (count1604 q) 1 2 (meaning1592 q) (meaning1601 q) (meaning1606 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1495 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1601 = false ∨ valuation q 1606 = true := counterClause1495 (baseVal q)

theorem counterClause1496 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1607 = true := by
  have hs : count1604 q = (countLit q [-46, -47, -50, -51]) + (countLit q [-54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -51]) (l₂ := [-54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1592)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1607)) (countLit q [-46, -47, -50, -51]) (countLit q [-54, -56, -57, -61]) (count1604 q) 1 3 (meaning1592 q) (meaning1602 q) (meaning1607 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1496 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1602 = false ∨ valuation q 1607 = true := counterClause1496 (baseVal q)

theorem counterClause1497 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1608 = true := by
  have hs : count1604 q = (countLit q [-46, -47, -50, -51]) + (countLit q [-54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -51]) (l₂ := [-54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1592)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1608)) (countLit q [-46, -47, -50, -51]) (countLit q [-54, -56, -57, -61]) (count1604 q) 1 4 (meaning1592 q) (meaning1603 q) (meaning1608 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1497 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1603 = false ∨ valuation q 1608 = true := counterClause1497 (baseVal q)

theorem counterClause1498 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1605 = true := by
  have hs : count1604 q = (countLit q [-46, -47, -50, -51]) + (countLit q [-54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -51]) (l₂ := [-54, -56, -57, -61])
  have hm := merge_left (literal (valuationOf q) (1593)) (literal (valuationOf q) (1605)) (countLit q [-46, -47, -50, -51]) (countLit q [-54, -56, -57, -61]) (count1604 q) 2 (meaning1593 q) (meaning1605 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1498 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1605 = true := counterClause1498 (baseVal q)

theorem counterClause1499 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1606 = true := by
  have hs : count1604 q = (countLit q [-46, -47, -50, -51]) + (countLit q [-54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -51]) (l₂ := [-54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1606)) (countLit q [-46, -47, -50, -51]) (countLit q [-54, -56, -57, -61]) (count1604 q) 2 1 (meaning1593 q) (meaning1600 q) (meaning1606 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1499 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1600 = false ∨ valuation q 1606 = true := counterClause1499 (baseVal q)

theorem counterClause1500 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1607 = true := by
  have hs : count1604 q = (countLit q [-46, -47, -50, -51]) + (countLit q [-54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -51]) (l₂ := [-54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1607)) (countLit q [-46, -47, -50, -51]) (countLit q [-54, -56, -57, -61]) (count1604 q) 2 2 (meaning1593 q) (meaning1601 q) (meaning1607 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1500 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1601 = false ∨ valuation q 1607 = true := counterClause1500 (baseVal q)

theorem counterClause1501 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1608 = true := by
  have hs : count1604 q = (countLit q [-46, -47, -50, -51]) + (countLit q [-54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -51]) (l₂ := [-54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1608)) (countLit q [-46, -47, -50, -51]) (countLit q [-54, -56, -57, -61]) (count1604 q) 2 3 (meaning1593 q) (meaning1602 q) (meaning1608 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1501 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1602 = false ∨ valuation q 1608 = true := counterClause1501 (baseVal q)

theorem counterClause1502 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1609 = true := by
  have hs : count1604 q = (countLit q [-46, -47, -50, -51]) + (countLit q [-54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -51]) (l₂ := [-54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1609)) (countLit q [-46, -47, -50, -51]) (countLit q [-54, -56, -57, -61]) (count1604 q) 2 4 (meaning1593 q) (meaning1603 q) (meaning1609 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1502 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1603 = false ∨ valuation q 1609 = true := counterClause1502 (baseVal q)

theorem counterClause1503 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1606 = true := by
  have hs : count1604 q = (countLit q [-46, -47, -50, -51]) + (countLit q [-54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -51]) (l₂ := [-54, -56, -57, -61])
  have hm := merge_left (literal (valuationOf q) (1594)) (literal (valuationOf q) (1606)) (countLit q [-46, -47, -50, -51]) (countLit q [-54, -56, -57, -61]) (count1604 q) 3 (meaning1594 q) (meaning1606 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1503 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1606 = true := counterClause1503 (baseVal q)

theorem counterClause1504 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1607 = true := by
  have hs : count1604 q = (countLit q [-46, -47, -50, -51]) + (countLit q [-54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -51]) (l₂ := [-54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1607)) (countLit q [-46, -47, -50, -51]) (countLit q [-54, -56, -57, -61]) (count1604 q) 3 1 (meaning1594 q) (meaning1600 q) (meaning1607 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1504 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1600 = false ∨ valuation q 1607 = true := counterClause1504 (baseVal q)

theorem block46 (q : Snake 81) (h : Conditions q) : B112E089.Block46 (valuation q) :=
  ⟨clause1473 q h, clause1474 q h, clause1475 q h, clause1476 q h, clause1477 q h, clause1478 q h, clause1479 q h, clause1480 q h, clause1481 q h, clause1482 q h, clause1483 q h, clause1484 q h, clause1485 q h, clause1486 q h, clause1487 q h, clause1488 q h, clause1489 q h, clause1490 q h, clause1491 q h, clause1492 q h, clause1493 q h, clause1494 q h, clause1495 q h, clause1496 q h, clause1497 q h, clause1498 q h, clause1499 q h, clause1500 q h, clause1501 q h, clause1502 q h, clause1503 q h, clause1504 q h⟩

end
end Snake9.Regrowth.E112089
