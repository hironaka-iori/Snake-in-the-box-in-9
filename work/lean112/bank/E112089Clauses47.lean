import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec47 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1505 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1608 = true := by
  have hs : count1604 q = (countLit q [-46, -47, -50, -51]) + (countLit q [-54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -51]) (l₂ := [-54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1608)) (countLit q [-46, -47, -50, -51]) (countLit q [-54, -56, -57, -61]) (count1604 q) 3 2 (meaning1594 q) (meaning1601 q) (meaning1608 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1505 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1601 = false ∨ valuation q 1608 = true := counterClause1505 (baseVal q)

theorem counterClause1506 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1609 = true := by
  have hs : count1604 q = (countLit q [-46, -47, -50, -51]) + (countLit q [-54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -51]) (l₂ := [-54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1609)) (countLit q [-46, -47, -50, -51]) (countLit q [-54, -56, -57, -61]) (count1604 q) 3 3 (meaning1594 q) (meaning1602 q) (meaning1609 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1506 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1602 = false ∨ valuation q 1609 = true := counterClause1506 (baseVal q)

theorem counterClause1507 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1610 = true := by
  have hs : count1604 q = (countLit q [-46, -47, -50, -51]) + (countLit q [-54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -51]) (l₂ := [-54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1610)) (countLit q [-46, -47, -50, -51]) (countLit q [-54, -56, -57, -61]) (count1604 q) 3 4 (meaning1594 q) (meaning1603 q) (meaning1610 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1507 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1603 = false ∨ valuation q 1610 = true := counterClause1507 (baseVal q)

theorem counterClause1508 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1607 = true := by
  have hs : count1604 q = (countLit q [-46, -47, -50, -51]) + (countLit q [-54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -51]) (l₂ := [-54, -56, -57, -61])
  have hm := merge_left (literal (valuationOf q) (1595)) (literal (valuationOf q) (1607)) (countLit q [-46, -47, -50, -51]) (countLit q [-54, -56, -57, -61]) (count1604 q) 4 (meaning1595 q) (meaning1607 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1508 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1607 = true := counterClause1508 (baseVal q)

theorem counterClause1509 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1608 = true := by
  have hs : count1604 q = (countLit q [-46, -47, -50, -51]) + (countLit q [-54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -51]) (l₂ := [-54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1608)) (countLit q [-46, -47, -50, -51]) (countLit q [-54, -56, -57, -61]) (count1604 q) 4 1 (meaning1595 q) (meaning1600 q) (meaning1608 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1509 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1600 = false ∨ valuation q 1608 = true := counterClause1509 (baseVal q)

theorem counterClause1510 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1609 = true := by
  have hs : count1604 q = (countLit q [-46, -47, -50, -51]) + (countLit q [-54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -51]) (l₂ := [-54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1609)) (countLit q [-46, -47, -50, -51]) (countLit q [-54, -56, -57, -61]) (count1604 q) 4 2 (meaning1595 q) (meaning1601 q) (meaning1609 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1510 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1601 = false ∨ valuation q 1609 = true := counterClause1510 (baseVal q)

theorem counterClause1511 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1610 = true := by
  have hs : count1604 q = (countLit q [-46, -47, -50, -51]) + (countLit q [-54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -50, -51]) (l₂ := [-54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1610)) (countLit q [-46, -47, -50, -51]) (countLit q [-54, -56, -57, -61]) (count1604 q) 4 3 (meaning1595 q) (meaning1602 q) (meaning1610 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1511 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1602 = false ∨ valuation q 1610 = true := counterClause1511 (baseVal q)

theorem counterClause1512 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1613 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_right (literal (valuationOf q) (1605)) (literal (valuationOf q) (1613)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 2 (meaning1605 q) (meaning1613 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1512 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1613 = true := counterClause1512 (baseVal q)

theorem counterClause1513 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1614 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_right (literal (valuationOf q) (1606)) (literal (valuationOf q) (1614)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 3 (meaning1606 q) (meaning1614 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1513 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1614 = true := counterClause1513 (baseVal q)

theorem counterClause1514 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1615 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_right (literal (valuationOf q) (1607)) (literal (valuationOf q) (1615)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 4 (meaning1607 q) (meaning1615 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1514 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1615 = true := counterClause1514 (baseVal q)

theorem counterClause1515 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1616 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_right (literal (valuationOf q) (1608)) (literal (valuationOf q) (1616)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 5 (meaning1608 q) (meaning1616 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1515 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1616 = true := counterClause1515 (baseVal q)

theorem counterClause1516 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1617 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_right (literal (valuationOf q) (1609)) (literal (valuationOf q) (1617)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 6 (meaning1609 q) (meaning1617 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1516 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1617 = true := counterClause1516 (baseVal q)

theorem counterClause1517 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1613 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1613)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 1 1 (meaning1580 q) (meaning1604 q) (meaning1613 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1517 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1604 = false ∨ valuation q 1613 = true := counterClause1517 (baseVal q)

theorem counterClause1518 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1614 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1614)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 1 2 (meaning1580 q) (meaning1605 q) (meaning1614 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1518 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1605 = false ∨ valuation q 1614 = true := counterClause1518 (baseVal q)

theorem counterClause1519 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1615 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1615)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 1 3 (meaning1580 q) (meaning1606 q) (meaning1615 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1519 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1606 = false ∨ valuation q 1615 = true := counterClause1519 (baseVal q)

theorem counterClause1520 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1616 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1616)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 1 4 (meaning1580 q) (meaning1607 q) (meaning1616 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1520 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1607 = false ∨ valuation q 1616 = true := counterClause1520 (baseVal q)

theorem counterClause1521 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1617 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1617)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 1 5 (meaning1580 q) (meaning1608 q) (meaning1617 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1521 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1608 = false ∨ valuation q 1617 = true := counterClause1521 (baseVal q)

theorem counterClause1522 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1618 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1618)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 1 6 (meaning1580 q) (meaning1609 q) (meaning1618 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1522 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1609 = false ∨ valuation q 1618 = true := counterClause1522 (baseVal q)

theorem counterClause1523 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1619 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1619)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 1 7 (meaning1580 q) (meaning1610 q) (meaning1619 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1523 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1610 = false ∨ valuation q 1619 = true := counterClause1523 (baseVal q)

theorem counterClause1524 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1613 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_left (literal (valuationOf q) (1581)) (literal (valuationOf q) (1613)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 2 (meaning1581 q) (meaning1613 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1524 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1613 = true := counterClause1524 (baseVal q)

theorem counterClause1525 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1614 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1581)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1614)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 2 1 (meaning1581 q) (meaning1604 q) (meaning1614 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1525 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1604 = false ∨ valuation q 1614 = true := counterClause1525 (baseVal q)

theorem counterClause1526 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1615 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1581)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1615)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 2 2 (meaning1581 q) (meaning1605 q) (meaning1615 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1526 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1605 = false ∨ valuation q 1615 = true := counterClause1526 (baseVal q)

theorem counterClause1527 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1616 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1581)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1616)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 2 3 (meaning1581 q) (meaning1606 q) (meaning1616 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1527 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1606 = false ∨ valuation q 1616 = true := counterClause1527 (baseVal q)

theorem counterClause1528 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1617 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1581)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1617)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 2 4 (meaning1581 q) (meaning1607 q) (meaning1617 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1528 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1607 = false ∨ valuation q 1617 = true := counterClause1528 (baseVal q)

theorem counterClause1529 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1618 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1581)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1618)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 2 5 (meaning1581 q) (meaning1608 q) (meaning1618 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1529 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1608 = false ∨ valuation q 1618 = true := counterClause1529 (baseVal q)

theorem counterClause1530 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1619 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1581)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1619)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 2 6 (meaning1581 q) (meaning1609 q) (meaning1619 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1530 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1609 = false ∨ valuation q 1619 = true := counterClause1530 (baseVal q)

theorem counterClause1531 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1620 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1581)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1620)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 2 7 (meaning1581 q) (meaning1610 q) (meaning1620 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1531 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1610 = false ∨ valuation q 1620 = true := counterClause1531 (baseVal q)

theorem counterClause1532 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1614 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_left (literal (valuationOf q) (1582)) (literal (valuationOf q) (1614)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 3 (meaning1582 q) (meaning1614 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1532 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1614 = true := counterClause1532 (baseVal q)

theorem counterClause1533 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1615 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1615)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 3 1 (meaning1582 q) (meaning1604 q) (meaning1615 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1533 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1604 = false ∨ valuation q 1615 = true := counterClause1533 (baseVal q)

theorem counterClause1534 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1616 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1616)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 3 2 (meaning1582 q) (meaning1605 q) (meaning1616 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1534 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1605 = false ∨ valuation q 1616 = true := counterClause1534 (baseVal q)

theorem counterClause1535 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1617 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1617)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 3 3 (meaning1582 q) (meaning1606 q) (meaning1617 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1535 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1606 = false ∨ valuation q 1617 = true := counterClause1535 (baseVal q)

theorem counterClause1536 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1618 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1618)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 3 4 (meaning1582 q) (meaning1607 q) (meaning1618 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1536 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1607 = false ∨ valuation q 1618 = true := counterClause1536 (baseVal q)

theorem block47 (q : Snake 81) (h : Conditions q) : B112E089.Block47 (valuation q) :=
  ⟨clause1505 q h, clause1506 q h, clause1507 q h, clause1508 q h, clause1509 q h, clause1510 q h, clause1511 q h, clause1512 q h, clause1513 q h, clause1514 q h, clause1515 q h, clause1516 q h, clause1517 q h, clause1518 q h, clause1519 q h, clause1520 q h, clause1521 q h, clause1522 q h, clause1523 q h, clause1524 q h, clause1525 q h, clause1526 q h, clause1527 q h, clause1528 q h, clause1529 q h, clause1530 q h, clause1531 q h, clause1532 q h, clause1533 q h, clause1534 q h, clause1535 q h, clause1536 q h⟩

end
end Snake9.Regrowth.E112089
