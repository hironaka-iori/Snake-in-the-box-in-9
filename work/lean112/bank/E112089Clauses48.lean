import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec48 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1537 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1619 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1619)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 3 5 (meaning1582 q) (meaning1608 q) (meaning1619 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1537 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1608 = false ∨ valuation q 1619 = true := counterClause1537 (baseVal q)

theorem counterClause1538 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1620 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1620)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 3 6 (meaning1582 q) (meaning1609 q) (meaning1620 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1538 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1609 = false ∨ valuation q 1620 = true := counterClause1538 (baseVal q)

theorem counterClause1539 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1621 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1621)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 3 7 (meaning1582 q) (meaning1610 q) (meaning1621 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1539 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1610 = false ∨ valuation q 1621 = true := counterClause1539 (baseVal q)

theorem counterClause1540 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1615 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_left (literal (valuationOf q) (1583)) (literal (valuationOf q) (1615)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 4 (meaning1583 q) (meaning1615 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1540 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1615 = true := counterClause1540 (baseVal q)

theorem counterClause1541 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1616 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1616)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 4 1 (meaning1583 q) (meaning1604 q) (meaning1616 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1541 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1604 = false ∨ valuation q 1616 = true := counterClause1541 (baseVal q)

theorem counterClause1542 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1617 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1617)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 4 2 (meaning1583 q) (meaning1605 q) (meaning1617 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1542 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1605 = false ∨ valuation q 1617 = true := counterClause1542 (baseVal q)

theorem counterClause1543 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1618 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1618)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 4 3 (meaning1583 q) (meaning1606 q) (meaning1618 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1543 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1606 = false ∨ valuation q 1618 = true := counterClause1543 (baseVal q)

theorem counterClause1544 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1619 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1619)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 4 4 (meaning1583 q) (meaning1607 q) (meaning1619 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1544 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1607 = false ∨ valuation q 1619 = true := counterClause1544 (baseVal q)

theorem counterClause1545 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1620 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1620)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 4 5 (meaning1583 q) (meaning1608 q) (meaning1620 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1545 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1608 = false ∨ valuation q 1620 = true := counterClause1545 (baseVal q)

theorem counterClause1546 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1621 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1621)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 4 6 (meaning1583 q) (meaning1609 q) (meaning1621 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1546 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1609 = false ∨ valuation q 1621 = true := counterClause1546 (baseVal q)

theorem counterClause1547 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1616 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_left (literal (valuationOf q) (1584)) (literal (valuationOf q) (1616)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 5 (meaning1584 q) (meaning1616 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1547 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1616 = true := counterClause1547 (baseVal q)

theorem counterClause1548 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1617 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1617)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 5 1 (meaning1584 q) (meaning1604 q) (meaning1617 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1548 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1604 = false ∨ valuation q 1617 = true := counterClause1548 (baseVal q)

theorem counterClause1549 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1618 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1618)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 5 2 (meaning1584 q) (meaning1605 q) (meaning1618 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1549 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1605 = false ∨ valuation q 1618 = true := counterClause1549 (baseVal q)

theorem counterClause1550 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1619 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1619)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 5 3 (meaning1584 q) (meaning1606 q) (meaning1619 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1550 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1606 = false ∨ valuation q 1619 = true := counterClause1550 (baseVal q)

theorem counterClause1551 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1620 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1620)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 5 4 (meaning1584 q) (meaning1607 q) (meaning1620 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1551 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1607 = false ∨ valuation q 1620 = true := counterClause1551 (baseVal q)

theorem counterClause1552 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1621 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1621)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 5 5 (meaning1584 q) (meaning1608 q) (meaning1621 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1552 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1608 = false ∨ valuation q 1621 = true := counterClause1552 (baseVal q)

theorem counterClause1553 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1617 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_left (literal (valuationOf q) (1585)) (literal (valuationOf q) (1617)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 6 (meaning1585 q) (meaning1617 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1553 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1617 = true := counterClause1553 (baseVal q)

theorem counterClause1554 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1618 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1618)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 6 1 (meaning1585 q) (meaning1604 q) (meaning1618 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1554 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1604 = false ∨ valuation q 1618 = true := counterClause1554 (baseVal q)

theorem counterClause1555 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1619 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1619)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 6 2 (meaning1585 q) (meaning1605 q) (meaning1619 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1555 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1605 = false ∨ valuation q 1619 = true := counterClause1555 (baseVal q)

theorem counterClause1556 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1620 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1620)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 6 3 (meaning1585 q) (meaning1606 q) (meaning1620 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1556 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1606 = false ∨ valuation q 1620 = true := counterClause1556 (baseVal q)

theorem counterClause1557 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1621 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1621)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 6 4 (meaning1585 q) (meaning1607 q) (meaning1621 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1557 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1607 = false ∨ valuation q 1621 = true := counterClause1557 (baseVal q)

theorem counterClause1558 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1618 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_left (literal (valuationOf q) (1586)) (literal (valuationOf q) (1618)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 7 (meaning1586 q) (meaning1618 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1558 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1618 = true := counterClause1558 (baseVal q)

theorem counterClause1559 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1621 = true := by
  have hs : count1612 q = (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) + (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-31, -32, -34, -39, -41, -42, -44, -45]) (l₂ := [-46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1621)) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45]) (countLit q [-46, -47, -50, -51, -54, -56, -57, -61]) (count1612 q) 7 3 (meaning1586 q) (meaning1606 q) (meaning1621 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1559 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1606 = false ∨ valuation q 1621 = true := counterClause1559 (baseVal q)

theorem counterClause1560 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1635 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1551)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1635)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 3 5 (meaning1551 q) (meaning1616 q) (meaning1635 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1560 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1616 = false ∨ valuation q 1635 = true := counterClause1560 (baseVal q)

theorem counterClause1561 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1636 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1551)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1636)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 3 6 (meaning1551 q) (meaning1617 q) (meaning1636 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1561 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1617 = false ∨ valuation q 1636 = true := counterClause1561 (baseVal q)

theorem counterClause1562 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1637 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1551)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1637)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 3 7 (meaning1551 q) (meaning1618 q) (meaning1637 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1562 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1618 = false ∨ valuation q 1637 = true := counterClause1562 (baseVal q)

theorem counterClause1563 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1638 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1551)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1638)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 3 8 (meaning1551 q) (meaning1619 q) (meaning1638 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1563 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1619 = false ∨ valuation q 1638 = true := counterClause1563 (baseVal q)

theorem counterClause1564 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1639 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1551)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1639)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 3 9 (meaning1551 q) (meaning1620 q) (meaning1639 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1564 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1620 = false ∨ valuation q 1639 = true := counterClause1564 (baseVal q)

theorem counterClause1565 (q : Nat → Bool) : valuationOf q 1552 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1633 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1552)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1633)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 4 2 (meaning1552 q) (meaning1613 q) (meaning1633 q) hs
  change valuationOf q 1552 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1565 (q : Snake 81) (h : Conditions q) : valuation q 1552 = false ∨ valuation q 1613 = false ∨ valuation q 1633 = true := counterClause1565 (baseVal q)

theorem counterClause1566 (q : Nat → Bool) : valuationOf q 1552 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1634 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1552)) (literal (valuationOf q) (1614)) (literal (valuationOf q) (1634)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 4 3 (meaning1552 q) (meaning1614 q) (meaning1634 q) hs
  change valuationOf q 1552 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1566 (q : Snake 81) (h : Conditions q) : valuation q 1552 = false ∨ valuation q 1614 = false ∨ valuation q 1634 = true := counterClause1566 (baseVal q)

theorem counterClause1567 (q : Nat → Bool) : valuationOf q 1552 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1635 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1552)) (literal (valuationOf q) (1615)) (literal (valuationOf q) (1635)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 4 4 (meaning1552 q) (meaning1615 q) (meaning1635 q) hs
  change valuationOf q 1552 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1567 (q : Snake 81) (h : Conditions q) : valuation q 1552 = false ∨ valuation q 1615 = false ∨ valuation q 1635 = true := counterClause1567 (baseVal q)

theorem counterClause1568 (q : Nat → Bool) : valuationOf q 1552 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1636 = true := by
  have hs : count1628 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) + (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (l₂ := [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61])
  have hm := merge_two (literal (valuationOf q) (1552)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1636)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29]) (countLit q [-31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (count1628 q) 4 5 (meaning1552 q) (meaning1616 q) (meaning1636 q) hs
  change valuationOf q 1552 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1568 (q : Snake 81) (h : Conditions q) : valuation q 1552 = false ∨ valuation q 1616 = false ∨ valuation q 1636 = true := counterClause1568 (baseVal q)

theorem block48 (q : Snake 81) (h : Conditions q) : B112E089.Block48 (valuation q) :=
  ⟨clause1537 q h, clause1538 q h, clause1539 q h, clause1540 q h, clause1541 q h, clause1542 q h, clause1543 q h, clause1544 q h, clause1545 q h, clause1546 q h, clause1547 q h, clause1548 q h, clause1549 q h, clause1550 q h, clause1551 q h, clause1552 q h, clause1553 q h, clause1554 q h, clause1555 q h, clause1556 q h, clause1557 q h, clause1558 q h, clause1559 q h, clause1560 q h, clause1561 q h, clause1562 q h, clause1563 q h, clause1564 q h, clause1565 q h, clause1566 q h, clause1567 q h, clause1568 q h⟩

end
end Snake9.Regrowth.E112089
