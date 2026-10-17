import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec45 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1441 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1611 = true := by
  have hs : count1608 q = (countLit q [-48, -49, -52, -54]) + (countLit q [-56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -52, -54]) (l₂ := [-56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1611)) (countLit q [-48, -49, -52, -54]) (countLit q [-56, -59, -60, -61]) (count1608 q) 2 2 (meaning1597 q) (meaning1605 q) (meaning1611 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1441 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1605 = false ∨ valuation q 1611 = true := counterClause1441 (baseVal q)

theorem counterClause1442 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1612 = true := by
  have hs : count1608 q = (countLit q [-48, -49, -52, -54]) + (countLit q [-56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -52, -54]) (l₂ := [-56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1612)) (countLit q [-48, -49, -52, -54]) (countLit q [-56, -59, -60, -61]) (count1608 q) 2 3 (meaning1597 q) (meaning1606 q) (meaning1612 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1442 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1606 = false ∨ valuation q 1612 = true := counterClause1442 (baseVal q)

theorem counterClause1443 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1613 = true := by
  have hs : count1608 q = (countLit q [-48, -49, -52, -54]) + (countLit q [-56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -52, -54]) (l₂ := [-56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1613)) (countLit q [-48, -49, -52, -54]) (countLit q [-56, -59, -60, -61]) (count1608 q) 2 4 (meaning1597 q) (meaning1607 q) (meaning1613 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1443 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1607 = false ∨ valuation q 1613 = true := counterClause1443 (baseVal q)

theorem counterClause1444 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1610 = true := by
  have hs : count1608 q = (countLit q [-48, -49, -52, -54]) + (countLit q [-56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -52, -54]) (l₂ := [-56, -59, -60, -61])
  have hm := merge_left (literal (valuationOf q) (1598)) (literal (valuationOf q) (1610)) (countLit q [-48, -49, -52, -54]) (countLit q [-56, -59, -60, -61]) (count1608 q) 3 (meaning1598 q) (meaning1610 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1444 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1610 = true := counterClause1444 (baseVal q)

theorem counterClause1445 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1611 = true := by
  have hs : count1608 q = (countLit q [-48, -49, -52, -54]) + (countLit q [-56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -52, -54]) (l₂ := [-56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1611)) (countLit q [-48, -49, -52, -54]) (countLit q [-56, -59, -60, -61]) (count1608 q) 3 1 (meaning1598 q) (meaning1604 q) (meaning1611 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1445 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1604 = false ∨ valuation q 1611 = true := counterClause1445 (baseVal q)

theorem counterClause1446 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1612 = true := by
  have hs : count1608 q = (countLit q [-48, -49, -52, -54]) + (countLit q [-56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -52, -54]) (l₂ := [-56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1612)) (countLit q [-48, -49, -52, -54]) (countLit q [-56, -59, -60, -61]) (count1608 q) 3 2 (meaning1598 q) (meaning1605 q) (meaning1612 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1446 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1605 = false ∨ valuation q 1612 = true := counterClause1446 (baseVal q)

theorem counterClause1447 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1613 = true := by
  have hs : count1608 q = (countLit q [-48, -49, -52, -54]) + (countLit q [-56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -52, -54]) (l₂ := [-56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1613)) (countLit q [-48, -49, -52, -54]) (countLit q [-56, -59, -60, -61]) (count1608 q) 3 3 (meaning1598 q) (meaning1606 q) (meaning1613 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1447 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1606 = false ∨ valuation q 1613 = true := counterClause1447 (baseVal q)

theorem counterClause1448 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1611 = true := by
  have hs : count1608 q = (countLit q [-48, -49, -52, -54]) + (countLit q [-56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -52, -54]) (l₂ := [-56, -59, -60, -61])
  have hm := merge_left (literal (valuationOf q) (1599)) (literal (valuationOf q) (1611)) (countLit q [-48, -49, -52, -54]) (countLit q [-56, -59, -60, -61]) (count1608 q) 4 (meaning1599 q) (meaning1611 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1448 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1611 = true := counterClause1448 (baseVal q)

theorem counterClause1449 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1612 = true := by
  have hs : count1608 q = (countLit q [-48, -49, -52, -54]) + (countLit q [-56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -52, -54]) (l₂ := [-56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1604)) (literal (valuationOf q) (1612)) (countLit q [-48, -49, -52, -54]) (countLit q [-56, -59, -60, -61]) (count1608 q) 4 1 (meaning1599 q) (meaning1604 q) (meaning1612 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1604 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1449 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1604 = false ∨ valuation q 1612 = true := counterClause1449 (baseVal q)

theorem counterClause1450 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1618 = true := by
  have hs : count1616 q = (countLit q [-33, -35, -37, -40, -41, -44, -45]) + (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -40, -41, -44, -45]) (l₂ := [-48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_right (literal (valuationOf q) (1610)) (literal (valuationOf q) (1618)) (countLit q [-33, -35, -37, -40, -41, -44, -45]) (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) (count1616 q) 3 (meaning1610 q) (meaning1618 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1450 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1618 = true := counterClause1450 (baseVal q)

theorem counterClause1451 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1619 = true := by
  have hs : count1616 q = (countLit q [-33, -35, -37, -40, -41, -44, -45]) + (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -40, -41, -44, -45]) (l₂ := [-48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_right (literal (valuationOf q) (1611)) (literal (valuationOf q) (1619)) (countLit q [-33, -35, -37, -40, -41, -44, -45]) (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) (count1616 q) 4 (meaning1611 q) (meaning1619 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1451 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1619 = true := counterClause1451 (baseVal q)

theorem counterClause1452 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1620 = true := by
  have hs : count1616 q = (countLit q [-33, -35, -37, -40, -41, -44, -45]) + (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -40, -41, -44, -45]) (l₂ := [-48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_right (literal (valuationOf q) (1612)) (literal (valuationOf q) (1620)) (countLit q [-33, -35, -37, -40, -41, -44, -45]) (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) (count1616 q) 5 (meaning1612 q) (meaning1620 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1452 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1620 = true := counterClause1452 (baseVal q)

theorem counterClause1453 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1621 = true := by
  have hs : count1616 q = (countLit q [-33, -35, -37, -40, -41, -44, -45]) + (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -40, -41, -44, -45]) (l₂ := [-48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_right (literal (valuationOf q) (1613)) (literal (valuationOf q) (1621)) (countLit q [-33, -35, -37, -40, -41, -44, -45]) (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) (count1616 q) 6 (meaning1613 q) (meaning1621 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1453 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1621 = true := counterClause1453 (baseVal q)

theorem counterClause1454 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1617 = true := by
  have hs : count1616 q = (countLit q [-33, -35, -37, -40, -41, -44, -45]) + (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -40, -41, -44, -45]) (l₂ := [-48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1617)) (countLit q [-33, -35, -37, -40, -41, -44, -45]) (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) (count1616 q) 1 1 (meaning1585 q) (meaning1608 q) (meaning1617 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1454 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1608 = false ∨ valuation q 1617 = true := counterClause1454 (baseVal q)

theorem counterClause1455 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1618 = true := by
  have hs : count1616 q = (countLit q [-33, -35, -37, -40, -41, -44, -45]) + (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -40, -41, -44, -45]) (l₂ := [-48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1618)) (countLit q [-33, -35, -37, -40, -41, -44, -45]) (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) (count1616 q) 1 2 (meaning1585 q) (meaning1609 q) (meaning1618 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1455 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1609 = false ∨ valuation q 1618 = true := counterClause1455 (baseVal q)

theorem counterClause1456 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1619 = true := by
  have hs : count1616 q = (countLit q [-33, -35, -37, -40, -41, -44, -45]) + (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -40, -41, -44, -45]) (l₂ := [-48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1619)) (countLit q [-33, -35, -37, -40, -41, -44, -45]) (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) (count1616 q) 1 3 (meaning1585 q) (meaning1610 q) (meaning1619 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1456 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1610 = false ∨ valuation q 1619 = true := counterClause1456 (baseVal q)

theorem counterClause1457 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1620 = true := by
  have hs : count1616 q = (countLit q [-33, -35, -37, -40, -41, -44, -45]) + (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -40, -41, -44, -45]) (l₂ := [-48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1620)) (countLit q [-33, -35, -37, -40, -41, -44, -45]) (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) (count1616 q) 1 4 (meaning1585 q) (meaning1611 q) (meaning1620 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1457 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1611 = false ∨ valuation q 1620 = true := counterClause1457 (baseVal q)

theorem counterClause1458 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1621 = true := by
  have hs : count1616 q = (countLit q [-33, -35, -37, -40, -41, -44, -45]) + (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -40, -41, -44, -45]) (l₂ := [-48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1621)) (countLit q [-33, -35, -37, -40, -41, -44, -45]) (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) (count1616 q) 1 5 (meaning1585 q) (meaning1612 q) (meaning1621 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1458 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1612 = false ∨ valuation q 1621 = true := counterClause1458 (baseVal q)

theorem counterClause1459 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1618 = true := by
  have hs : count1616 q = (countLit q [-33, -35, -37, -40, -41, -44, -45]) + (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -40, -41, -44, -45]) (l₂ := [-48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1618)) (countLit q [-33, -35, -37, -40, -41, -44, -45]) (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) (count1616 q) 2 1 (meaning1586 q) (meaning1608 q) (meaning1618 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1459 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1608 = false ∨ valuation q 1618 = true := counterClause1459 (baseVal q)

theorem counterClause1460 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1619 = true := by
  have hs : count1616 q = (countLit q [-33, -35, -37, -40, -41, -44, -45]) + (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -40, -41, -44, -45]) (l₂ := [-48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1619)) (countLit q [-33, -35, -37, -40, -41, -44, -45]) (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) (count1616 q) 2 2 (meaning1586 q) (meaning1609 q) (meaning1619 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1460 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1609 = false ∨ valuation q 1619 = true := counterClause1460 (baseVal q)

theorem counterClause1461 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1620 = true := by
  have hs : count1616 q = (countLit q [-33, -35, -37, -40, -41, -44, -45]) + (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -40, -41, -44, -45]) (l₂ := [-48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1620)) (countLit q [-33, -35, -37, -40, -41, -44, -45]) (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) (count1616 q) 2 3 (meaning1586 q) (meaning1610 q) (meaning1620 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1461 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1610 = false ∨ valuation q 1620 = true := counterClause1461 (baseVal q)

theorem counterClause1462 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1621 = true := by
  have hs : count1616 q = (countLit q [-33, -35, -37, -40, -41, -44, -45]) + (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -40, -41, -44, -45]) (l₂ := [-48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1621)) (countLit q [-33, -35, -37, -40, -41, -44, -45]) (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) (count1616 q) 2 4 (meaning1586 q) (meaning1611 q) (meaning1621 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1462 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1611 = false ∨ valuation q 1621 = true := counterClause1462 (baseVal q)

theorem counterClause1463 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1622 = true := by
  have hs : count1616 q = (countLit q [-33, -35, -37, -40, -41, -44, -45]) + (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -40, -41, -44, -45]) (l₂ := [-48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1622)) (countLit q [-33, -35, -37, -40, -41, -44, -45]) (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) (count1616 q) 2 5 (meaning1586 q) (meaning1612 q) (meaning1622 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1463 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1612 = false ∨ valuation q 1622 = true := counterClause1463 (baseVal q)

theorem counterClause1464 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1623 = true := by
  have hs : count1616 q = (countLit q [-33, -35, -37, -40, -41, -44, -45]) + (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -40, -41, -44, -45]) (l₂ := [-48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1623)) (countLit q [-33, -35, -37, -40, -41, -44, -45]) (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) (count1616 q) 2 6 (meaning1586 q) (meaning1613 q) (meaning1623 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1464 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1613 = false ∨ valuation q 1623 = true := counterClause1464 (baseVal q)

theorem counterClause1465 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1618 = true := by
  have hs : count1616 q = (countLit q [-33, -35, -37, -40, -41, -44, -45]) + (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -40, -41, -44, -45]) (l₂ := [-48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_left (literal (valuationOf q) (1587)) (literal (valuationOf q) (1618)) (countLit q [-33, -35, -37, -40, -41, -44, -45]) (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) (count1616 q) 3 (meaning1587 q) (meaning1618 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1465 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1618 = true := counterClause1465 (baseVal q)

theorem counterClause1466 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1619 = true := by
  have hs : count1616 q = (countLit q [-33, -35, -37, -40, -41, -44, -45]) + (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -40, -41, -44, -45]) (l₂ := [-48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1587)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1619)) (countLit q [-33, -35, -37, -40, -41, -44, -45]) (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) (count1616 q) 3 1 (meaning1587 q) (meaning1608 q) (meaning1619 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1466 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1608 = false ∨ valuation q 1619 = true := counterClause1466 (baseVal q)

theorem counterClause1467 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1620 = true := by
  have hs : count1616 q = (countLit q [-33, -35, -37, -40, -41, -44, -45]) + (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -40, -41, -44, -45]) (l₂ := [-48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1587)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1620)) (countLit q [-33, -35, -37, -40, -41, -44, -45]) (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) (count1616 q) 3 2 (meaning1587 q) (meaning1609 q) (meaning1620 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1467 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1609 = false ∨ valuation q 1620 = true := counterClause1467 (baseVal q)

theorem counterClause1468 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1621 = true := by
  have hs : count1616 q = (countLit q [-33, -35, -37, -40, -41, -44, -45]) + (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -40, -41, -44, -45]) (l₂ := [-48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1587)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1621)) (countLit q [-33, -35, -37, -40, -41, -44, -45]) (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) (count1616 q) 3 3 (meaning1587 q) (meaning1610 q) (meaning1621 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1468 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1610 = false ∨ valuation q 1621 = true := counterClause1468 (baseVal q)

theorem counterClause1469 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1622 = true := by
  have hs : count1616 q = (countLit q [-33, -35, -37, -40, -41, -44, -45]) + (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -40, -41, -44, -45]) (l₂ := [-48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1587)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1622)) (countLit q [-33, -35, -37, -40, -41, -44, -45]) (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) (count1616 q) 3 4 (meaning1587 q) (meaning1611 q) (meaning1622 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1469 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1611 = false ∨ valuation q 1622 = true := counterClause1469 (baseVal q)

theorem counterClause1470 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1623 = true := by
  have hs : count1616 q = (countLit q [-33, -35, -37, -40, -41, -44, -45]) + (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -40, -41, -44, -45]) (l₂ := [-48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1587)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1623)) (countLit q [-33, -35, -37, -40, -41, -44, -45]) (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) (count1616 q) 3 5 (meaning1587 q) (meaning1612 q) (meaning1623 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1470 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1612 = false ∨ valuation q 1623 = true := counterClause1470 (baseVal q)

theorem counterClause1471 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1619 = true := by
  have hs : count1616 q = (countLit q [-33, -35, -37, -40, -41, -44, -45]) + (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -40, -41, -44, -45]) (l₂ := [-48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_left (literal (valuationOf q) (1588)) (literal (valuationOf q) (1619)) (countLit q [-33, -35, -37, -40, -41, -44, -45]) (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) (count1616 q) 4 (meaning1588 q) (meaning1619 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1471 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1619 = true := counterClause1471 (baseVal q)

theorem counterClause1472 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1620 = true := by
  have hs : count1616 q = (countLit q [-33, -35, -37, -40, -41, -44, -45]) + (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -40, -41, -44, -45]) (l₂ := [-48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1588)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1620)) (countLit q [-33, -35, -37, -40, -41, -44, -45]) (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) (count1616 q) 4 1 (meaning1588 q) (meaning1608 q) (meaning1620 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1472 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1608 = false ∨ valuation q 1620 = true := counterClause1472 (baseVal q)

theorem block45 (q : Snake 81) (h : Conditions q) : B112E105.Block45 (valuation q) :=
  ⟨clause1441 q h, clause1442 q h, clause1443 q h, clause1444 q h, clause1445 q h, clause1446 q h, clause1447 q h, clause1448 q h, clause1449 q h, clause1450 q h, clause1451 q h, clause1452 q h, clause1453 q h, clause1454 q h, clause1455 q h, clause1456 q h, clause1457 q h, clause1458 q h, clause1459 q h, clause1460 q h, clause1461 q h, clause1462 q h, clause1463 q h, clause1464 q h, clause1465 q h, clause1466 q h, clause1467 q h, clause1468 q h, clause1469 q h, clause1470 q h, clause1471 q h, clause1472 q h⟩

end
end Snake9.Regrowth.E112105
