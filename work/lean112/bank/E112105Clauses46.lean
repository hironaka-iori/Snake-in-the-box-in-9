import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec46 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1473 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1621 = true := by
  have hs : count1616 q = (countLit q [-33, -35, -37, -40, -41, -44, -45]) + (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -40, -41, -44, -45]) (l₂ := [-48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1588)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1621)) (countLit q [-33, -35, -37, -40, -41, -44, -45]) (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) (count1616 q) 4 2 (meaning1588 q) (meaning1609 q) (meaning1621 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1473 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1609 = false ∨ valuation q 1621 = true := counterClause1473 (baseVal q)

theorem counterClause1474 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1622 = true := by
  have hs : count1616 q = (countLit q [-33, -35, -37, -40, -41, -44, -45]) + (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -40, -41, -44, -45]) (l₂ := [-48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1588)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1622)) (countLit q [-33, -35, -37, -40, -41, -44, -45]) (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) (count1616 q) 4 3 (meaning1588 q) (meaning1610 q) (meaning1622 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1474 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1610 = false ∨ valuation q 1622 = true := counterClause1474 (baseVal q)

theorem counterClause1475 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1623 = true := by
  have hs : count1616 q = (countLit q [-33, -35, -37, -40, -41, -44, -45]) + (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -40, -41, -44, -45]) (l₂ := [-48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1588)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1623)) (countLit q [-33, -35, -37, -40, -41, -44, -45]) (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) (count1616 q) 4 4 (meaning1588 q) (meaning1611 q) (meaning1623 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1475 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1611 = false ∨ valuation q 1623 = true := counterClause1475 (baseVal q)

theorem counterClause1476 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1624 = true := by
  have hs : count1616 q = (countLit q [-33, -35, -37, -40, -41, -44, -45]) + (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -40, -41, -44, -45]) (l₂ := [-48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1588)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1624)) (countLit q [-33, -35, -37, -40, -41, -44, -45]) (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) (count1616 q) 4 5 (meaning1588 q) (meaning1612 q) (meaning1624 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1476 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1612 = false ∨ valuation q 1624 = true := counterClause1476 (baseVal q)

theorem counterClause1477 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1625 = true := by
  have hs : count1616 q = (countLit q [-33, -35, -37, -40, -41, -44, -45]) + (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -40, -41, -44, -45]) (l₂ := [-48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1588)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1625)) (countLit q [-33, -35, -37, -40, -41, -44, -45]) (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) (count1616 q) 4 6 (meaning1588 q) (meaning1613 q) (meaning1625 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1477 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1613 = false ∨ valuation q 1625 = true := counterClause1477 (baseVal q)

theorem counterClause1478 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1620 = true := by
  have hs : count1616 q = (countLit q [-33, -35, -37, -40, -41, -44, -45]) + (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -40, -41, -44, -45]) (l₂ := [-48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_left (literal (valuationOf q) (1589)) (literal (valuationOf q) (1620)) (countLit q [-33, -35, -37, -40, -41, -44, -45]) (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) (count1616 q) 5 (meaning1589 q) (meaning1620 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1478 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1620 = true := counterClause1478 (baseVal q)

theorem counterClause1479 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1621 = true := by
  have hs : count1616 q = (countLit q [-33, -35, -37, -40, -41, -44, -45]) + (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -40, -41, -44, -45]) (l₂ := [-48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1589)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1621)) (countLit q [-33, -35, -37, -40, -41, -44, -45]) (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) (count1616 q) 5 1 (meaning1589 q) (meaning1608 q) (meaning1621 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1479 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1608 = false ∨ valuation q 1621 = true := counterClause1479 (baseVal q)

theorem counterClause1480 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1622 = true := by
  have hs : count1616 q = (countLit q [-33, -35, -37, -40, -41, -44, -45]) + (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -40, -41, -44, -45]) (l₂ := [-48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1589)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1622)) (countLit q [-33, -35, -37, -40, -41, -44, -45]) (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) (count1616 q) 5 2 (meaning1589 q) (meaning1609 q) (meaning1622 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1480 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1609 = false ∨ valuation q 1622 = true := counterClause1480 (baseVal q)

theorem counterClause1481 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1623 = true := by
  have hs : count1616 q = (countLit q [-33, -35, -37, -40, -41, -44, -45]) + (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -40, -41, -44, -45]) (l₂ := [-48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1589)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1623)) (countLit q [-33, -35, -37, -40, -41, -44, -45]) (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) (count1616 q) 5 3 (meaning1589 q) (meaning1610 q) (meaning1623 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1481 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1610 = false ∨ valuation q 1623 = true := counterClause1481 (baseVal q)

theorem counterClause1482 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1624 = true := by
  have hs : count1616 q = (countLit q [-33, -35, -37, -40, -41, -44, -45]) + (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37, -40, -41, -44, -45]) (l₂ := [-48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1589)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1624)) (countLit q [-33, -35, -37, -40, -41, -44, -45]) (countLit q [-48, -49, -52, -54, -56, -59, -60, -61]) (count1616 q) 5 4 (meaning1589 q) (meaning1611 q) (meaning1624 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1482 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1611 = false ∨ valuation q 1624 = true := counterClause1482 (baseVal q)

theorem counterClause1483 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1638 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1622)) (literal (valuationOf q) (1638)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 1 7 (meaning1557 q) (meaning1622 q) (meaning1638 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1483 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1622 = false ∨ valuation q 1638 = true := counterClause1483 (baseVal q)

theorem counterClause1484 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1637 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1558)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1637)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 2 5 (meaning1558 q) (meaning1620 q) (meaning1637 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1484 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1620 = false ∨ valuation q 1637 = true := counterClause1484 (baseVal q)

theorem counterClause1485 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1638 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1558)) (literal (valuationOf q) (1621)) (literal (valuationOf q) (1638)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 2 6 (meaning1558 q) (meaning1621 q) (meaning1638 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1485 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1621 = false ∨ valuation q 1638 = true := counterClause1485 (baseVal q)

theorem counterClause1486 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1639 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1558)) (literal (valuationOf q) (1622)) (literal (valuationOf q) (1639)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 2 7 (meaning1558 q) (meaning1622 q) (meaning1639 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1486 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1622 = false ∨ valuation q 1639 = true := counterClause1486 (baseVal q)

theorem counterClause1487 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1636 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1636)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 3 3 (meaning1559 q) (meaning1618 q) (meaning1636 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1487 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1618 = false ∨ valuation q 1636 = true := counterClause1487 (baseVal q)

theorem counterClause1488 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1637 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1637)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 3 4 (meaning1559 q) (meaning1619 q) (meaning1637 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1488 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1619 = false ∨ valuation q 1637 = true := counterClause1488 (baseVal q)

theorem counterClause1489 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1638 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1638)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 3 5 (meaning1559 q) (meaning1620 q) (meaning1638 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1489 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1620 = false ∨ valuation q 1638 = true := counterClause1489 (baseVal q)

theorem counterClause1490 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1639 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1621)) (literal (valuationOf q) (1639)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 3 6 (meaning1559 q) (meaning1621 q) (meaning1639 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1490 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1621 = false ∨ valuation q 1639 = true := counterClause1490 (baseVal q)

theorem counterClause1491 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1640 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1622)) (literal (valuationOf q) (1640)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 3 7 (meaning1559 q) (meaning1622 q) (meaning1640 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1491 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1622 = false ∨ valuation q 1640 = true := counterClause1491 (baseVal q)

theorem counterClause1492 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1623 = false ∨ valuationOf q 1641 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1623)) (literal (valuationOf q) (1641)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 3 8 (meaning1559 q) (meaning1623 q) (meaning1641 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1623 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1492 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1623 = false ∨ valuation q 1641 = true := counterClause1492 (baseVal q)

theorem counterClause1493 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1637 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1637)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 4 3 (meaning1560 q) (meaning1618 q) (meaning1637 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1493 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1618 = false ∨ valuation q 1637 = true := counterClause1493 (baseVal q)

theorem counterClause1494 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1638 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1638)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 4 4 (meaning1560 q) (meaning1619 q) (meaning1638 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1494 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1619 = false ∨ valuation q 1638 = true := counterClause1494 (baseVal q)

theorem counterClause1495 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1639 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1639)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 4 5 (meaning1560 q) (meaning1620 q) (meaning1639 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1495 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1620 = false ∨ valuation q 1639 = true := counterClause1495 (baseVal q)

theorem counterClause1496 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1640 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1621)) (literal (valuationOf q) (1640)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 4 6 (meaning1560 q) (meaning1621 q) (meaning1640 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1496 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1621 = false ∨ valuation q 1640 = true := counterClause1496 (baseVal q)

theorem counterClause1497 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1641 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1622)) (literal (valuationOf q) (1641)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 4 7 (meaning1560 q) (meaning1622 q) (meaning1641 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1497 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1622 = false ∨ valuation q 1641 = true := counterClause1497 (baseVal q)

theorem counterClause1498 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1623 = false ∨ valuationOf q 1642 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1623)) (literal (valuationOf q) (1642)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 4 8 (meaning1560 q) (meaning1623 q) (meaning1642 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1623 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1498 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1623 = false ∨ valuation q 1642 = true := counterClause1498 (baseVal q)

theorem counterClause1499 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1624 = false ∨ valuationOf q 1643 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1624)) (literal (valuationOf q) (1643)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 4 9 (meaning1560 q) (meaning1624 q) (meaning1643 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1624 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1499 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1624 = false ∨ valuation q 1643 = true := counterClause1499 (baseVal q)

theorem counterClause1500 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1644 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1625)) (literal (valuationOf q) (1644)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 4 10 (meaning1560 q) (meaning1625 q) (meaning1644 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1500 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1625 = false ∨ valuation q 1644 = true := counterClause1500 (baseVal q)

theorem counterClause1501 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1637 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1561)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1637)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 5 2 (meaning1561 q) (meaning1617 q) (meaning1637 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1501 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1617 = false ∨ valuation q 1637 = true := counterClause1501 (baseVal q)

theorem counterClause1502 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1638 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1561)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1638)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 5 3 (meaning1561 q) (meaning1618 q) (meaning1638 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1502 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1618 = false ∨ valuation q 1638 = true := counterClause1502 (baseVal q)

theorem counterClause1503 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1639 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1561)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1639)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 5 4 (meaning1561 q) (meaning1619 q) (meaning1639 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1503 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1619 = false ∨ valuation q 1639 = true := counterClause1503 (baseVal q)

theorem counterClause1504 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1640 = true := by
  have hs : count1631 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) + (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (l₂ := [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61])
  have hm := merge_two (literal (valuationOf q) (1561)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1640)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31]) (countLit q [-33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (count1631 q) 5 5 (meaning1561 q) (meaning1620 q) (meaning1640 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1504 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1620 = false ∨ valuation q 1640 = true := counterClause1504 (baseVal q)

theorem block46 (q : Snake 81) (h : Conditions q) : B112E105.Block46 (valuation q) :=
  ⟨clause1473 q h, clause1474 q h, clause1475 q h, clause1476 q h, clause1477 q h, clause1478 q h, clause1479 q h, clause1480 q h, clause1481 q h, clause1482 q h, clause1483 q h, clause1484 q h, clause1485 q h, clause1486 q h, clause1487 q h, clause1488 q h, clause1489 q h, clause1490 q h, clause1491 q h, clause1492 q h, clause1493 q h, clause1494 q h, clause1495 q h, clause1496 q h, clause1497 q h, clause1498 q h, clause1499 q h, clause1500 q h, clause1501 q h, clause1502 q h, clause1503 q h, clause1504 q h⟩

end
end Snake9.Regrowth.E112105
