import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec46 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1473 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1632 = true := by
  have hs : count1631 q = (countLit q [-75, -76]) + (countLit q [-80, -81]) := List.countP_append (p := literal q) (l₁ := [-75, -76]) (l₂ := [-80, -81])
  have hm := merge_left (literal (valuationOf q) (1628)) (literal (valuationOf q) (1632)) (countLit q [-75, -76]) (countLit q [-80, -81]) (count1631 q) 2 (meaning1628 q) (meaning1632 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1473 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1632 = true := counterClause1473 (baseVal q)

theorem counterClause1474 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1633 = true := by
  have hs : count1631 q = (countLit q [-75, -76]) + (countLit q [-80, -81]) := List.countP_append (p := literal q) (l₁ := [-75, -76]) (l₂ := [-80, -81])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1629)) (literal (valuationOf q) (1633)) (countLit q [-75, -76]) (countLit q [-80, -81]) (count1631 q) 2 1 (meaning1628 q) (meaning1629 q) (meaning1633 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1629 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1474 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1629 = false ∨ valuation q 1633 = true := counterClause1474 (baseVal q)

theorem counterClause1475 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1634 = true := by
  have hs : count1631 q = (countLit q [-75, -76]) + (countLit q [-80, -81]) := List.countP_append (p := literal q) (l₁ := [-75, -76]) (l₂ := [-80, -81])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1630)) (literal (valuationOf q) (1634)) (countLit q [-75, -76]) (countLit q [-80, -81]) (count1631 q) 2 2 (meaning1628 q) (meaning1630 q) (meaning1634 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1475 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1630 = false ∨ valuation q 1634 = true := counterClause1475 (baseVal q)

theorem counterClause1476 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1635 = true := by
  have hs : count1635 q = (countLit q [-82]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-85])
  have hm := merge_right (literal (valuationOf q) (-85)) (literal (valuationOf q) (1635)) (countLit q [-82]) (countLit q [-85]) (count1635 q) 1 (meaningNeg85 q) (meaning1635 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1476 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1635 = true := counterClause1476 (baseVal q)

theorem counterClause1477 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1635 = true := by
  have hs : count1635 q = (countLit q [-82]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-85])
  have hm := merge_left (literal (valuationOf q) (-82)) (literal (valuationOf q) (1635)) (countLit q [-82]) (countLit q [-85]) (count1635 q) 1 (meaningNeg82 q) (meaning1635 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1477 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1635 = true := counterClause1477 (baseVal q)

theorem counterClause1478 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 85 = true ∨ valuationOf q 1636 = true := by
  have hs : count1635 q = (countLit q [-82]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-85])
  have hm := merge_two (literal (valuationOf q) (-82)) (literal (valuationOf q) (-85)) (literal (valuationOf q) (1636)) (countLit q [-82]) (countLit q [-85]) (count1635 q) 1 1 (meaningNeg82 q) (meaningNeg85 q) (meaning1636 q) hs
  change (! (valuationOf q 82)) = false ∨ (! (valuationOf q 85)) = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1478 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 85 = true ∨ valuation q 1636 = true := counterClause1478 (baseVal q)

theorem counterClause1479 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 1637 = true := by
  have hs : count1637 q = (countLit q [-87]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-89])
  have hm := merge_right (literal (valuationOf q) (-89)) (literal (valuationOf q) (1637)) (countLit q [-87]) (countLit q [-89]) (count1637 q) 1 (meaningNeg89 q) (meaning1637 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1479 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 1637 = true := counterClause1479 (baseVal q)

theorem counterClause1480 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 1637 = true := by
  have hs : count1637 q = (countLit q [-87]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-89])
  have hm := merge_left (literal (valuationOf q) (-87)) (literal (valuationOf q) (1637)) (countLit q [-87]) (countLit q [-89]) (count1637 q) 1 (meaningNeg87 q) (meaning1637 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1480 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 1637 = true := counterClause1480 (baseVal q)

theorem counterClause1481 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 89 = true ∨ valuationOf q 1638 = true := by
  have hs : count1637 q = (countLit q [-87]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-87]) (l₂ := [-89])
  have hm := merge_two (literal (valuationOf q) (-87)) (literal (valuationOf q) (-89)) (literal (valuationOf q) (1638)) (countLit q [-87]) (countLit q [-89]) (count1637 q) 1 1 (meaningNeg87 q) (meaningNeg89 q) (meaning1638 q) hs
  change (! (valuationOf q 87)) = false ∨ (! (valuationOf q 89)) = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1481 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 89 = true ∨ valuation q 1638 = true := counterClause1481 (baseVal q)

theorem counterClause1482 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1639 = true := by
  have hs : count1639 q = (countLit q [-82, -85]) + (countLit q [-87, -89]) := List.countP_append (p := literal q) (l₁ := [-82, -85]) (l₂ := [-87, -89])
  have hm := merge_right (literal (valuationOf q) (1637)) (literal (valuationOf q) (1639)) (countLit q [-82, -85]) (countLit q [-87, -89]) (count1639 q) 1 (meaning1637 q) (meaning1639 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1482 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1639 = true := counterClause1482 (baseVal q)

theorem counterClause1483 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1640 = true := by
  have hs : count1639 q = (countLit q [-82, -85]) + (countLit q [-87, -89]) := List.countP_append (p := literal q) (l₁ := [-82, -85]) (l₂ := [-87, -89])
  have hm := merge_right (literal (valuationOf q) (1638)) (literal (valuationOf q) (1640)) (countLit q [-82, -85]) (countLit q [-87, -89]) (count1639 q) 2 (meaning1638 q) (meaning1640 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1483 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1640 = true := counterClause1483 (baseVal q)

theorem counterClause1484 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1639 = true := by
  have hs : count1639 q = (countLit q [-82, -85]) + (countLit q [-87, -89]) := List.countP_append (p := literal q) (l₁ := [-82, -85]) (l₂ := [-87, -89])
  have hm := merge_left (literal (valuationOf q) (1635)) (literal (valuationOf q) (1639)) (countLit q [-82, -85]) (countLit q [-87, -89]) (count1639 q) 1 (meaning1635 q) (meaning1639 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1484 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1639 = true := counterClause1484 (baseVal q)

theorem counterClause1485 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1637 = false ∨ valuationOf q 1640 = true := by
  have hs : count1639 q = (countLit q [-82, -85]) + (countLit q [-87, -89]) := List.countP_append (p := literal q) (l₁ := [-82, -85]) (l₂ := [-87, -89])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1637)) (literal (valuationOf q) (1640)) (countLit q [-82, -85]) (countLit q [-87, -89]) (count1639 q) 1 1 (meaning1635 q) (meaning1637 q) (meaning1640 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1637 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1485 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1637 = false ∨ valuation q 1640 = true := counterClause1485 (baseVal q)

theorem counterClause1486 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1641 = true := by
  have hs : count1639 q = (countLit q [-82, -85]) + (countLit q [-87, -89]) := List.countP_append (p := literal q) (l₁ := [-82, -85]) (l₂ := [-87, -89])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1638)) (literal (valuationOf q) (1641)) (countLit q [-82, -85]) (countLit q [-87, -89]) (count1639 q) 1 2 (meaning1635 q) (meaning1638 q) (meaning1641 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1486 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1638 = false ∨ valuation q 1641 = true := counterClause1486 (baseVal q)

theorem counterClause1487 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1640 = true := by
  have hs : count1639 q = (countLit q [-82, -85]) + (countLit q [-87, -89]) := List.countP_append (p := literal q) (l₁ := [-82, -85]) (l₂ := [-87, -89])
  have hm := merge_left (literal (valuationOf q) (1636)) (literal (valuationOf q) (1640)) (countLit q [-82, -85]) (countLit q [-87, -89]) (count1639 q) 2 (meaning1636 q) (meaning1640 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1487 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1640 = true := counterClause1487 (baseVal q)

theorem counterClause1488 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1637 = false ∨ valuationOf q 1641 = true := by
  have hs : count1639 q = (countLit q [-82, -85]) + (countLit q [-87, -89]) := List.countP_append (p := literal q) (l₁ := [-82, -85]) (l₂ := [-87, -89])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1637)) (literal (valuationOf q) (1641)) (countLit q [-82, -85]) (countLit q [-87, -89]) (count1639 q) 2 1 (meaning1636 q) (meaning1637 q) (meaning1641 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1637 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1488 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1637 = false ∨ valuation q 1641 = true := counterClause1488 (baseVal q)

theorem counterClause1489 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1642 = true := by
  have hs : count1639 q = (countLit q [-82, -85]) + (countLit q [-87, -89]) := List.countP_append (p := literal q) (l₁ := [-82, -85]) (l₂ := [-87, -89])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1638)) (literal (valuationOf q) (1642)) (countLit q [-82, -85]) (countLit q [-87, -89]) (count1639 q) 2 2 (meaning1636 q) (meaning1638 q) (meaning1642 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1489 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1638 = false ∨ valuation q 1642 = true := counterClause1489 (baseVal q)

theorem counterClause1490 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1643 = true := by
  have hs : count1643 q = (countLit q [-75, -76, -80, -81]) + (countLit q [-82, -85, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -80, -81]) (l₂ := [-82, -85, -87, -89])
  have hm := merge_right (literal (valuationOf q) (1639)) (literal (valuationOf q) (1643)) (countLit q [-75, -76, -80, -81]) (countLit q [-82, -85, -87, -89]) (count1643 q) 1 (meaning1639 q) (meaning1643 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1490 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1643 = true := counterClause1490 (baseVal q)

theorem counterClause1491 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1644 = true := by
  have hs : count1643 q = (countLit q [-75, -76, -80, -81]) + (countLit q [-82, -85, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -80, -81]) (l₂ := [-82, -85, -87, -89])
  have hm := merge_right (literal (valuationOf q) (1640)) (literal (valuationOf q) (1644)) (countLit q [-75, -76, -80, -81]) (countLit q [-82, -85, -87, -89]) (count1643 q) 2 (meaning1640 q) (meaning1644 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1491 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1644 = true := counterClause1491 (baseVal q)

theorem counterClause1492 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1645 = true := by
  have hs : count1643 q = (countLit q [-75, -76, -80, -81]) + (countLit q [-82, -85, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -80, -81]) (l₂ := [-82, -85, -87, -89])
  have hm := merge_right (literal (valuationOf q) (1641)) (literal (valuationOf q) (1645)) (countLit q [-75, -76, -80, -81]) (countLit q [-82, -85, -87, -89]) (count1643 q) 3 (meaning1641 q) (meaning1645 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1492 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1645 = true := counterClause1492 (baseVal q)

theorem counterClause1493 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1646 = true := by
  have hs : count1643 q = (countLit q [-75, -76, -80, -81]) + (countLit q [-82, -85, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -80, -81]) (l₂ := [-82, -85, -87, -89])
  have hm := merge_right (literal (valuationOf q) (1642)) (literal (valuationOf q) (1646)) (countLit q [-75, -76, -80, -81]) (countLit q [-82, -85, -87, -89]) (count1643 q) 4 (meaning1642 q) (meaning1646 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1493 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1646 = true := counterClause1493 (baseVal q)

theorem counterClause1494 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1643 = true := by
  have hs : count1643 q = (countLit q [-75, -76, -80, -81]) + (countLit q [-82, -85, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -80, -81]) (l₂ := [-82, -85, -87, -89])
  have hm := merge_left (literal (valuationOf q) (1631)) (literal (valuationOf q) (1643)) (countLit q [-75, -76, -80, -81]) (countLit q [-82, -85, -87, -89]) (count1643 q) 1 (meaning1631 q) (meaning1643 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1494 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1643 = true := counterClause1494 (baseVal q)

theorem counterClause1495 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1644 = true := by
  have hs : count1643 q = (countLit q [-75, -76, -80, -81]) + (countLit q [-82, -85, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -80, -81]) (l₂ := [-82, -85, -87, -89])
  have hm := merge_two (literal (valuationOf q) (1631)) (literal (valuationOf q) (1639)) (literal (valuationOf q) (1644)) (countLit q [-75, -76, -80, -81]) (countLit q [-82, -85, -87, -89]) (count1643 q) 1 1 (meaning1631 q) (meaning1639 q) (meaning1644 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1495 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1639 = false ∨ valuation q 1644 = true := counterClause1495 (baseVal q)

theorem counterClause1496 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1645 = true := by
  have hs : count1643 q = (countLit q [-75, -76, -80, -81]) + (countLit q [-82, -85, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -80, -81]) (l₂ := [-82, -85, -87, -89])
  have hm := merge_two (literal (valuationOf q) (1631)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1645)) (countLit q [-75, -76, -80, -81]) (countLit q [-82, -85, -87, -89]) (count1643 q) 1 2 (meaning1631 q) (meaning1640 q) (meaning1645 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1496 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1640 = false ∨ valuation q 1645 = true := counterClause1496 (baseVal q)

theorem counterClause1497 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1646 = true := by
  have hs : count1643 q = (countLit q [-75, -76, -80, -81]) + (countLit q [-82, -85, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -80, -81]) (l₂ := [-82, -85, -87, -89])
  have hm := merge_two (literal (valuationOf q) (1631)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1646)) (countLit q [-75, -76, -80, -81]) (countLit q [-82, -85, -87, -89]) (count1643 q) 1 3 (meaning1631 q) (meaning1641 q) (meaning1646 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1497 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1641 = false ∨ valuation q 1646 = true := counterClause1497 (baseVal q)

theorem counterClause1498 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1647 = true := by
  have hs : count1643 q = (countLit q [-75, -76, -80, -81]) + (countLit q [-82, -85, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -80, -81]) (l₂ := [-82, -85, -87, -89])
  have hm := merge_two (literal (valuationOf q) (1631)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1647)) (countLit q [-75, -76, -80, -81]) (countLit q [-82, -85, -87, -89]) (count1643 q) 1 4 (meaning1631 q) (meaning1642 q) (meaning1647 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1498 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1642 = false ∨ valuation q 1647 = true := counterClause1498 (baseVal q)

theorem counterClause1499 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1644 = true := by
  have hs : count1643 q = (countLit q [-75, -76, -80, -81]) + (countLit q [-82, -85, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -80, -81]) (l₂ := [-82, -85, -87, -89])
  have hm := merge_left (literal (valuationOf q) (1632)) (literal (valuationOf q) (1644)) (countLit q [-75, -76, -80, -81]) (countLit q [-82, -85, -87, -89]) (count1643 q) 2 (meaning1632 q) (meaning1644 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1499 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1644 = true := counterClause1499 (baseVal q)

theorem counterClause1500 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1645 = true := by
  have hs : count1643 q = (countLit q [-75, -76, -80, -81]) + (countLit q [-82, -85, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -80, -81]) (l₂ := [-82, -85, -87, -89])
  have hm := merge_two (literal (valuationOf q) (1632)) (literal (valuationOf q) (1639)) (literal (valuationOf q) (1645)) (countLit q [-75, -76, -80, -81]) (countLit q [-82, -85, -87, -89]) (count1643 q) 2 1 (meaning1632 q) (meaning1639 q) (meaning1645 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1500 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1639 = false ∨ valuation q 1645 = true := counterClause1500 (baseVal q)

theorem counterClause1501 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1646 = true := by
  have hs : count1643 q = (countLit q [-75, -76, -80, -81]) + (countLit q [-82, -85, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -80, -81]) (l₂ := [-82, -85, -87, -89])
  have hm := merge_two (literal (valuationOf q) (1632)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1646)) (countLit q [-75, -76, -80, -81]) (countLit q [-82, -85, -87, -89]) (count1643 q) 2 2 (meaning1632 q) (meaning1640 q) (meaning1646 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1501 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1640 = false ∨ valuation q 1646 = true := counterClause1501 (baseVal q)

theorem counterClause1502 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1647 = true := by
  have hs : count1643 q = (countLit q [-75, -76, -80, -81]) + (countLit q [-82, -85, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -80, -81]) (l₂ := [-82, -85, -87, -89])
  have hm := merge_two (literal (valuationOf q) (1632)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1647)) (countLit q [-75, -76, -80, -81]) (countLit q [-82, -85, -87, -89]) (count1643 q) 2 3 (meaning1632 q) (meaning1641 q) (meaning1647 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1502 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1641 = false ∨ valuation q 1647 = true := counterClause1502 (baseVal q)

theorem counterClause1503 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1648 = true := by
  have hs : count1643 q = (countLit q [-75, -76, -80, -81]) + (countLit q [-82, -85, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -80, -81]) (l₂ := [-82, -85, -87, -89])
  have hm := merge_two (literal (valuationOf q) (1632)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1648)) (countLit q [-75, -76, -80, -81]) (countLit q [-82, -85, -87, -89]) (count1643 q) 2 4 (meaning1632 q) (meaning1642 q) (meaning1648 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1503 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1642 = false ∨ valuation q 1648 = true := counterClause1503 (baseVal q)

theorem counterClause1504 (q : Nat → Bool) : valuationOf q 1633 = false ∨ valuationOf q 1645 = true := by
  have hs : count1643 q = (countLit q [-75, -76, -80, -81]) + (countLit q [-82, -85, -87, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -80, -81]) (l₂ := [-82, -85, -87, -89])
  have hm := merge_left (literal (valuationOf q) (1633)) (literal (valuationOf q) (1645)) (countLit q [-75, -76, -80, -81]) (countLit q [-82, -85, -87, -89]) (count1643 q) 3 (meaning1633 q) (meaning1645 q) hs
  change valuationOf q 1633 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1504 (q : Snake 81) (h : Conditions q) : valuation q 1633 = false ∨ valuation q 1645 = true := counterClause1504 (baseVal q)

theorem block46 (q : Snake 81) (h : Conditions q) : B112E019.Block46 (valuation q) :=
  ⟨clause1473 q h, clause1474 q h, clause1475 q h, clause1476 q h, clause1477 q h, clause1478 q h, clause1479 q h, clause1480 q h, clause1481 q h, clause1482 q h, clause1483 q h, clause1484 q h, clause1485 q h, clause1486 q h, clause1487 q h, clause1488 q h, clause1489 q h, clause1490 q h, clause1491 q h, clause1492 q h, clause1493 q h, clause1494 q h, clause1495 q h, clause1496 q h, clause1497 q h, clause1498 q h, clause1499 q h, clause1500 q h, clause1501 q h, clause1502 q h, clause1503 q h, clause1504 q h⟩

end
end Snake9.Regrowth.E112019
