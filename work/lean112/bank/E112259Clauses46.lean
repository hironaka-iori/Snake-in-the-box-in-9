import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec46 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1473 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1603 = true := by
  have hs : count1602 q = (countLit q [-100, -102]) + (countLit q [-103, -105]) := List.countP_append (p := literal q) (l₁ := [-100, -102]) (l₂ := [-103, -105])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1603)) (countLit q [-100, -102]) (countLit q [-103, -105]) (count1602 q) 1 1 (meaning1598 q) (meaning1600 q) (meaning1603 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1473 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1600 = false ∨ valuation q 1603 = true := counterClause1473 (baseVal q)

theorem counterClause1474 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1604 = true := by
  have hs : count1602 q = (countLit q [-100, -102]) + (countLit q [-103, -105]) := List.countP_append (p := literal q) (l₁ := [-100, -102]) (l₂ := [-103, -105])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1604)) (countLit q [-100, -102]) (countLit q [-103, -105]) (count1602 q) 1 2 (meaning1598 q) (meaning1601 q) (meaning1604 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1474 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1601 = false ∨ valuation q 1604 = true := counterClause1474 (baseVal q)

theorem counterClause1475 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 1606 = true := by
  have hs : count1606 q = (countLit q [-106]) + (countLit q [-107]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-107])
  have hm := merge_right (literal (valuationOf q) (-107)) (literal (valuationOf q) (1606)) (countLit q [-106]) (countLit q [-107]) (count1606 q) 1 (meaningNeg107 q) (meaning1606 q) hs
  change (! (valuationOf q 107)) = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1475 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 1606 = true := counterClause1475 (baseVal q)

theorem counterClause1476 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 1608 = true := by
  have hs : count1608 q = (countLit q [-111]) + (countLit q [-115]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-115])
  have hm := merge_left (literal (valuationOf q) (-111)) (literal (valuationOf q) (1608)) (countLit q [-111]) (countLit q [-115]) (count1608 q) 1 (meaningNeg111 q) (meaning1608 q) hs
  change (! (valuationOf q 111)) = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1476 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 1608 = true := counterClause1476 (baseVal q)

theorem counterClause1477 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1610 = true := by
  have hs : count1610 q = (countLit q [-106, -107]) + (countLit q [-111, -115]) := List.countP_append (p := literal q) (l₁ := [-106, -107]) (l₂ := [-111, -115])
  have hm := merge_right (literal (valuationOf q) (1608)) (literal (valuationOf q) (1610)) (countLit q [-106, -107]) (countLit q [-111, -115]) (count1610 q) 1 (meaning1608 q) (meaning1610 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1477 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1610 = true := counterClause1477 (baseVal q)

theorem counterClause1478 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1611 = true := by
  have hs : count1610 q = (countLit q [-106, -107]) + (countLit q [-111, -115]) := List.countP_append (p := literal q) (l₁ := [-106, -107]) (l₂ := [-111, -115])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1611)) (countLit q [-106, -107]) (countLit q [-111, -115]) (count1610 q) 1 1 (meaning1606 q) (meaning1608 q) (meaning1611 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1478 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1608 = false ∨ valuation q 1611 = true := counterClause1478 (baseVal q)

theorem counterClause1479 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1615 = true := by
  have hs : count1614 q = (countLit q [-100, -102, -103, -105]) + (countLit q [-106, -107, -111, -115]) := List.countP_append (p := literal q) (l₁ := [-100, -102, -103, -105]) (l₂ := [-106, -107, -111, -115])
  have hm := merge_right (literal (valuationOf q) (1611)) (literal (valuationOf q) (1615)) (countLit q [-100, -102, -103, -105]) (countLit q [-106, -107, -111, -115]) (count1614 q) 2 (meaning1611 q) (meaning1615 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1479 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1615 = true := counterClause1479 (baseVal q)

theorem counterClause1480 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1614 = true := by
  have hs : count1614 q = (countLit q [-100, -102, -103, -105]) + (countLit q [-106, -107, -111, -115]) := List.countP_append (p := literal q) (l₁ := [-100, -102, -103, -105]) (l₂ := [-106, -107, -111, -115])
  have hm := merge_left (literal (valuationOf q) (1602)) (literal (valuationOf q) (1614)) (countLit q [-100, -102, -103, -105]) (countLit q [-106, -107, -111, -115]) (count1614 q) 1 (meaning1602 q) (meaning1614 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1480 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1614 = true := counterClause1480 (baseVal q)

theorem counterClause1481 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1615 = true := by
  have hs : count1614 q = (countLit q [-100, -102, -103, -105]) + (countLit q [-106, -107, -111, -115]) := List.countP_append (p := literal q) (l₁ := [-100, -102, -103, -105]) (l₂ := [-106, -107, -111, -115])
  have hm := merge_two (literal (valuationOf q) (1602)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1615)) (countLit q [-100, -102, -103, -105]) (countLit q [-106, -107, -111, -115]) (count1614 q) 1 1 (meaning1602 q) (meaning1610 q) (meaning1615 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1481 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1610 = false ∨ valuation q 1615 = true := counterClause1481 (baseVal q)

theorem counterClause1482 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1615 = true := by
  have hs : count1614 q = (countLit q [-100, -102, -103, -105]) + (countLit q [-106, -107, -111, -115]) := List.countP_append (p := literal q) (l₁ := [-100, -102, -103, -105]) (l₂ := [-106, -107, -111, -115])
  have hm := merge_left (literal (valuationOf q) (1603)) (literal (valuationOf q) (1615)) (countLit q [-100, -102, -103, -105]) (countLit q [-106, -107, -111, -115]) (count1614 q) 2 (meaning1603 q) (meaning1615 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1482 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1615 = true := counterClause1482 (baseVal q)

theorem counterClause1483 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1616 = true := by
  have hs : count1614 q = (countLit q [-100, -102, -103, -105]) + (countLit q [-106, -107, -111, -115]) := List.countP_append (p := literal q) (l₁ := [-100, -102, -103, -105]) (l₂ := [-106, -107, -111, -115])
  have hm := merge_two (literal (valuationOf q) (1603)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1616)) (countLit q [-100, -102, -103, -105]) (countLit q [-106, -107, -111, -115]) (count1614 q) 2 1 (meaning1603 q) (meaning1610 q) (meaning1616 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1483 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1610 = false ∨ valuation q 1616 = true := counterClause1483 (baseVal q)

theorem counterClause1484 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1616 = true := by
  have hs : count1614 q = (countLit q [-100, -102, -103, -105]) + (countLit q [-106, -107, -111, -115]) := List.countP_append (p := literal q) (l₁ := [-100, -102, -103, -105]) (l₂ := [-106, -107, -111, -115])
  have hm := merge_left (literal (valuationOf q) (1604)) (literal (valuationOf q) (1616)) (countLit q [-100, -102, -103, -105]) (countLit q [-106, -107, -111, -115]) (count1614 q) 3 (meaning1604 q) (meaning1616 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1484 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1616 = true := counterClause1484 (baseVal q)

theorem counterClause1485 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1624 = true := by
  have hs : count1622 q = (countLit q [-83, -86, -90, -92, -93, -96, -98]) + (countLit q [-100, -102, -103, -105, -106, -107, -111, -115]) := List.countP_append (p := literal q) (l₁ := [-83, -86, -90, -92, -93, -96, -98]) (l₂ := [-100, -102, -103, -105, -106, -107, -111, -115])
  have hm := merge_two (literal (valuationOf q) (1591)) (literal (valuationOf q) (1615)) (literal (valuationOf q) (1624)) (countLit q [-83, -86, -90, -92, -93, -96, -98]) (countLit q [-100, -102, -103, -105, -106, -107, -111, -115]) (count1622 q) 1 2 (meaning1591 q) (meaning1615 q) (meaning1624 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1485 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1615 = false ∨ valuation q 1624 = true := counterClause1485 (baseVal q)

theorem counterClause1486 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1624 = true := by
  have hs : count1622 q = (countLit q [-83, -86, -90, -92, -93, -96, -98]) + (countLit q [-100, -102, -103, -105, -106, -107, -111, -115]) := List.countP_append (p := literal q) (l₁ := [-83, -86, -90, -92, -93, -96, -98]) (l₂ := [-100, -102, -103, -105, -106, -107, -111, -115])
  have hm := merge_two (literal (valuationOf q) (1592)) (literal (valuationOf q) (1614)) (literal (valuationOf q) (1624)) (countLit q [-83, -86, -90, -92, -93, -96, -98]) (countLit q [-100, -102, -103, -105, -106, -107, -111, -115]) (count1622 q) 2 1 (meaning1592 q) (meaning1614 q) (meaning1624 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1486 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1614 = false ∨ valuation q 1624 = true := counterClause1486 (baseVal q)

theorem counterClause1487 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1625 = true := by
  have hs : count1622 q = (countLit q [-83, -86, -90, -92, -93, -96, -98]) + (countLit q [-100, -102, -103, -105, -106, -107, -111, -115]) := List.countP_append (p := literal q) (l₁ := [-83, -86, -90, -92, -93, -96, -98]) (l₂ := [-100, -102, -103, -105, -106, -107, -111, -115])
  have hm := merge_two (literal (valuationOf q) (1592)) (literal (valuationOf q) (1615)) (literal (valuationOf q) (1625)) (countLit q [-83, -86, -90, -92, -93, -96, -98]) (countLit q [-100, -102, -103, -105, -106, -107, -111, -115]) (count1622 q) 2 2 (meaning1592 q) (meaning1615 q) (meaning1625 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1487 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1615 = false ∨ valuation q 1625 = true := counterClause1487 (baseVal q)

theorem counterClause1488 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1626 = true := by
  have hs : count1622 q = (countLit q [-83, -86, -90, -92, -93, -96, -98]) + (countLit q [-100, -102, -103, -105, -106, -107, -111, -115]) := List.countP_append (p := literal q) (l₁ := [-83, -86, -90, -92, -93, -96, -98]) (l₂ := [-100, -102, -103, -105, -106, -107, -111, -115])
  have hm := merge_two (literal (valuationOf q) (1592)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1626)) (countLit q [-83, -86, -90, -92, -93, -96, -98]) (countLit q [-100, -102, -103, -105, -106, -107, -111, -115]) (count1622 q) 2 3 (meaning1592 q) (meaning1616 q) (meaning1626 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1488 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1616 = false ∨ valuation q 1626 = true := counterClause1488 (baseVal q)

theorem counterClause1489 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1625 = true := by
  have hs : count1622 q = (countLit q [-83, -86, -90, -92, -93, -96, -98]) + (countLit q [-100, -102, -103, -105, -106, -107, -111, -115]) := List.countP_append (p := literal q) (l₁ := [-83, -86, -90, -92, -93, -96, -98]) (l₂ := [-100, -102, -103, -105, -106, -107, -111, -115])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1614)) (literal (valuationOf q) (1625)) (countLit q [-83, -86, -90, -92, -93, -96, -98]) (countLit q [-100, -102, -103, -105, -106, -107, -111, -115]) (count1622 q) 3 1 (meaning1593 q) (meaning1614 q) (meaning1625 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1489 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1614 = false ∨ valuation q 1625 = true := counterClause1489 (baseVal q)

theorem counterClause1490 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1627 = true := by
  have hs : count1622 q = (countLit q [-83, -86, -90, -92, -93, -96, -98]) + (countLit q [-100, -102, -103, -105, -106, -107, -111, -115]) := List.countP_append (p := literal q) (l₁ := [-83, -86, -90, -92, -93, -96, -98]) (l₂ := [-100, -102, -103, -105, -106, -107, -111, -115])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1627)) (countLit q [-83, -86, -90, -92, -93, -96, -98]) (countLit q [-100, -102, -103, -105, -106, -107, -111, -115]) (count1622 q) 3 3 (meaning1593 q) (meaning1616 q) (meaning1627 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1490 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1616 = false ∨ valuation q 1627 = true := counterClause1490 (baseVal q)

theorem counterClause1491 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1649 = true := by
  have hs : count1637 q = (countLit q [-58, -59, -61, -65, -67, -70, -71, -72, -73, -76, -77, -79, -80, -81]) + (countLit q [-83, -86, -90, -92, -93, -96, -98, -100, -102, -103, -105, -106, -107, -111, -115]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -61, -65, -67, -70, -71, -72, -73, -76, -77, -79, -80, -81]) (l₂ := [-83, -86, -90, -92, -93, -96, -98, -100, -102, -103, -105, -106, -107, -111, -115])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1649)) (countLit q [-58, -59, -61, -65, -67, -70, -71, -72, -73, -76, -77, -79, -80, -81]) (countLit q [-83, -86, -90, -92, -93, -96, -98, -100, -102, -103, -105, -106, -107, -111, -115]) (count1637 q) 7 6 (meaning1570 q) (meaning1627 q) (meaning1649 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1491 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1627 = false ∨ valuation q 1649 = true := counterClause1491 (baseVal q)

theorem counterClause1492 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1624 = false ∨ valuationOf q 1647 = true := by
  have hs : count1637 q = (countLit q [-58, -59, -61, -65, -67, -70, -71, -72, -73, -76, -77, -79, -80, -81]) + (countLit q [-83, -86, -90, -92, -93, -96, -98, -100, -102, -103, -105, -106, -107, -111, -115]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -61, -65, -67, -70, -71, -72, -73, -76, -77, -79, -80, -81]) (l₂ := [-83, -86, -90, -92, -93, -96, -98, -100, -102, -103, -105, -106, -107, -111, -115])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1624)) (literal (valuationOf q) (1647)) (countLit q [-58, -59, -61, -65, -67, -70, -71, -72, -73, -76, -77, -79, -80, -81]) (countLit q [-83, -86, -90, -92, -93, -96, -98, -100, -102, -103, -105, -106, -107, -111, -115]) (count1637 q) 8 3 (meaning1571 q) (meaning1624 q) (meaning1647 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1624 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1492 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1624 = false ∨ valuation q 1647 = true := counterClause1492 (baseVal q)

theorem counterClause1493 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1648 = true := by
  have hs : count1637 q = (countLit q [-58, -59, -61, -65, -67, -70, -71, -72, -73, -76, -77, -79, -80, -81]) + (countLit q [-83, -86, -90, -92, -93, -96, -98, -100, -102, -103, -105, -106, -107, -111, -115]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -61, -65, -67, -70, -71, -72, -73, -76, -77, -79, -80, -81]) (l₂ := [-83, -86, -90, -92, -93, -96, -98, -100, -102, -103, -105, -106, -107, -111, -115])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1625)) (literal (valuationOf q) (1648)) (countLit q [-58, -59, -61, -65, -67, -70, -71, -72, -73, -76, -77, -79, -80, -81]) (countLit q [-83, -86, -90, -92, -93, -96, -98, -100, -102, -103, -105, -106, -107, -111, -115]) (count1637 q) 8 4 (meaning1571 q) (meaning1625 q) (meaning1648 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1625 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1493 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1625 = false ∨ valuation q 1648 = true := counterClause1493 (baseVal q)

theorem counterClause1494 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1650 = true := by
  have hs : count1637 q = (countLit q [-58, -59, -61, -65, -67, -70, -71, -72, -73, -76, -77, -79, -80, -81]) + (countLit q [-83, -86, -90, -92, -93, -96, -98, -100, -102, -103, -105, -106, -107, -111, -115]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -61, -65, -67, -70, -71, -72, -73, -76, -77, -79, -80, -81]) (l₂ := [-83, -86, -90, -92, -93, -96, -98, -100, -102, -103, -105, -106, -107, -111, -115])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1626)) (literal (valuationOf q) (1650)) (countLit q [-58, -59, -61, -65, -67, -70, -71, -72, -73, -76, -77, -79, -80, -81]) (countLit q [-83, -86, -90, -92, -93, -96, -98, -100, -102, -103, -105, -106, -107, -111, -115]) (count1637 q) 9 5 (meaning1572 q) (meaning1626 q) (meaning1650 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1626 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1494 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1626 = false ∨ valuation q 1650 = true := counterClause1494 (baseVal q)

theorem counterClause1495 (q : Nat → Bool) : valuationOf q 1509 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1672 = true := by
  have hs : count1655 q = (countLit q [-3, -4, -5, -8, -9, -12, -13, -16, -18, -20, -22, -24, -26, -28, -29, -31, -33, -35, -37, -40, -41, -43, -45, -47, -49, -51, -53, -54, -56]) + (countLit q [-58, -59, -61, -65, -67, -70, -71, -72, -73, -76, -77, -79, -80, -81, -83, -86, -90, -92, -93, -96, -98, -100, -102, -103, -105, -106, -107, -111, -115]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -12, -13, -16, -18, -20, -22, -24, -26, -28, -29, -31, -33, -35, -37, -40, -41, -43, -45, -47, -49, -51, -53, -54, -56]) (l₂ := [-58, -59, -61, -65, -67, -70, -71, -72, -73, -76, -77, -79, -80, -81, -83, -86, -90, -92, -93, -96, -98, -100, -102, -103, -105, -106, -107, -111, -115])
  have hm := merge_two (literal (valuationOf q) (1509)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1672)) (countLit q [-3, -4, -5, -8, -9, -12, -13, -16, -18, -20, -22, -24, -26, -28, -29, -31, -33, -35, -37, -40, -41, -43, -45, -47, -49, -51, -53, -54, -56]) (countLit q [-58, -59, -61, -65, -67, -70, -71, -72, -73, -76, -77, -79, -80, -81, -83, -86, -90, -92, -93, -96, -98, -100, -102, -103, -105, -106, -107, -111, -115]) (count1655 q) 4 14 (meaning1509 q) (meaning1650 q) (meaning1672 q) hs
  change valuationOf q 1509 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1495 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1650 = false ∨ valuation q 1672 = true := counterClause1495 (baseVal q)

theorem counterClause1496 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1672 = true := by
  have hs : count1655 q = (countLit q [-3, -4, -5, -8, -9, -12, -13, -16, -18, -20, -22, -24, -26, -28, -29, -31, -33, -35, -37, -40, -41, -43, -45, -47, -49, -51, -53, -54, -56]) + (countLit q [-58, -59, -61, -65, -67, -70, -71, -72, -73, -76, -77, -79, -80, -81, -83, -86, -90, -92, -93, -96, -98, -100, -102, -103, -105, -106, -107, -111, -115]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -12, -13, -16, -18, -20, -22, -24, -26, -28, -29, -31, -33, -35, -37, -40, -41, -43, -45, -47, -49, -51, -53, -54, -56]) (l₂ := [-58, -59, -61, -65, -67, -70, -71, -72, -73, -76, -77, -79, -80, -81, -83, -86, -90, -92, -93, -96, -98, -100, -102, -103, -105, -106, -107, -111, -115])
  have hm := merge_two (literal (valuationOf q) (1510)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1672)) (countLit q [-3, -4, -5, -8, -9, -12, -13, -16, -18, -20, -22, -24, -26, -28, -29, -31, -33, -35, -37, -40, -41, -43, -45, -47, -49, -51, -53, -54, -56]) (countLit q [-58, -59, -61, -65, -67, -70, -71, -72, -73, -76, -77, -79, -80, -81, -83, -86, -90, -92, -93, -96, -98, -100, -102, -103, -105, -106, -107, -111, -115]) (count1655 q) 5 13 (meaning1510 q) (meaning1649 q) (meaning1672 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1496 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1649 = false ∨ valuation q 1672 = true := counterClause1496 (baseVal q)

theorem counterClause1497 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1672 = true := by
  have hs : count1655 q = (countLit q [-3, -4, -5, -8, -9, -12, -13, -16, -18, -20, -22, -24, -26, -28, -29, -31, -33, -35, -37, -40, -41, -43, -45, -47, -49, -51, -53, -54, -56]) + (countLit q [-58, -59, -61, -65, -67, -70, -71, -72, -73, -76, -77, -79, -80, -81, -83, -86, -90, -92, -93, -96, -98, -100, -102, -103, -105, -106, -107, -111, -115]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -12, -13, -16, -18, -20, -22, -24, -26, -28, -29, -31, -33, -35, -37, -40, -41, -43, -45, -47, -49, -51, -53, -54, -56]) (l₂ := [-58, -59, -61, -65, -67, -70, -71, -72, -73, -76, -77, -79, -80, -81, -83, -86, -90, -92, -93, -96, -98, -100, -102, -103, -105, -106, -107, -111, -115])
  have hm := merge_two (literal (valuationOf q) (1511)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1672)) (countLit q [-3, -4, -5, -8, -9, -12, -13, -16, -18, -20, -22, -24, -26, -28, -29, -31, -33, -35, -37, -40, -41, -43, -45, -47, -49, -51, -53, -54, -56]) (countLit q [-58, -59, -61, -65, -67, -70, -71, -72, -73, -76, -77, -79, -80, -81, -83, -86, -90, -92, -93, -96, -98, -100, -102, -103, -105, -106, -107, -111, -115]) (count1655 q) 6 12 (meaning1511 q) (meaning1648 q) (meaning1672 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1497 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1648 = false ∨ valuation q 1672 = true := counterClause1497 (baseVal q)

theorem counterClause1498 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1672 = true := by
  have hs : count1655 q = (countLit q [-3, -4, -5, -8, -9, -12, -13, -16, -18, -20, -22, -24, -26, -28, -29, -31, -33, -35, -37, -40, -41, -43, -45, -47, -49, -51, -53, -54, -56]) + (countLit q [-58, -59, -61, -65, -67, -70, -71, -72, -73, -76, -77, -79, -80, -81, -83, -86, -90, -92, -93, -96, -98, -100, -102, -103, -105, -106, -107, -111, -115]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -12, -13, -16, -18, -20, -22, -24, -26, -28, -29, -31, -33, -35, -37, -40, -41, -43, -45, -47, -49, -51, -53, -54, -56]) (l₂ := [-58, -59, -61, -65, -67, -70, -71, -72, -73, -76, -77, -79, -80, -81, -83, -86, -90, -92, -93, -96, -98, -100, -102, -103, -105, -106, -107, -111, -115])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1647)) (literal (valuationOf q) (1672)) (countLit q [-3, -4, -5, -8, -9, -12, -13, -16, -18, -20, -22, -24, -26, -28, -29, -31, -33, -35, -37, -40, -41, -43, -45, -47, -49, -51, -53, -54, -56]) (countLit q [-58, -59, -61, -65, -67, -70, -71, -72, -73, -76, -77, -79, -80, -81, -83, -86, -90, -92, -93, -96, -98, -100, -102, -103, -105, -106, -107, -111, -115]) (count1655 q) 7 11 (meaning1512 q) (meaning1647 q) (meaning1672 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1498 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1647 = false ∨ valuation q 1672 = true := counterClause1498 (baseVal q)

theorem clause1499 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false := by
  rw [value1672]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1655 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1500 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 3 = false ∨ valuation q 54 = false ∨ valuation q 57 = false := by
  rw [value1, value3, value54, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (0 : Vertex) (4 : Vertex) (128 : Vertex) (132 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1501 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 5 = false ∨ valuation q 54 = false ∨ valuation q 60 = false := by
  rw [value1, value5, value54, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (0 : Vertex) (8 : Vertex) (128 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1502 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 20 = false ∨ valuation q 56 = false ∨ valuation q 78 = false := by
  rw [value2, value20, value56, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (3 : Vertex) (35 : Vertex) (131 : Vertex) (163 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1503 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 21 = false ∨ valuation q 57 = false ∨ valuation q 79 = false := by
  rw [value3, value21, value57, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (4 : Vertex) (36 : Vertex) (132 : Vertex) (164 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1504 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 60 = false ∨ valuation q 61 = false := by
  rw [value5, value6, value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (8 : Vertex) (9 : Vertex) (136 : Vertex) (137 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block46 (q : Snake 81) (h : Conditions q) : B112E259.Block46 (valuation q) :=
  ⟨clause1473 q h, clause1474 q h, clause1475 q h, clause1476 q h, clause1477 q h, clause1478 q h, clause1479 q h, clause1480 q h, clause1481 q h, clause1482 q h, clause1483 q h, clause1484 q h, clause1485 q h, clause1486 q h, clause1487 q h, clause1488 q h, clause1489 q h, clause1490 q h, clause1491 q h, clause1492 q h, clause1493 q h, clause1494 q h, clause1495 q h, clause1496 q h, clause1497 q h, clause1498 q h, clause1499 q h, clause1500 q h, clause1501 q h, clause1502 q h, clause1503 q h, clause1504 q h⟩

end
end Snake9.Regrowth.E112259
