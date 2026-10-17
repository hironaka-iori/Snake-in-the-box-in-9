import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec45 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1441 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1604 = true := by
  have hs : count1602 q = (countLit q [-98, -100]) + (countLit q [-103, -104]) := List.countP_append (p := literal q) (l₁ := [-98, -100]) (l₂ := [-103, -104])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1604)) (countLit q [-98, -100]) (countLit q [-103, -104]) (count1602 q) 2 1 (meaning1599 q) (meaning1600 q) (meaning1604 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1441 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1600 = false ∨ valuation q 1604 = true := counterClause1441 (baseVal q)

theorem counterClause1442 (q : Nat → Bool) : valuationOf q 110 = true ∨ valuationOf q 1606 = true := by
  have hs : count1606 q = (countLit q [-106]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-110])
  have hm := merge_right (literal (valuationOf q) (-110)) (literal (valuationOf q) (1606)) (countLit q [-106]) (countLit q [-110]) (count1606 q) 1 (meaningNeg110 q) (meaning1606 q) hs
  change (! (valuationOf q 110)) = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1442 (q : Snake 81) (h : Conditions q) : valuation q 110 = true ∨ valuation q 1606 = true := counterClause1442 (baseVal q)

theorem counterClause1443 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 1606 = true := by
  have hs : count1606 q = (countLit q [-106]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-110])
  have hm := merge_left (literal (valuationOf q) (-106)) (literal (valuationOf q) (1606)) (countLit q [-106]) (countLit q [-110]) (count1606 q) 1 (meaningNeg106 q) (meaning1606 q) hs
  change (! (valuationOf q 106)) = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1443 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 1606 = true := counterClause1443 (baseVal q)

theorem counterClause1444 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 110 = true ∨ valuationOf q 1607 = true := by
  have hs : count1606 q = (countLit q [-106]) + (countLit q [-110]) := List.countP_append (p := literal q) (l₁ := [-106]) (l₂ := [-110])
  have hm := merge_two (literal (valuationOf q) (-106)) (literal (valuationOf q) (-110)) (literal (valuationOf q) (1607)) (countLit q [-106]) (countLit q [-110]) (count1606 q) 1 1 (meaningNeg106 q) (meaningNeg110 q) (meaning1607 q) hs
  change (! (valuationOf q 106)) = false ∨ (! (valuationOf q 110)) = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1444 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 110 = true ∨ valuation q 1607 = true := counterClause1444 (baseVal q)

theorem counterClause1445 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 1608 = true := by
  have hs : count1608 q = (countLit q [-115]) + (countLit q [-116]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-116])
  have hm := merge_left (literal (valuationOf q) (-115)) (literal (valuationOf q) (1608)) (countLit q [-115]) (countLit q [-116]) (count1608 q) 1 (meaningNeg115 q) (meaning1608 q) hs
  change (! (valuationOf q 115)) = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1445 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 1608 = true := counterClause1445 (baseVal q)

theorem counterClause1446 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 116 = true ∨ valuationOf q 1609 = true := by
  have hs : count1608 q = (countLit q [-115]) + (countLit q [-116]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-116])
  have hm := merge_two (literal (valuationOf q) (-115)) (literal (valuationOf q) (-116)) (literal (valuationOf q) (1609)) (countLit q [-115]) (countLit q [-116]) (count1608 q) 1 1 (meaningNeg115 q) (meaningNeg116 q) (meaning1609 q) hs
  change (! (valuationOf q 115)) = false ∨ (! (valuationOf q 116)) = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1446 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 116 = true ∨ valuation q 1609 = true := counterClause1446 (baseVal q)

theorem counterClause1447 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1610 = true := by
  have hs : count1610 q = (countLit q [-106, -110]) + (countLit q [-115, -116]) := List.countP_append (p := literal q) (l₁ := [-106, -110]) (l₂ := [-115, -116])
  have hm := merge_right (literal (valuationOf q) (1608)) (literal (valuationOf q) (1610)) (countLit q [-106, -110]) (countLit q [-115, -116]) (count1610 q) 1 (meaning1608 q) (meaning1610 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1447 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1610 = true := counterClause1447 (baseVal q)

theorem counterClause1448 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1610 = true := by
  have hs : count1610 q = (countLit q [-106, -110]) + (countLit q [-115, -116]) := List.countP_append (p := literal q) (l₁ := [-106, -110]) (l₂ := [-115, -116])
  have hm := merge_left (literal (valuationOf q) (1606)) (literal (valuationOf q) (1610)) (countLit q [-106, -110]) (countLit q [-115, -116]) (count1610 q) 1 (meaning1606 q) (meaning1610 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1448 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1610 = true := counterClause1448 (baseVal q)

theorem counterClause1449 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1611 = true := by
  have hs : count1610 q = (countLit q [-106, -110]) + (countLit q [-115, -116]) := List.countP_append (p := literal q) (l₁ := [-106, -110]) (l₂ := [-115, -116])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1611)) (countLit q [-106, -110]) (countLit q [-115, -116]) (count1610 q) 1 1 (meaning1606 q) (meaning1608 q) (meaning1611 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1449 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1608 = false ∨ valuation q 1611 = true := counterClause1449 (baseVal q)

theorem counterClause1450 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1612 = true := by
  have hs : count1610 q = (countLit q [-106, -110]) + (countLit q [-115, -116]) := List.countP_append (p := literal q) (l₁ := [-106, -110]) (l₂ := [-115, -116])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1612)) (countLit q [-106, -110]) (countLit q [-115, -116]) (count1610 q) 1 2 (meaning1606 q) (meaning1609 q) (meaning1612 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1450 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1609 = false ∨ valuation q 1612 = true := counterClause1450 (baseVal q)

theorem counterClause1451 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1611 = true := by
  have hs : count1610 q = (countLit q [-106, -110]) + (countLit q [-115, -116]) := List.countP_append (p := literal q) (l₁ := [-106, -110]) (l₂ := [-115, -116])
  have hm := merge_left (literal (valuationOf q) (1607)) (literal (valuationOf q) (1611)) (countLit q [-106, -110]) (countLit q [-115, -116]) (count1610 q) 2 (meaning1607 q) (meaning1611 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1451 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1611 = true := counterClause1451 (baseVal q)

theorem counterClause1452 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1612 = true := by
  have hs : count1610 q = (countLit q [-106, -110]) + (countLit q [-115, -116]) := List.countP_append (p := literal q) (l₁ := [-106, -110]) (l₂ := [-115, -116])
  have hm := merge_two (literal (valuationOf q) (1607)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1612)) (countLit q [-106, -110]) (countLit q [-115, -116]) (count1610 q) 2 1 (meaning1607 q) (meaning1608 q) (meaning1612 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1452 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1608 = false ∨ valuation q 1612 = true := counterClause1452 (baseVal q)

theorem counterClause1453 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1616 = true := by
  have hs : count1614 q = (countLit q [-98, -100, -103, -104]) + (countLit q [-106, -110, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-98, -100, -103, -104]) (l₂ := [-106, -110, -115, -116])
  have hm := merge_right (literal (valuationOf q) (1612)) (literal (valuationOf q) (1616)) (countLit q [-98, -100, -103, -104]) (countLit q [-106, -110, -115, -116]) (count1614 q) 3 (meaning1612 q) (meaning1616 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1453 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1616 = true := counterClause1453 (baseVal q)

theorem counterClause1454 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1616 = true := by
  have hs : count1614 q = (countLit q [-98, -100, -103, -104]) + (countLit q [-106, -110, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-98, -100, -103, -104]) (l₂ := [-106, -110, -115, -116])
  have hm := merge_two (literal (valuationOf q) (1602)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1616)) (countLit q [-98, -100, -103, -104]) (countLit q [-106, -110, -115, -116]) (count1614 q) 1 2 (meaning1602 q) (meaning1611 q) (meaning1616 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1454 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1611 = false ∨ valuation q 1616 = true := counterClause1454 (baseVal q)

theorem counterClause1455 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1616 = true := by
  have hs : count1614 q = (countLit q [-98, -100, -103, -104]) + (countLit q [-106, -110, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-98, -100, -103, -104]) (l₂ := [-106, -110, -115, -116])
  have hm := merge_two (literal (valuationOf q) (1603)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1616)) (countLit q [-98, -100, -103, -104]) (countLit q [-106, -110, -115, -116]) (count1614 q) 2 1 (meaning1603 q) (meaning1610 q) (meaning1616 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1455 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1610 = false ∨ valuation q 1616 = true := counterClause1455 (baseVal q)

theorem counterClause1456 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1617 = true := by
  have hs : count1614 q = (countLit q [-98, -100, -103, -104]) + (countLit q [-106, -110, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-98, -100, -103, -104]) (l₂ := [-106, -110, -115, -116])
  have hm := merge_two (literal (valuationOf q) (1603)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1617)) (countLit q [-98, -100, -103, -104]) (countLit q [-106, -110, -115, -116]) (count1614 q) 2 2 (meaning1603 q) (meaning1611 q) (meaning1617 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1456 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1611 = false ∨ valuation q 1617 = true := counterClause1456 (baseVal q)

theorem counterClause1457 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1616 = true := by
  have hs : count1614 q = (countLit q [-98, -100, -103, -104]) + (countLit q [-106, -110, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-98, -100, -103, -104]) (l₂ := [-106, -110, -115, -116])
  have hm := merge_left (literal (valuationOf q) (1604)) (literal (valuationOf q) (1616)) (countLit q [-98, -100, -103, -104]) (countLit q [-106, -110, -115, -116]) (count1614 q) 3 (meaning1604 q) (meaning1616 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1457 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1616 = true := counterClause1457 (baseVal q)

theorem counterClause1458 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1617 = true := by
  have hs : count1614 q = (countLit q [-98, -100, -103, -104]) + (countLit q [-106, -110, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-98, -100, -103, -104]) (l₂ := [-106, -110, -115, -116])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1617)) (countLit q [-98, -100, -103, -104]) (countLit q [-106, -110, -115, -116]) (count1614 q) 3 1 (meaning1604 q) (meaning1610 q) (meaning1617 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1458 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1610 = false ∨ valuation q 1617 = true := counterClause1458 (baseVal q)

theorem counterClause1459 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1627 = true := by
  have hs : count1622 q = (countLit q [-86, -88, -90, -92, -94, -96, -97]) + (countLit q [-98, -100, -103, -104, -106, -110, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -90, -92, -94, -96, -97]) (l₂ := [-98, -100, -103, -104, -106, -110, -115, -116])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1627)) (countLit q [-86, -88, -90, -92, -94, -96, -97]) (countLit q [-98, -100, -103, -104, -106, -110, -115, -116]) (count1622 q) 3 3 (meaning1593 q) (meaning1616 q) (meaning1627 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1459 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1616 = false ∨ valuation q 1627 = true := counterClause1459 (baseVal q)

theorem counterClause1460 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1628 = true := by
  have hs : count1622 q = (countLit q [-86, -88, -90, -92, -94, -96, -97]) + (countLit q [-98, -100, -103, -104, -106, -110, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -90, -92, -94, -96, -97]) (l₂ := [-98, -100, -103, -104, -106, -110, -115, -116])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1628)) (countLit q [-86, -88, -90, -92, -94, -96, -97]) (countLit q [-98, -100, -103, -104, -106, -110, -115, -116]) (count1622 q) 3 4 (meaning1593 q) (meaning1617 q) (meaning1628 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1460 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1617 = false ∨ valuation q 1628 = true := counterClause1460 (baseVal q)

theorem counterClause1461 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1628 = true := by
  have hs : count1622 q = (countLit q [-86, -88, -90, -92, -94, -96, -97]) + (countLit q [-98, -100, -103, -104, -106, -110, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -90, -92, -94, -96, -97]) (l₂ := [-98, -100, -103, -104, -106, -110, -115, -116])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1628)) (countLit q [-86, -88, -90, -92, -94, -96, -97]) (countLit q [-98, -100, -103, -104, -106, -110, -115, -116]) (count1622 q) 4 3 (meaning1594 q) (meaning1616 q) (meaning1628 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1461 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1616 = false ∨ valuation q 1628 = true := counterClause1461 (baseVal q)

theorem counterClause1462 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1647 = true := by
  have hs : count1637 q = (countLit q [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84]) + (countLit q [-86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84]) (l₂ := [-86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1628)) (literal (valuationOf q) (1647)) (countLit q [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84]) (countLit q [-86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116]) (count1637 q) 4 7 (meaning1567 q) (meaning1628 q) (meaning1647 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1462 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1628 = false ∨ valuation q 1647 = true := counterClause1462 (baseVal q)

theorem counterClause1463 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1647 = true := by
  have hs : count1637 q = (countLit q [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84]) + (countLit q [-86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84]) (l₂ := [-86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1647)) (countLit q [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84]) (countLit q [-86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116]) (count1637 q) 5 6 (meaning1568 q) (meaning1627 q) (meaning1647 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1463 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1627 = false ∨ valuation q 1647 = true := counterClause1463 (baseVal q)

theorem counterClause1464 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1648 = true := by
  have hs : count1637 q = (countLit q [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84]) + (countLit q [-86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84]) (l₂ := [-86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1628)) (literal (valuationOf q) (1648)) (countLit q [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84]) (countLit q [-86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116]) (count1637 q) 5 7 (meaning1568 q) (meaning1628 q) (meaning1648 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1464 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1628 = false ∨ valuation q 1648 = true := counterClause1464 (baseVal q)

theorem counterClause1465 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1648 = true := by
  have hs : count1637 q = (countLit q [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84]) + (countLit q [-86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84]) (l₂ := [-86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1648)) (countLit q [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84]) (countLit q [-86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116]) (count1637 q) 6 6 (meaning1569 q) (meaning1627 q) (meaning1648 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1465 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1627 = false ∨ valuation q 1648 = true := counterClause1465 (baseVal q)

theorem counterClause1466 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1649 = true := by
  have hs : count1637 q = (countLit q [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84]) + (countLit q [-86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84]) (l₂ := [-86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1628)) (literal (valuationOf q) (1649)) (countLit q [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84]) (countLit q [-86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116]) (count1637 q) 6 7 (meaning1569 q) (meaning1628 q) (meaning1649 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1466 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1628 = false ∨ valuation q 1649 = true := counterClause1466 (baseVal q)

theorem counterClause1467 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1649 = true := by
  have hs : count1637 q = (countLit q [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84]) + (countLit q [-86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84]) (l₂ := [-86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1649)) (countLit q [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84]) (countLit q [-86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116]) (count1637 q) 7 6 (meaning1570 q) (meaning1627 q) (meaning1649 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1467 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1627 = false ∨ valuation q 1649 = true := counterClause1467 (baseVal q)

theorem counterClause1468 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1650 = true := by
  have hs : count1637 q = (countLit q [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84]) + (countLit q [-86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84]) (l₂ := [-86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1628)) (literal (valuationOf q) (1650)) (countLit q [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84]) (countLit q [-86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116]) (count1637 q) 7 7 (meaning1570 q) (meaning1628 q) (meaning1650 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1628 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1468 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1628 = false ∨ valuation q 1650 = true := counterClause1468 (baseVal q)

theorem counterClause1469 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1650 = true := by
  have hs : count1637 q = (countLit q [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84]) + (countLit q [-86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84]) (l₂ := [-86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1627)) (literal (valuationOf q) (1650)) (countLit q [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84]) (countLit q [-86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116]) (count1637 q) 8 6 (meaning1571 q) (meaning1627 q) (meaning1650 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1627 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1469 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1627 = false ∨ valuation q 1650 = true := counterClause1469 (baseVal q)

theorem counterClause1470 (q : Nat → Bool) : valuationOf q 1509 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1672 = true := by
  have hs : count1655 q = (countLit q [-3, -5, -8, -9, -10, -13, -14, -17, -18, -20, -22, -24, -25, -27, -29, -31, -33, -35, -36, -37, -38, -39, -41, -43, -47, -51, -53, -55, -56]) + (countLit q [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84, -86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -8, -9, -10, -13, -14, -17, -18, -20, -22, -24, -25, -27, -29, -31, -33, -35, -36, -37, -38, -39, -41, -43, -47, -51, -53, -55, -56]) (l₂ := [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84, -86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116])
  have hm := merge_two (literal (valuationOf q) (1509)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1672)) (countLit q [-3, -5, -8, -9, -10, -13, -14, -17, -18, -20, -22, -24, -25, -27, -29, -31, -33, -35, -36, -37, -38, -39, -41, -43, -47, -51, -53, -55, -56]) (countLit q [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84, -86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116]) (count1655 q) 4 14 (meaning1509 q) (meaning1650 q) (meaning1672 q) hs
  change valuationOf q 1509 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1470 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1650 = false ∨ valuation q 1672 = true := counterClause1470 (baseVal q)

theorem counterClause1471 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1672 = true := by
  have hs : count1655 q = (countLit q [-3, -5, -8, -9, -10, -13, -14, -17, -18, -20, -22, -24, -25, -27, -29, -31, -33, -35, -36, -37, -38, -39, -41, -43, -47, -51, -53, -55, -56]) + (countLit q [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84, -86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -8, -9, -10, -13, -14, -17, -18, -20, -22, -24, -25, -27, -29, -31, -33, -35, -36, -37, -38, -39, -41, -43, -47, -51, -53, -55, -56]) (l₂ := [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84, -86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116])
  have hm := merge_two (literal (valuationOf q) (1510)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1672)) (countLit q [-3, -5, -8, -9, -10, -13, -14, -17, -18, -20, -22, -24, -25, -27, -29, -31, -33, -35, -36, -37, -38, -39, -41, -43, -47, -51, -53, -55, -56]) (countLit q [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84, -86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116]) (count1655 q) 5 13 (meaning1510 q) (meaning1649 q) (meaning1672 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1471 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1649 = false ∨ valuation q 1672 = true := counterClause1471 (baseVal q)

theorem counterClause1472 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1672 = true := by
  have hs : count1655 q = (countLit q [-3, -5, -8, -9, -10, -13, -14, -17, -18, -20, -22, -24, -25, -27, -29, -31, -33, -35, -36, -37, -38, -39, -41, -43, -47, -51, -53, -55, -56]) + (countLit q [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84, -86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -8, -9, -10, -13, -14, -17, -18, -20, -22, -24, -25, -27, -29, -31, -33, -35, -36, -37, -38, -39, -41, -43, -47, -51, -53, -55, -56]) (l₂ := [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84, -86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116])
  have hm := merge_two (literal (valuationOf q) (1511)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1672)) (countLit q [-3, -5, -8, -9, -10, -13, -14, -17, -18, -20, -22, -24, -25, -27, -29, -31, -33, -35, -36, -37, -38, -39, -41, -43, -47, -51, -53, -55, -56]) (countLit q [-57, -58, -61, -65, -67, -69, -73, -74, -76, -77, -78, -80, -83, -84, -86, -88, -90, -92, -94, -96, -97, -98, -100, -103, -104, -106, -110, -115, -116]) (count1655 q) 6 12 (meaning1511 q) (meaning1648 q) (meaning1672 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1472 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1648 = false ∨ valuation q 1672 = true := counterClause1472 (baseVal q)

theorem block45 (q : Snake 81) (h : Conditions q) : B112E257.Block45 (valuation q) :=
  ⟨clause1441 q h, clause1442 q h, clause1443 q h, clause1444 q h, clause1445 q h, clause1446 q h, clause1447 q h, clause1448 q h, clause1449 q h, clause1450 q h, clause1451 q h, clause1452 q h, clause1453 q h, clause1454 q h, clause1455 q h, clause1456 q h, clause1457 q h, clause1458 q h, clause1459 q h, clause1460 q h, clause1461 q h, clause1462 q h, clause1463 q h, clause1464 q h, clause1465 q h, clause1466 q h, clause1467 q h, clause1468 q h, clause1469 q h, clause1470 q h, clause1471 q h, clause1472 q h⟩

end
end Snake9.Regrowth.E112257
