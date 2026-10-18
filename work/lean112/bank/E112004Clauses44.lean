import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec44 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1409 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1596 = true := by
  have hs : count1593 q = (countLit q [-61, -62, -64]) + (countLit q [-67, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64]) (l₂ := [-67, -70, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1596)) (countLit q [-61, -62, -64]) (countLit q [-67, -70, -71, -73]) (count1593 q) 2 2 (meaning1583 q) (meaning1590 q) (meaning1596 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1409 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1590 = false ∨ valuation q 1596 = true := counterClause1409 (baseVal q)

theorem counterClause1410 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1597 = true := by
  have hs : count1593 q = (countLit q [-61, -62, -64]) + (countLit q [-67, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64]) (l₂ := [-67, -70, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1597)) (countLit q [-61, -62, -64]) (countLit q [-67, -70, -71, -73]) (count1593 q) 2 3 (meaning1583 q) (meaning1591 q) (meaning1597 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1410 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1591 = false ∨ valuation q 1597 = true := counterClause1410 (baseVal q)

theorem counterClause1411 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1598 = true := by
  have hs : count1593 q = (countLit q [-61, -62, -64]) + (countLit q [-67, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64]) (l₂ := [-67, -70, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1598)) (countLit q [-61, -62, -64]) (countLit q [-67, -70, -71, -73]) (count1593 q) 2 4 (meaning1583 q) (meaning1592 q) (meaning1598 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1411 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1592 = false ∨ valuation q 1598 = true := counterClause1411 (baseVal q)

theorem counterClause1412 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1595 = true := by
  have hs : count1593 q = (countLit q [-61, -62, -64]) + (countLit q [-67, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64]) (l₂ := [-67, -70, -71, -73])
  have hm := merge_left (literal (valuationOf q) (1584)) (literal (valuationOf q) (1595)) (countLit q [-61, -62, -64]) (countLit q [-67, -70, -71, -73]) (count1593 q) 3 (meaning1584 q) (meaning1595 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1412 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1595 = true := counterClause1412 (baseVal q)

theorem counterClause1413 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1596 = true := by
  have hs : count1593 q = (countLit q [-61, -62, -64]) + (countLit q [-67, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64]) (l₂ := [-67, -70, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1596)) (countLit q [-61, -62, -64]) (countLit q [-67, -70, -71, -73]) (count1593 q) 3 1 (meaning1584 q) (meaning1589 q) (meaning1596 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1413 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1589 = false ∨ valuation q 1596 = true := counterClause1413 (baseVal q)

theorem counterClause1414 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1597 = true := by
  have hs : count1593 q = (countLit q [-61, -62, -64]) + (countLit q [-67, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64]) (l₂ := [-67, -70, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1597)) (countLit q [-61, -62, -64]) (countLit q [-67, -70, -71, -73]) (count1593 q) 3 2 (meaning1584 q) (meaning1590 q) (meaning1597 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1414 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1590 = false ∨ valuation q 1597 = true := counterClause1414 (baseVal q)

theorem counterClause1415 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1598 = true := by
  have hs : count1593 q = (countLit q [-61, -62, -64]) + (countLit q [-67, -70, -71, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64]) (l₂ := [-67, -70, -71, -73])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1598)) (countLit q [-61, -62, -64]) (countLit q [-67, -70, -71, -73]) (count1593 q) 3 3 (meaning1584 q) (meaning1591 q) (meaning1598 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1415 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1591 = false ∨ valuation q 1598 = true := counterClause1415 (baseVal q)

theorem counterClause1416 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1600 = true := by
  have hs : count1600 q = (countLit q [-75]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-78])
  have hm := merge_right (literal (valuationOf q) (-78)) (literal (valuationOf q) (1600)) (countLit q [-75]) (countLit q [-78]) (count1600 q) 1 (meaningNeg78 q) (meaning1600 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1416 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1600 = true := counterClause1416 (baseVal q)

theorem counterClause1417 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1602 = true := by
  have hs : count1602 q = (countLit q [-80]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-82])
  have hm := merge_right (literal (valuationOf q) (-82)) (literal (valuationOf q) (1602)) (countLit q [-80]) (countLit q [-82]) (count1602 q) 1 (meaningNeg82 q) (meaning1602 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1417 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1602 = true := counterClause1417 (baseVal q)

theorem counterClause1418 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 1602 = true := by
  have hs : count1602 q = (countLit q [-80]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-82])
  have hm := merge_left (literal (valuationOf q) (-80)) (literal (valuationOf q) (1602)) (countLit q [-80]) (countLit q [-82]) (count1602 q) 1 (meaningNeg80 q) (meaning1602 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1418 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 1602 = true := counterClause1418 (baseVal q)

theorem counterClause1419 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 82 = true ∨ valuationOf q 1603 = true := by
  have hs : count1602 q = (countLit q [-80]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-82])
  have hm := merge_two (literal (valuationOf q) (-80)) (literal (valuationOf q) (-82)) (literal (valuationOf q) (1603)) (countLit q [-80]) (countLit q [-82]) (count1602 q) 1 1 (meaningNeg80 q) (meaningNeg82 q) (meaning1603 q) hs
  change (! (valuationOf q 80)) = false ∨ (! (valuationOf q 82)) = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1419 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 82 = true ∨ valuation q 1603 = true := counterClause1419 (baseVal q)

theorem counterClause1420 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1604 = true := by
  have hs : count1604 q = (countLit q [-75, -78]) + (countLit q [-80, -82]) := List.countP_append (p := literal q) (l₁ := [-75, -78]) (l₂ := [-80, -82])
  have hm := merge_right (literal (valuationOf q) (1602)) (literal (valuationOf q) (1604)) (countLit q [-75, -78]) (countLit q [-80, -82]) (count1604 q) 1 (meaning1602 q) (meaning1604 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1420 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1604 = true := counterClause1420 (baseVal q)

theorem counterClause1421 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1605 = true := by
  have hs : count1604 q = (countLit q [-75, -78]) + (countLit q [-80, -82]) := List.countP_append (p := literal q) (l₁ := [-75, -78]) (l₂ := [-80, -82])
  have hm := merge_right (literal (valuationOf q) (1603)) (literal (valuationOf q) (1605)) (countLit q [-75, -78]) (countLit q [-80, -82]) (count1604 q) 2 (meaning1603 q) (meaning1605 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1421 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1605 = true := counterClause1421 (baseVal q)

theorem counterClause1422 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1604 = true := by
  have hs : count1604 q = (countLit q [-75, -78]) + (countLit q [-80, -82]) := List.countP_append (p := literal q) (l₁ := [-75, -78]) (l₂ := [-80, -82])
  have hm := merge_left (literal (valuationOf q) (1600)) (literal (valuationOf q) (1604)) (countLit q [-75, -78]) (countLit q [-80, -82]) (count1604 q) 1 (meaning1600 q) (meaning1604 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1422 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1604 = true := counterClause1422 (baseVal q)

theorem counterClause1423 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1605 = true := by
  have hs : count1604 q = (countLit q [-75, -78]) + (countLit q [-80, -82]) := List.countP_append (p := literal q) (l₁ := [-75, -78]) (l₂ := [-80, -82])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1605)) (countLit q [-75, -78]) (countLit q [-80, -82]) (count1604 q) 1 1 (meaning1600 q) (meaning1602 q) (meaning1605 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1423 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1602 = false ∨ valuation q 1605 = true := counterClause1423 (baseVal q)

theorem counterClause1424 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1606 = true := by
  have hs : count1604 q = (countLit q [-75, -78]) + (countLit q [-80, -82]) := List.countP_append (p := literal q) (l₁ := [-75, -78]) (l₂ := [-80, -82])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1606)) (countLit q [-75, -78]) (countLit q [-80, -82]) (count1604 q) 1 2 (meaning1600 q) (meaning1603 q) (meaning1606 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1424 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1603 = false ∨ valuation q 1606 = true := counterClause1424 (baseVal q)

theorem counterClause1425 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1608 = true := by
  have hs : count1608 q = (countLit q [-83]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-84])
  have hm := merge_right (literal (valuationOf q) (-84)) (literal (valuationOf q) (1608)) (countLit q [-83]) (countLit q [-84]) (count1608 q) 1 (meaningNeg84 q) (meaning1608 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1425 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1608 = true := counterClause1425 (baseVal q)

theorem counterClause1426 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 1608 = true := by
  have hs : count1608 q = (countLit q [-83]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-84])
  have hm := merge_left (literal (valuationOf q) (-83)) (literal (valuationOf q) (1608)) (countLit q [-83]) (countLit q [-84]) (count1608 q) 1 (meaningNeg83 q) (meaning1608 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1426 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 1608 = true := counterClause1426 (baseVal q)

theorem counterClause1427 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 84 = true ∨ valuationOf q 1609 = true := by
  have hs : count1608 q = (countLit q [-83]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-84])
  have hm := merge_two (literal (valuationOf q) (-83)) (literal (valuationOf q) (-84)) (literal (valuationOf q) (1609)) (countLit q [-83]) (countLit q [-84]) (count1608 q) 1 1 (meaningNeg83 q) (meaningNeg84 q) (meaning1609 q) hs
  change (! (valuationOf q 83)) = false ∨ (! (valuationOf q 84)) = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1427 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 84 = true ∨ valuation q 1609 = true := counterClause1427 (baseVal q)

theorem counterClause1428 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 1610 = true := by
  have hs : count1610 q = (countLit q [-86]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-87])
  have hm := merge_right (literal (valuationOf q) (-87)) (literal (valuationOf q) (1610)) (countLit q [-86]) (countLit q [-87]) (count1610 q) 1 (meaningNeg87 q) (meaning1610 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1428 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 1610 = true := counterClause1428 (baseVal q)

theorem counterClause1429 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1610 = true := by
  have hs : count1610 q = (countLit q [-86]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-87])
  have hm := merge_left (literal (valuationOf q) (-86)) (literal (valuationOf q) (1610)) (countLit q [-86]) (countLit q [-87]) (count1610 q) 1 (meaningNeg86 q) (meaning1610 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1429 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1610 = true := counterClause1429 (baseVal q)

theorem counterClause1430 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 87 = true ∨ valuationOf q 1611 = true := by
  have hs : count1610 q = (countLit q [-86]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-87])
  have hm := merge_two (literal (valuationOf q) (-86)) (literal (valuationOf q) (-87)) (literal (valuationOf q) (1611)) (countLit q [-86]) (countLit q [-87]) (count1610 q) 1 1 (meaningNeg86 q) (meaningNeg87 q) (meaning1611 q) hs
  change (! (valuationOf q 86)) = false ∨ (! (valuationOf q 87)) = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1430 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 87 = true ∨ valuation q 1611 = true := counterClause1430 (baseVal q)

theorem counterClause1431 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1612 = true := by
  have hs : count1612 q = (countLit q [-83, -84]) + (countLit q [-86, -87]) := List.countP_append (p := literal q) (l₁ := [-83, -84]) (l₂ := [-86, -87])
  have hm := merge_right (literal (valuationOf q) (1610)) (literal (valuationOf q) (1612)) (countLit q [-83, -84]) (countLit q [-86, -87]) (count1612 q) 1 (meaning1610 q) (meaning1612 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1431 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1612 = true := counterClause1431 (baseVal q)

theorem counterClause1432 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1613 = true := by
  have hs : count1612 q = (countLit q [-83, -84]) + (countLit q [-86, -87]) := List.countP_append (p := literal q) (l₁ := [-83, -84]) (l₂ := [-86, -87])
  have hm := merge_right (literal (valuationOf q) (1611)) (literal (valuationOf q) (1613)) (countLit q [-83, -84]) (countLit q [-86, -87]) (count1612 q) 2 (meaning1611 q) (meaning1613 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1432 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1613 = true := counterClause1432 (baseVal q)

theorem counterClause1433 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1612 = true := by
  have hs : count1612 q = (countLit q [-83, -84]) + (countLit q [-86, -87]) := List.countP_append (p := literal q) (l₁ := [-83, -84]) (l₂ := [-86, -87])
  have hm := merge_left (literal (valuationOf q) (1608)) (literal (valuationOf q) (1612)) (countLit q [-83, -84]) (countLit q [-86, -87]) (count1612 q) 1 (meaning1608 q) (meaning1612 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1433 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1612 = true := counterClause1433 (baseVal q)

theorem counterClause1434 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1613 = true := by
  have hs : count1612 q = (countLit q [-83, -84]) + (countLit q [-86, -87]) := List.countP_append (p := literal q) (l₁ := [-83, -84]) (l₂ := [-86, -87])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1613)) (countLit q [-83, -84]) (countLit q [-86, -87]) (count1612 q) 1 1 (meaning1608 q) (meaning1610 q) (meaning1613 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1434 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1610 = false ∨ valuation q 1613 = true := counterClause1434 (baseVal q)

theorem counterClause1435 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1614 = true := by
  have hs : count1612 q = (countLit q [-83, -84]) + (countLit q [-86, -87]) := List.countP_append (p := literal q) (l₁ := [-83, -84]) (l₂ := [-86, -87])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1614)) (countLit q [-83, -84]) (countLit q [-86, -87]) (count1612 q) 1 2 (meaning1608 q) (meaning1611 q) (meaning1614 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1435 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1611 = false ∨ valuation q 1614 = true := counterClause1435 (baseVal q)

theorem counterClause1436 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1613 = true := by
  have hs : count1612 q = (countLit q [-83, -84]) + (countLit q [-86, -87]) := List.countP_append (p := literal q) (l₁ := [-83, -84]) (l₂ := [-86, -87])
  have hm := merge_left (literal (valuationOf q) (1609)) (literal (valuationOf q) (1613)) (countLit q [-83, -84]) (countLit q [-86, -87]) (count1612 q) 2 (meaning1609 q) (meaning1613 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1436 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1613 = true := counterClause1436 (baseVal q)

theorem counterClause1437 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1614 = true := by
  have hs : count1612 q = (countLit q [-83, -84]) + (countLit q [-86, -87]) := List.countP_append (p := literal q) (l₁ := [-83, -84]) (l₂ := [-86, -87])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1614)) (countLit q [-83, -84]) (countLit q [-86, -87]) (count1612 q) 2 1 (meaning1609 q) (meaning1610 q) (meaning1614 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1437 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1610 = false ∨ valuation q 1614 = true := counterClause1437 (baseVal q)

theorem counterClause1438 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1615 = true := by
  have hs : count1612 q = (countLit q [-83, -84]) + (countLit q [-86, -87]) := List.countP_append (p := literal q) (l₁ := [-83, -84]) (l₂ := [-86, -87])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1615)) (countLit q [-83, -84]) (countLit q [-86, -87]) (count1612 q) 2 2 (meaning1609 q) (meaning1611 q) (meaning1615 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1438 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1611 = false ∨ valuation q 1615 = true := counterClause1438 (baseVal q)

theorem counterClause1439 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1616 = true := by
  have hs : count1616 q = (countLit q [-75, -78, -80, -82]) + (countLit q [-83, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-75, -78, -80, -82]) (l₂ := [-83, -84, -86, -87])
  have hm := merge_right (literal (valuationOf q) (1612)) (literal (valuationOf q) (1616)) (countLit q [-75, -78, -80, -82]) (countLit q [-83, -84, -86, -87]) (count1616 q) 1 (meaning1612 q) (meaning1616 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1439 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1616 = true := counterClause1439 (baseVal q)

theorem counterClause1440 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1617 = true := by
  have hs : count1616 q = (countLit q [-75, -78, -80, -82]) + (countLit q [-83, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-75, -78, -80, -82]) (l₂ := [-83, -84, -86, -87])
  have hm := merge_right (literal (valuationOf q) (1613)) (literal (valuationOf q) (1617)) (countLit q [-75, -78, -80, -82]) (countLit q [-83, -84, -86, -87]) (count1616 q) 2 (meaning1613 q) (meaning1617 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1440 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1617 = true := counterClause1440 (baseVal q)

theorem block44 (q : Snake 81) (h : Conditions q) : B112E004.Block44 (valuation q) :=
  ⟨clause1409 q h, clause1410 q h, clause1411 q h, clause1412 q h, clause1413 q h, clause1414 q h, clause1415 q h, clause1416 q h, clause1417 q h, clause1418 q h, clause1419 q h, clause1420 q h, clause1421 q h, clause1422 q h, clause1423 q h, clause1424 q h, clause1425 q h, clause1426 q h, clause1427 q h, clause1428 q h, clause1429 q h, clause1430 q h, clause1431 q h, clause1432 q h, clause1433 q h, clause1434 q h, clause1435 q h, clause1436 q h, clause1437 q h, clause1438 q h, clause1439 q h, clause1440 q h⟩

end
end Snake9.Regrowth.E112004
