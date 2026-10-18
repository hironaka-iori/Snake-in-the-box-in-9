import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec43 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1377 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1603 = true := by
  have hs : count1597 q = (countLit q [-59, -61, -63, -65, -68, -71, -73]) + (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73]) (l₂ := [-74, -77, -78, -80, -82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1603)) (countLit q [-59, -61, -63, -65, -68, -71, -73]) (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) (count1597 q) 6 1 (meaning1571 q) (meaning1589 q) (meaning1603 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1377 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1589 = false ∨ valuation q 1603 = true := counterClause1377 (baseVal q)

theorem counterClause1378 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1604 = true := by
  have hs : count1597 q = (countLit q [-59, -61, -63, -65, -68, -71, -73]) + (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73]) (l₂ := [-74, -77, -78, -80, -82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1604)) (countLit q [-59, -61, -63, -65, -68, -71, -73]) (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) (count1597 q) 6 2 (meaning1571 q) (meaning1590 q) (meaning1604 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1378 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1590 = false ∨ valuation q 1604 = true := counterClause1378 (baseVal q)

theorem counterClause1379 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1606 = true := by
  have hs : count1597 q = (countLit q [-59, -61, -63, -65, -68, -71, -73]) + (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73]) (l₂ := [-74, -77, -78, -80, -82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1606)) (countLit q [-59, -61, -63, -65, -68, -71, -73]) (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) (count1597 q) 6 4 (meaning1571 q) (meaning1592 q) (meaning1606 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1379 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1592 = false ∨ valuation q 1606 = true := counterClause1379 (baseVal q)

theorem counterClause1380 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1604 = true := by
  have hs : count1597 q = (countLit q [-59, -61, -63, -65, -68, -71, -73]) + (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73]) (l₂ := [-74, -77, -78, -80, -82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1604)) (countLit q [-59, -61, -63, -65, -68, -71, -73]) (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) (count1597 q) 7 1 (meaning1572 q) (meaning1589 q) (meaning1604 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1380 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1589 = false ∨ valuation q 1604 = true := counterClause1380 (baseVal q)

theorem counterClause1381 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1612 = true := by
  have hs : count1612 q = (countLit q [-92]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93])
  have hm := merge_right (literal (valuationOf q) (-93)) (literal (valuationOf q) (1612)) (countLit q [-92]) (countLit q [-93]) (count1612 q) 1 (meaningNeg93 q) (meaning1612 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1381 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1612 = true := counterClause1381 (baseVal q)

theorem counterClause1382 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1612 = true := by
  have hs : count1612 q = (countLit q [-92]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93])
  have hm := merge_left (literal (valuationOf q) (-92)) (literal (valuationOf q) (1612)) (countLit q [-92]) (countLit q [-93]) (count1612 q) 1 (meaningNeg92 q) (meaning1612 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1382 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1612 = true := counterClause1382 (baseVal q)

theorem counterClause1383 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 93 = true ∨ valuationOf q 1613 = true := by
  have hs : count1612 q = (countLit q [-92]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93])
  have hm := merge_two (literal (valuationOf q) (-92)) (literal (valuationOf q) (-93)) (literal (valuationOf q) (1613)) (countLit q [-92]) (countLit q [-93]) (count1612 q) 1 1 (meaningNeg92 q) (meaningNeg93 q) (meaning1613 q) hs
  change (! (valuationOf q 92)) = false ∨ (! (valuationOf q 93)) = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1383 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 93 = true ∨ valuation q 1613 = true := counterClause1383 (baseVal q)

theorem counterClause1384 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1614 = true := by
  have hs : count1614 q = (countLit q [-89]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-92, -93])
  have hm := merge_right (literal (valuationOf q) (1612)) (literal (valuationOf q) (1614)) (countLit q [-89]) (countLit q [-92, -93]) (count1614 q) 1 (meaning1612 q) (meaning1614 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1384 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1614 = true := counterClause1384 (baseVal q)

theorem counterClause1385 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1615 = true := by
  have hs : count1614 q = (countLit q [-89]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-92, -93])
  have hm := merge_right (literal (valuationOf q) (1613)) (literal (valuationOf q) (1615)) (countLit q [-89]) (countLit q [-92, -93]) (count1614 q) 2 (meaning1613 q) (meaning1615 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1385 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1615 = true := counterClause1385 (baseVal q)

theorem counterClause1386 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 1614 = true := by
  have hs : count1614 q = (countLit q [-89]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-92, -93])
  have hm := merge_left (literal (valuationOf q) (-89)) (literal (valuationOf q) (1614)) (countLit q [-89]) (countLit q [-92, -93]) (count1614 q) 1 (meaningNeg89 q) (meaning1614 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1386 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 1614 = true := counterClause1386 (baseVal q)

theorem counterClause1387 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 1612 = false ∨ valuationOf q 1615 = true := by
  have hs : count1614 q = (countLit q [-89]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-92, -93])
  have hm := merge_two (literal (valuationOf q) (-89)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1615)) (countLit q [-89]) (countLit q [-92, -93]) (count1614 q) 1 1 (meaningNeg89 q) (meaning1612 q) (meaning1615 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1387 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 1612 = false ∨ valuation q 1615 = true := counterClause1387 (baseVal q)

theorem counterClause1388 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 1613 = false ∨ valuationOf q 1616 = true := by
  have hs : count1614 q = (countLit q [-89]) + (countLit q [-92, -93]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-92, -93])
  have hm := merge_two (literal (valuationOf q) (-89)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1616)) (countLit q [-89]) (countLit q [-92, -93]) (count1614 q) 1 2 (meaningNeg89 q) (meaning1613 q) (meaning1616 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1388 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 1613 = false ∨ valuation q 1616 = true := counterClause1388 (baseVal q)

theorem counterClause1389 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1617 = true := by
  have hs : count1617 q = (countLit q [-95]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-98])
  have hm := merge_right (literal (valuationOf q) (-98)) (literal (valuationOf q) (1617)) (countLit q [-95]) (countLit q [-98]) (count1617 q) 1 (meaningNeg98 q) (meaning1617 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1389 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1617 = true := counterClause1389 (baseVal q)

theorem counterClause1390 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 1617 = true := by
  have hs : count1617 q = (countLit q [-95]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-98])
  have hm := merge_left (literal (valuationOf q) (-95)) (literal (valuationOf q) (1617)) (countLit q [-95]) (countLit q [-98]) (count1617 q) 1 (meaningNeg95 q) (meaning1617 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1390 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 1617 = true := counterClause1390 (baseVal q)

theorem counterClause1391 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 98 = true ∨ valuationOf q 1618 = true := by
  have hs : count1617 q = (countLit q [-95]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-98])
  have hm := merge_two (literal (valuationOf q) (-95)) (literal (valuationOf q) (-98)) (literal (valuationOf q) (1618)) (countLit q [-95]) (countLit q [-98]) (count1617 q) 1 1 (meaningNeg95 q) (meaningNeg98 q) (meaning1618 q) hs
  change (! (valuationOf q 95)) = false ∨ (! (valuationOf q 98)) = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1391 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 98 = true ∨ valuation q 1618 = true := counterClause1391 (baseVal q)

theorem counterClause1392 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 1619 = true := by
  have hs : count1619 q = (countLit q [-100]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-102])
  have hm := merge_right (literal (valuationOf q) (-102)) (literal (valuationOf q) (1619)) (countLit q [-100]) (countLit q [-102]) (count1619 q) 1 (meaningNeg102 q) (meaning1619 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1392 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 1619 = true := counterClause1392 (baseVal q)

theorem counterClause1393 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 1619 = true := by
  have hs : count1619 q = (countLit q [-100]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-102])
  have hm := merge_left (literal (valuationOf q) (-100)) (literal (valuationOf q) (1619)) (countLit q [-100]) (countLit q [-102]) (count1619 q) 1 (meaningNeg100 q) (meaning1619 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1393 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 1619 = true := counterClause1393 (baseVal q)

theorem counterClause1394 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 102 = true ∨ valuationOf q 1620 = true := by
  have hs : count1619 q = (countLit q [-100]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-102])
  have hm := merge_two (literal (valuationOf q) (-100)) (literal (valuationOf q) (-102)) (literal (valuationOf q) (1620)) (countLit q [-100]) (countLit q [-102]) (count1619 q) 1 1 (meaningNeg100 q) (meaningNeg102 q) (meaning1620 q) hs
  change (! (valuationOf q 100)) = false ∨ (! (valuationOf q 102)) = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1394 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 102 = true ∨ valuation q 1620 = true := counterClause1394 (baseVal q)

theorem counterClause1395 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1621 = true := by
  have hs : count1621 q = (countLit q [-95, -98]) + (countLit q [-100, -102]) := List.countP_append (p := literal q) (l₁ := [-95, -98]) (l₂ := [-100, -102])
  have hm := merge_right (literal (valuationOf q) (1619)) (literal (valuationOf q) (1621)) (countLit q [-95, -98]) (countLit q [-100, -102]) (count1621 q) 1 (meaning1619 q) (meaning1621 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1395 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1621 = true := counterClause1395 (baseVal q)

theorem counterClause1396 (q : Nat → Bool) : valuationOf q 1620 = false ∨ valuationOf q 1622 = true := by
  have hs : count1621 q = (countLit q [-95, -98]) + (countLit q [-100, -102]) := List.countP_append (p := literal q) (l₁ := [-95, -98]) (l₂ := [-100, -102])
  have hm := merge_right (literal (valuationOf q) (1620)) (literal (valuationOf q) (1622)) (countLit q [-95, -98]) (countLit q [-100, -102]) (count1621 q) 2 (meaning1620 q) (meaning1622 q) hs
  change valuationOf q 1620 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1396 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1622 = true := counterClause1396 (baseVal q)

theorem counterClause1397 (q : Nat → Bool) : valuationOf q 1617 = false ∨ valuationOf q 1621 = true := by
  have hs : count1621 q = (countLit q [-95, -98]) + (countLit q [-100, -102]) := List.countP_append (p := literal q) (l₁ := [-95, -98]) (l₂ := [-100, -102])
  have hm := merge_left (literal (valuationOf q) (1617)) (literal (valuationOf q) (1621)) (countLit q [-95, -98]) (countLit q [-100, -102]) (count1621 q) 1 (meaning1617 q) (meaning1621 q) hs
  change valuationOf q 1617 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1397 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1621 = true := counterClause1397 (baseVal q)

theorem counterClause1398 (q : Nat → Bool) : valuationOf q 1617 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1622 = true := by
  have hs : count1621 q = (countLit q [-95, -98]) + (countLit q [-100, -102]) := List.countP_append (p := literal q) (l₁ := [-95, -98]) (l₂ := [-100, -102])
  have hm := merge_two (literal (valuationOf q) (1617)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1622)) (countLit q [-95, -98]) (countLit q [-100, -102]) (count1621 q) 1 1 (meaning1617 q) (meaning1619 q) (meaning1622 q) hs
  change valuationOf q 1617 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1398 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1619 = false ∨ valuation q 1622 = true := counterClause1398 (baseVal q)

theorem counterClause1399 (q : Nat → Bool) : valuationOf q 1617 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1623 = true := by
  have hs : count1621 q = (countLit q [-95, -98]) + (countLit q [-100, -102]) := List.countP_append (p := literal q) (l₁ := [-95, -98]) (l₂ := [-100, -102])
  have hm := merge_two (literal (valuationOf q) (1617)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1623)) (countLit q [-95, -98]) (countLit q [-100, -102]) (count1621 q) 1 2 (meaning1617 q) (meaning1620 q) (meaning1623 q) hs
  change valuationOf q 1617 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1399 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1620 = false ∨ valuation q 1623 = true := counterClause1399 (baseVal q)

theorem counterClause1400 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1622 = true := by
  have hs : count1621 q = (countLit q [-95, -98]) + (countLit q [-100, -102]) := List.countP_append (p := literal q) (l₁ := [-95, -98]) (l₂ := [-100, -102])
  have hm := merge_left (literal (valuationOf q) (1618)) (literal (valuationOf q) (1622)) (countLit q [-95, -98]) (countLit q [-100, -102]) (count1621 q) 2 (meaning1618 q) (meaning1622 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1400 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1622 = true := counterClause1400 (baseVal q)

theorem counterClause1401 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1623 = true := by
  have hs : count1621 q = (countLit q [-95, -98]) + (countLit q [-100, -102]) := List.countP_append (p := literal q) (l₁ := [-95, -98]) (l₂ := [-100, -102])
  have hm := merge_two (literal (valuationOf q) (1618)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1623)) (countLit q [-95, -98]) (countLit q [-100, -102]) (count1621 q) 2 1 (meaning1618 q) (meaning1619 q) (meaning1623 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1401 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1619 = false ∨ valuation q 1623 = true := counterClause1401 (baseVal q)

theorem counterClause1402 (q : Nat → Bool) : valuationOf q 1621 = false ∨ valuationOf q 1625 = true := by
  have hs : count1625 q = (countLit q [-89, -92, -93]) + (countLit q [-95, -98, -100, -102]) := List.countP_append (p := literal q) (l₁ := [-89, -92, -93]) (l₂ := [-95, -98, -100, -102])
  have hm := merge_right (literal (valuationOf q) (1621)) (literal (valuationOf q) (1625)) (countLit q [-89, -92, -93]) (countLit q [-95, -98, -100, -102]) (count1625 q) 1 (meaning1621 q) (meaning1625 q) hs
  change valuationOf q 1621 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1402 (q : Snake 81) (h : Conditions q) : valuation q 1621 = false ∨ valuation q 1625 = true := counterClause1402 (baseVal q)

theorem counterClause1403 (q : Nat → Bool) : valuationOf q 1622 = false ∨ valuationOf q 1626 = true := by
  have hs : count1625 q = (countLit q [-89, -92, -93]) + (countLit q [-95, -98, -100, -102]) := List.countP_append (p := literal q) (l₁ := [-89, -92, -93]) (l₂ := [-95, -98, -100, -102])
  have hm := merge_right (literal (valuationOf q) (1622)) (literal (valuationOf q) (1626)) (countLit q [-89, -92, -93]) (countLit q [-95, -98, -100, -102]) (count1625 q) 2 (meaning1622 q) (meaning1626 q) hs
  change valuationOf q 1622 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1403 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1626 = true := counterClause1403 (baseVal q)

theorem counterClause1404 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1627 = true := by
  have hs : count1625 q = (countLit q [-89, -92, -93]) + (countLit q [-95, -98, -100, -102]) := List.countP_append (p := literal q) (l₁ := [-89, -92, -93]) (l₂ := [-95, -98, -100, -102])
  have hm := merge_right (literal (valuationOf q) (1623)) (literal (valuationOf q) (1627)) (countLit q [-89, -92, -93]) (countLit q [-95, -98, -100, -102]) (count1625 q) 3 (meaning1623 q) (meaning1627 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1404 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1627 = true := counterClause1404 (baseVal q)

theorem counterClause1405 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1625 = true := by
  have hs : count1625 q = (countLit q [-89, -92, -93]) + (countLit q [-95, -98, -100, -102]) := List.countP_append (p := literal q) (l₁ := [-89, -92, -93]) (l₂ := [-95, -98, -100, -102])
  have hm := merge_left (literal (valuationOf q) (1614)) (literal (valuationOf q) (1625)) (countLit q [-89, -92, -93]) (countLit q [-95, -98, -100, -102]) (count1625 q) 1 (meaning1614 q) (meaning1625 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1405 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1625 = true := counterClause1405 (baseVal q)

theorem counterClause1406 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1626 = true := by
  have hs : count1625 q = (countLit q [-89, -92, -93]) + (countLit q [-95, -98, -100, -102]) := List.countP_append (p := literal q) (l₁ := [-89, -92, -93]) (l₂ := [-95, -98, -100, -102])
  have hm := merge_two (literal (valuationOf q) (1614)) (literal (valuationOf q) (1621)) (literal (valuationOf q) (1626)) (countLit q [-89, -92, -93]) (countLit q [-95, -98, -100, -102]) (count1625 q) 1 1 (meaning1614 q) (meaning1621 q) (meaning1626 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1406 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1621 = false ∨ valuation q 1626 = true := counterClause1406 (baseVal q)

theorem counterClause1407 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1627 = true := by
  have hs : count1625 q = (countLit q [-89, -92, -93]) + (countLit q [-95, -98, -100, -102]) := List.countP_append (p := literal q) (l₁ := [-89, -92, -93]) (l₂ := [-95, -98, -100, -102])
  have hm := merge_two (literal (valuationOf q) (1614)) (literal (valuationOf q) (1622)) (literal (valuationOf q) (1627)) (countLit q [-89, -92, -93]) (countLit q [-95, -98, -100, -102]) (count1625 q) 1 2 (meaning1614 q) (meaning1622 q) (meaning1627 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1622 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1407 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1622 = false ∨ valuation q 1627 = true := counterClause1407 (baseVal q)

theorem counterClause1408 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1623 = false ∨ valuationOf q 1628 = true := by
  have hs : count1625 q = (countLit q [-89, -92, -93]) + (countLit q [-95, -98, -100, -102]) := List.countP_append (p := literal q) (l₁ := [-89, -92, -93]) (l₂ := [-95, -98, -100, -102])
  have hm := merge_two (literal (valuationOf q) (1614)) (literal (valuationOf q) (1623)) (literal (valuationOf q) (1628)) (countLit q [-89, -92, -93]) (countLit q [-95, -98, -100, -102]) (count1625 q) 1 3 (meaning1614 q) (meaning1623 q) (meaning1628 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1623 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1408 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1623 = false ∨ valuation q 1628 = true := counterClause1408 (baseVal q)

theorem block43 (q : Snake 81) (h : Conditions q) : B112E158.Block43 (valuation q) :=
  ⟨clause1377 q h, clause1378 q h, clause1379 q h, clause1380 q h, clause1381 q h, clause1382 q h, clause1383 q h, clause1384 q h, clause1385 q h, clause1386 q h, clause1387 q h, clause1388 q h, clause1389 q h, clause1390 q h, clause1391 q h, clause1392 q h, clause1393 q h, clause1394 q h, clause1395 q h, clause1396 q h, clause1397 q h, clause1398 q h, clause1399 q h, clause1400 q h, clause1401 q h, clause1402 q h, clause1403 q h, clause1404 q h, clause1405 q h, clause1406 q h, clause1407 q h, clause1408 q h⟩

end
end Snake9.Regrowth.E112158
