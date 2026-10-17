import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec45 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1441 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1549 = true := by
  have hs : count1549 q = (countLit q [-77]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-79])
  have hm := merge_left (literal (valuationOf q) (-77)) (literal (valuationOf q) (1549)) (countLit q [-77]) (countLit q [-79]) (count1549 q) 1 (meaningNeg77 q) (meaning1549 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1441 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1549 = true := counterClause1441 (baseVal q)

theorem counterClause1442 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1551 = true := by
  have hs : count1551 q = (countLit q [-80]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-80]) (l₂ := [-81])
  have hm := merge_right (literal (valuationOf q) (-81)) (literal (valuationOf q) (1551)) (countLit q [-80]) (countLit q [-81]) (count1551 q) 1 (meaningNeg81 q) (meaning1551 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1442 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1551 = true := counterClause1442 (baseVal q)

theorem counterClause1443 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1553 = true := by
  have hs : count1553 q = (countLit q [-77, -79]) + (countLit q [-80, -81]) := List.countP_append (p := literal q) (l₁ := [-77, -79]) (l₂ := [-80, -81])
  have hm := merge_left (literal (valuationOf q) (1549)) (literal (valuationOf q) (1553)) (countLit q [-77, -79]) (countLit q [-80, -81]) (count1553 q) 1 (meaning1549 q) (meaning1553 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1443 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1553 = true := counterClause1443 (baseVal q)

theorem counterClause1444 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1554 = true := by
  have hs : count1553 q = (countLit q [-77, -79]) + (countLit q [-80, -81]) := List.countP_append (p := literal q) (l₁ := [-77, -79]) (l₂ := [-80, -81])
  have hm := merge_two (literal (valuationOf q) (1549)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1554)) (countLit q [-77, -79]) (countLit q [-80, -81]) (count1553 q) 1 1 (meaning1549 q) (meaning1551 q) (meaning1554 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1444 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1551 = false ∨ valuation q 1554 = true := counterClause1444 (baseVal q)

theorem counterClause1445 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1559 = true := by
  have hs : count1557 q = (countLit q [-72, -73, -76]) + (countLit q [-77, -79, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -76]) (l₂ := [-77, -79, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1559)) (countLit q [-72, -73, -76]) (countLit q [-77, -79, -80, -81]) (count1557 q) 1 2 (meaning1546 q) (meaning1554 q) (meaning1559 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1445 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1554 = false ∨ valuation q 1559 = true := counterClause1445 (baseVal q)

theorem counterClause1446 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1559 = true := by
  have hs : count1557 q = (countLit q [-72, -73, -76]) + (countLit q [-77, -79, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -76]) (l₂ := [-77, -79, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1559)) (countLit q [-72, -73, -76]) (countLit q [-77, -79, -80, -81]) (count1557 q) 2 1 (meaning1547 q) (meaning1553 q) (meaning1559 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1446 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1553 = false ∨ valuation q 1559 = true := counterClause1446 (baseVal q)

theorem counterClause1447 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1560 = true := by
  have hs : count1557 q = (countLit q [-72, -73, -76]) + (countLit q [-77, -79, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -76]) (l₂ := [-77, -79, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1560)) (countLit q [-72, -73, -76]) (countLit q [-77, -79, -80, -81]) (count1557 q) 2 2 (meaning1547 q) (meaning1554 q) (meaning1560 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1447 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1554 = false ∨ valuation q 1560 = true := counterClause1447 (baseVal q)

theorem counterClause1448 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1561 = true := by
  have hs : count1557 q = (countLit q [-72, -73, -76]) + (countLit q [-77, -79, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -76]) (l₂ := [-77, -79, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1561)) (countLit q [-72, -73, -76]) (countLit q [-77, -79, -80, -81]) (count1557 q) 3 2 (meaning1548 q) (meaning1554 q) (meaning1561 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1448 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1554 = false ∨ valuation q 1561 = true := counterClause1448 (baseVal q)

theorem counterClause1449 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1570 = true := by
  have hs : count1564 q = (countLit q [-58, -59, -61, -65, -67, -70, -71]) + (countLit q [-72, -73, -76, -77, -79, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -61, -65, -67, -70, -71]) (l₂ := [-72, -73, -76, -77, -79, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1539)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1570)) (countLit q [-58, -59, -61, -65, -67, -70, -71]) (countLit q [-72, -73, -76, -77, -79, -80, -81]) (count1564 q) 3 4 (meaning1539 q) (meaning1560 q) (meaning1570 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1449 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1560 = false ∨ valuation q 1570 = true := counterClause1449 (baseVal q)

theorem counterClause1450 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1571 = true := by
  have hs : count1564 q = (countLit q [-58, -59, -61, -65, -67, -70, -71]) + (countLit q [-72, -73, -76, -77, -79, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -61, -65, -67, -70, -71]) (l₂ := [-72, -73, -76, -77, -79, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1539)) (literal (valuationOf q) (1561)) (literal (valuationOf q) (1571)) (countLit q [-58, -59, -61, -65, -67, -70, -71]) (countLit q [-72, -73, -76, -77, -79, -80, -81]) (count1564 q) 3 5 (meaning1539 q) (meaning1561 q) (meaning1571 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1450 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1561 = false ∨ valuation q 1571 = true := counterClause1450 (baseVal q)

theorem counterClause1451 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1570 = true := by
  have hs : count1564 q = (countLit q [-58, -59, -61, -65, -67, -70, -71]) + (countLit q [-72, -73, -76, -77, -79, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -61, -65, -67, -70, -71]) (l₂ := [-72, -73, -76, -77, -79, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1540)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1570)) (countLit q [-58, -59, -61, -65, -67, -70, -71]) (countLit q [-72, -73, -76, -77, -79, -80, -81]) (count1564 q) 4 3 (meaning1540 q) (meaning1559 q) (meaning1570 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1451 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1559 = false ∨ valuation q 1570 = true := counterClause1451 (baseVal q)

theorem counterClause1452 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1571 = true := by
  have hs : count1564 q = (countLit q [-58, -59, -61, -65, -67, -70, -71]) + (countLit q [-72, -73, -76, -77, -79, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -61, -65, -67, -70, -71]) (l₂ := [-72, -73, -76, -77, -79, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1571)) (countLit q [-58, -59, -61, -65, -67, -70, -71]) (countLit q [-72, -73, -76, -77, -79, -80, -81]) (count1564 q) 5 3 (meaning1541 q) (meaning1559 q) (meaning1571 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1452 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1559 = false ∨ valuation q 1571 = true := counterClause1452 (baseVal q)

theorem counterClause1453 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1572 = true := by
  have hs : count1564 q = (countLit q [-58, -59, -61, -65, -67, -70, -71]) + (countLit q [-72, -73, -76, -77, -79, -80, -81]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -61, -65, -67, -70, -71]) (l₂ := [-72, -73, -76, -77, -79, -80, -81])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1572)) (countLit q [-58, -59, -61, -65, -67, -70, -71]) (countLit q [-72, -73, -76, -77, -79, -80, -81]) (count1564 q) 5 4 (meaning1541 q) (meaning1560 q) (meaning1572 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1453 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1560 = false ∨ valuation q 1572 = true := counterClause1453 (baseVal q)

theorem counterClause1454 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1578 = true := by
  have hs : count1578 q = (countLit q [-86]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-90])
  have hm := merge_right (literal (valuationOf q) (-90)) (literal (valuationOf q) (1578)) (countLit q [-86]) (countLit q [-90]) (count1578 q) 1 (meaningNeg90 q) (meaning1578 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1454 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1578 = true := counterClause1454 (baseVal q)

theorem counterClause1455 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1578 = true := by
  have hs : count1578 q = (countLit q [-86]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-90])
  have hm := merge_left (literal (valuationOf q) (-86)) (literal (valuationOf q) (1578)) (countLit q [-86]) (countLit q [-90]) (count1578 q) 1 (meaningNeg86 q) (meaning1578 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1455 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1578 = true := counterClause1455 (baseVal q)

theorem counterClause1456 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1580 = true := by
  have hs : count1580 q = (countLit q [-83]) + (countLit q [-86, -90]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-86, -90])
  have hm := merge_right (literal (valuationOf q) (1578)) (literal (valuationOf q) (1580)) (countLit q [-83]) (countLit q [-86, -90]) (count1580 q) 1 (meaning1578 q) (meaning1580 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1456 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1580 = true := counterClause1456 (baseVal q)

theorem counterClause1457 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 1580 = true := by
  have hs : count1580 q = (countLit q [-83]) + (countLit q [-86, -90]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-86, -90])
  have hm := merge_left (literal (valuationOf q) (-83)) (literal (valuationOf q) (1580)) (countLit q [-83]) (countLit q [-86, -90]) (count1580 q) 1 (meaningNeg83 q) (meaning1580 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1457 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 1580 = true := counterClause1457 (baseVal q)

theorem counterClause1458 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 1578 = false ∨ valuationOf q 1581 = true := by
  have hs : count1580 q = (countLit q [-83]) + (countLit q [-86, -90]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-86, -90])
  have hm := merge_two (literal (valuationOf q) (-83)) (literal (valuationOf q) (1578)) (literal (valuationOf q) (1581)) (countLit q [-83]) (countLit q [-86, -90]) (count1580 q) 1 1 (meaningNeg83 q) (meaning1578 q) (meaning1581 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1458 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 1578 = false ∨ valuation q 1581 = true := counterClause1458 (baseVal q)

theorem counterClause1459 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1583 = true := by
  have hs : count1583 q = (countLit q [-92]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93])
  have hm := merge_left (literal (valuationOf q) (-92)) (literal (valuationOf q) (1583)) (countLit q [-92]) (countLit q [-93]) (count1583 q) 1 (meaningNeg92 q) (meaning1583 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1459 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1583 = true := counterClause1459 (baseVal q)

theorem counterClause1460 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1587 = true := by
  have hs : count1587 q = (countLit q [-92, -93]) + (countLit q [-96, -98]) := List.countP_append (p := literal q) (l₁ := [-92, -93]) (l₂ := [-96, -98])
  have hm := merge_left (literal (valuationOf q) (1583)) (literal (valuationOf q) (1587)) (countLit q [-92, -93]) (countLit q [-96, -98]) (count1587 q) 1 (meaning1583 q) (meaning1587 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1460 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1587 = true := counterClause1460 (baseVal q)

theorem counterClause1461 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1591 = true := by
  have hs : count1591 q = (countLit q [-83, -86, -90]) + (countLit q [-92, -93, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-83, -86, -90]) (l₂ := [-92, -93, -96, -98])
  have hm := merge_right (literal (valuationOf q) (1587)) (literal (valuationOf q) (1591)) (countLit q [-83, -86, -90]) (countLit q [-92, -93, -96, -98]) (count1591 q) 1 (meaning1587 q) (meaning1591 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1461 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1591 = true := counterClause1461 (baseVal q)

theorem counterClause1462 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1591 = true := by
  have hs : count1591 q = (countLit q [-83, -86, -90]) + (countLit q [-92, -93, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-83, -86, -90]) (l₂ := [-92, -93, -96, -98])
  have hm := merge_left (literal (valuationOf q) (1580)) (literal (valuationOf q) (1591)) (countLit q [-83, -86, -90]) (countLit q [-92, -93, -96, -98]) (count1591 q) 1 (meaning1580 q) (meaning1591 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1462 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1591 = true := counterClause1462 (baseVal q)

theorem counterClause1463 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1592 = true := by
  have hs : count1591 q = (countLit q [-83, -86, -90]) + (countLit q [-92, -93, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-83, -86, -90]) (l₂ := [-92, -93, -96, -98])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1592)) (countLit q [-83, -86, -90]) (countLit q [-92, -93, -96, -98]) (count1591 q) 1 1 (meaning1580 q) (meaning1587 q) (meaning1592 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1463 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1587 = false ∨ valuation q 1592 = true := counterClause1463 (baseVal q)

theorem counterClause1464 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1592 = true := by
  have hs : count1591 q = (countLit q [-83, -86, -90]) + (countLit q [-92, -93, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-83, -86, -90]) (l₂ := [-92, -93, -96, -98])
  have hm := merge_left (literal (valuationOf q) (1581)) (literal (valuationOf q) (1592)) (countLit q [-83, -86, -90]) (countLit q [-92, -93, -96, -98]) (count1591 q) 2 (meaning1581 q) (meaning1592 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1464 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1592 = true := counterClause1464 (baseVal q)

theorem counterClause1465 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1593 = true := by
  have hs : count1591 q = (countLit q [-83, -86, -90]) + (countLit q [-92, -93, -96, -98]) := List.countP_append (p := literal q) (l₁ := [-83, -86, -90]) (l₂ := [-92, -93, -96, -98])
  have hm := merge_two (literal (valuationOf q) (1581)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1593)) (countLit q [-83, -86, -90]) (countLit q [-92, -93, -96, -98]) (count1591 q) 2 1 (meaning1581 q) (meaning1587 q) (meaning1593 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1465 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1587 = false ∨ valuation q 1593 = true := counterClause1465 (baseVal q)

theorem counterClause1466 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 1598 = true := by
  have hs : count1598 q = (countLit q [-100]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-102])
  have hm := merge_left (literal (valuationOf q) (-100)) (literal (valuationOf q) (1598)) (countLit q [-100]) (countLit q [-102]) (count1598 q) 1 (meaningNeg100 q) (meaning1598 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1466 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 1598 = true := counterClause1466 (baseVal q)

theorem counterClause1467 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 1600 = true := by
  have hs : count1600 q = (countLit q [-103]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-105])
  have hm := merge_right (literal (valuationOf q) (-105)) (literal (valuationOf q) (1600)) (countLit q [-103]) (countLit q [-105]) (count1600 q) 1 (meaningNeg105 q) (meaning1600 q) hs
  change (! (valuationOf q 105)) = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1467 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 1600 = true := counterClause1467 (baseVal q)

theorem counterClause1468 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1600 = true := by
  have hs : count1600 q = (countLit q [-103]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-105])
  have hm := merge_left (literal (valuationOf q) (-103)) (literal (valuationOf q) (1600)) (countLit q [-103]) (countLit q [-105]) (count1600 q) 1 (meaningNeg103 q) (meaning1600 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1468 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1600 = true := counterClause1468 (baseVal q)

theorem counterClause1469 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 105 = true ∨ valuationOf q 1601 = true := by
  have hs : count1600 q = (countLit q [-103]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-105])
  have hm := merge_two (literal (valuationOf q) (-103)) (literal (valuationOf q) (-105)) (literal (valuationOf q) (1601)) (countLit q [-103]) (countLit q [-105]) (count1600 q) 1 1 (meaningNeg103 q) (meaningNeg105 q) (meaning1601 q) hs
  change (! (valuationOf q 103)) = false ∨ (! (valuationOf q 105)) = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1469 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 105 = true ∨ valuation q 1601 = true := counterClause1469 (baseVal q)

theorem counterClause1470 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1602 = true := by
  have hs : count1602 q = (countLit q [-100, -102]) + (countLit q [-103, -105]) := List.countP_append (p := literal q) (l₁ := [-100, -102]) (l₂ := [-103, -105])
  have hm := merge_right (literal (valuationOf q) (1600)) (literal (valuationOf q) (1602)) (countLit q [-100, -102]) (countLit q [-103, -105]) (count1602 q) 1 (meaning1600 q) (meaning1602 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1470 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1602 = true := counterClause1470 (baseVal q)

theorem counterClause1471 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1603 = true := by
  have hs : count1602 q = (countLit q [-100, -102]) + (countLit q [-103, -105]) := List.countP_append (p := literal q) (l₁ := [-100, -102]) (l₂ := [-103, -105])
  have hm := merge_right (literal (valuationOf q) (1601)) (literal (valuationOf q) (1603)) (countLit q [-100, -102]) (countLit q [-103, -105]) (count1602 q) 2 (meaning1601 q) (meaning1603 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1471 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1603 = true := counterClause1471 (baseVal q)

theorem counterClause1472 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1602 = true := by
  have hs : count1602 q = (countLit q [-100, -102]) + (countLit q [-103, -105]) := List.countP_append (p := literal q) (l₁ := [-100, -102]) (l₂ := [-103, -105])
  have hm := merge_left (literal (valuationOf q) (1598)) (literal (valuationOf q) (1602)) (countLit q [-100, -102]) (countLit q [-103, -105]) (count1602 q) 1 (meaning1598 q) (meaning1602 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1472 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1602 = true := counterClause1472 (baseVal q)

theorem block45 (q : Snake 81) (h : Conditions q) : B112E259.Block45 (valuation q) :=
  ⟨clause1441 q h, clause1442 q h, clause1443 q h, clause1444 q h, clause1445 q h, clause1446 q h, clause1447 q h, clause1448 q h, clause1449 q h, clause1450 q h, clause1451 q h, clause1452 q h, clause1453 q h, clause1454 q h, clause1455 q h, clause1456 q h, clause1457 q h, clause1458 q h, clause1459 q h, clause1460 q h, clause1461 q h, clause1462 q h, clause1463 q h, clause1464 q h, clause1465 q h, clause1466 q h, clause1467 q h, clause1468 q h, clause1469 q h, clause1470 q h, clause1471 q h, clause1472 q h⟩

end
end Snake9.Regrowth.E112259
