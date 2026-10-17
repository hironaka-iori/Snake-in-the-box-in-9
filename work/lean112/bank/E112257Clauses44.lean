import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec44 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1409 (q : Nat → Bool) : valuationOf q 1550 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1556 = true := by
  have hs : count1553 q = (countLit q [-78, -80]) + (countLit q [-83, -84]) := List.countP_append (p := literal q) (l₁ := [-78, -80]) (l₂ := [-83, -84])
  have hm := merge_two (literal (valuationOf q) (1550)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1556)) (countLit q [-78, -80]) (countLit q [-83, -84]) (count1553 q) 2 2 (meaning1550 q) (meaning1552 q) (meaning1556 q) hs
  change valuationOf q 1550 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1409 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1552 = false ∨ valuation q 1556 = true := counterClause1409 (baseVal q)

theorem counterClause1410 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1558 = true := by
  have hs : count1557 q = (countLit q [-74, -76, -77]) + (countLit q [-78, -80, -83, -84]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -77]) (l₂ := [-78, -80, -83, -84])
  have hm := merge_right (literal (valuationOf q) (1554)) (literal (valuationOf q) (1558)) (countLit q [-74, -76, -77]) (countLit q [-78, -80, -83, -84]) (count1557 q) 2 (meaning1554 q) (meaning1558 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1410 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1558 = true := counterClause1410 (baseVal q)

theorem counterClause1411 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1559 = true := by
  have hs : count1557 q = (countLit q [-74, -76, -77]) + (countLit q [-78, -80, -83, -84]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -77]) (l₂ := [-78, -80, -83, -84])
  have hm := merge_right (literal (valuationOf q) (1555)) (literal (valuationOf q) (1559)) (countLit q [-74, -76, -77]) (countLit q [-78, -80, -83, -84]) (count1557 q) 3 (meaning1555 q) (meaning1559 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1411 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1559 = true := counterClause1411 (baseVal q)

theorem counterClause1412 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1560 = true := by
  have hs : count1557 q = (countLit q [-74, -76, -77]) + (countLit q [-78, -80, -83, -84]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -77]) (l₂ := [-78, -80, -83, -84])
  have hm := merge_right (literal (valuationOf q) (1556)) (literal (valuationOf q) (1560)) (countLit q [-74, -76, -77]) (countLit q [-78, -80, -83, -84]) (count1557 q) 4 (meaning1556 q) (meaning1560 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1412 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1560 = true := counterClause1412 (baseVal q)

theorem counterClause1413 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1558 = true := by
  have hs : count1557 q = (countLit q [-74, -76, -77]) + (countLit q [-78, -80, -83, -84]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -77]) (l₂ := [-78, -80, -83, -84])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1558)) (countLit q [-74, -76, -77]) (countLit q [-78, -80, -83, -84]) (count1557 q) 1 1 (meaning1546 q) (meaning1553 q) (meaning1558 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1413 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1553 = false ∨ valuation q 1558 = true := counterClause1413 (baseVal q)

theorem counterClause1414 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1559 = true := by
  have hs : count1557 q = (countLit q [-74, -76, -77]) + (countLit q [-78, -80, -83, -84]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -77]) (l₂ := [-78, -80, -83, -84])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1559)) (countLit q [-74, -76, -77]) (countLit q [-78, -80, -83, -84]) (count1557 q) 1 2 (meaning1546 q) (meaning1554 q) (meaning1559 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1414 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1554 = false ∨ valuation q 1559 = true := counterClause1414 (baseVal q)

theorem counterClause1415 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1560 = true := by
  have hs : count1557 q = (countLit q [-74, -76, -77]) + (countLit q [-78, -80, -83, -84]) := List.countP_append (p := literal q) (l₁ := [-74, -76, -77]) (l₂ := [-78, -80, -83, -84])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1555)) (literal (valuationOf q) (1560)) (countLit q [-74, -76, -77]) (countLit q [-78, -80, -83, -84]) (count1557 q) 1 3 (meaning1546 q) (meaning1555 q) (meaning1560 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1415 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1555 = false ∨ valuation q 1560 = true := counterClause1415 (baseVal q)

theorem counterClause1416 (q : Nat → Bool) : valuationOf q 1538 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1567 = true := by
  have hs : count1564 q = (countLit q [-57, -58, -61, -65, -67, -69, -73]) + (countLit q [-74, -76, -77, -78, -80, -83, -84]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -65, -67, -69, -73]) (l₂ := [-74, -76, -77, -78, -80, -83, -84])
  have hm := merge_two (literal (valuationOf q) (1538)) (literal (valuationOf q) (1558)) (literal (valuationOf q) (1567)) (countLit q [-57, -58, -61, -65, -67, -69, -73]) (countLit q [-74, -76, -77, -78, -80, -83, -84]) (count1564 q) 2 2 (meaning1538 q) (meaning1558 q) (meaning1567 q) hs
  change valuationOf q 1538 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1416 (q : Snake 81) (h : Conditions q) : valuation q 1538 = false ∨ valuation q 1558 = false ∨ valuation q 1567 = true := counterClause1416 (baseVal q)

theorem counterClause1417 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1568 = true := by
  have hs : count1564 q = (countLit q [-57, -58, -61, -65, -67, -69, -73]) + (countLit q [-74, -76, -77, -78, -80, -83, -84]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -65, -67, -69, -73]) (l₂ := [-74, -76, -77, -78, -80, -83, -84])
  have hm := merge_two (literal (valuationOf q) (1539)) (literal (valuationOf q) (1558)) (literal (valuationOf q) (1568)) (countLit q [-57, -58, -61, -65, -67, -69, -73]) (countLit q [-74, -76, -77, -78, -80, -83, -84]) (count1564 q) 3 2 (meaning1539 q) (meaning1558 q) (meaning1568 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1417 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1558 = false ∨ valuation q 1568 = true := counterClause1417 (baseVal q)

theorem counterClause1418 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1569 = true := by
  have hs : count1564 q = (countLit q [-57, -58, -61, -65, -67, -69, -73]) + (countLit q [-74, -76, -77, -78, -80, -83, -84]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -65, -67, -69, -73]) (l₂ := [-74, -76, -77, -78, -80, -83, -84])
  have hm := merge_two (literal (valuationOf q) (1539)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1569)) (countLit q [-57, -58, -61, -65, -67, -69, -73]) (countLit q [-74, -76, -77, -78, -80, -83, -84]) (count1564 q) 3 3 (meaning1539 q) (meaning1559 q) (meaning1569 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1418 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1559 = false ∨ valuation q 1569 = true := counterClause1418 (baseVal q)

theorem counterClause1419 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1570 = true := by
  have hs : count1564 q = (countLit q [-57, -58, -61, -65, -67, -69, -73]) + (countLit q [-74, -76, -77, -78, -80, -83, -84]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -65, -67, -69, -73]) (l₂ := [-74, -76, -77, -78, -80, -83, -84])
  have hm := merge_two (literal (valuationOf q) (1539)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1570)) (countLit q [-57, -58, -61, -65, -67, -69, -73]) (countLit q [-74, -76, -77, -78, -80, -83, -84]) (count1564 q) 3 4 (meaning1539 q) (meaning1560 q) (meaning1570 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1419 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1560 = false ∨ valuation q 1570 = true := counterClause1419 (baseVal q)

theorem counterClause1420 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1570 = true := by
  have hs : count1564 q = (countLit q [-57, -58, -61, -65, -67, -69, -73]) + (countLit q [-74, -76, -77, -78, -80, -83, -84]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -65, -67, -69, -73]) (l₂ := [-74, -76, -77, -78, -80, -83, -84])
  have hm := merge_two (literal (valuationOf q) (1540)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1570)) (countLit q [-57, -58, -61, -65, -67, -69, -73]) (countLit q [-74, -76, -77, -78, -80, -83, -84]) (count1564 q) 4 3 (meaning1540 q) (meaning1559 q) (meaning1570 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1420 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1559 = false ∨ valuation q 1570 = true := counterClause1420 (baseVal q)

theorem counterClause1421 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1571 = true := by
  have hs : count1564 q = (countLit q [-57, -58, -61, -65, -67, -69, -73]) + (countLit q [-74, -76, -77, -78, -80, -83, -84]) := List.countP_append (p := literal q) (l₁ := [-57, -58, -61, -65, -67, -69, -73]) (l₂ := [-74, -76, -77, -78, -80, -83, -84])
  have hm := merge_two (literal (valuationOf q) (1540)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1571)) (countLit q [-57, -58, -61, -65, -67, -69, -73]) (countLit q [-74, -76, -77, -78, -80, -83, -84]) (count1564 q) 4 4 (meaning1540 q) (meaning1560 q) (meaning1571 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1421 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1560 = false ∨ valuation q 1571 = true := counterClause1421 (baseVal q)

theorem counterClause1422 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1578 = true := by
  have hs : count1578 q = (countLit q [-88]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90])
  have hm := merge_right (literal (valuationOf q) (-90)) (literal (valuationOf q) (1578)) (countLit q [-88]) (countLit q [-90]) (count1578 q) 1 (meaningNeg90 q) (meaning1578 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1422 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1578 = true := counterClause1422 (baseVal q)

theorem counterClause1423 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1578 = true := by
  have hs : count1578 q = (countLit q [-88]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90])
  have hm := merge_left (literal (valuationOf q) (-88)) (literal (valuationOf q) (1578)) (countLit q [-88]) (countLit q [-90]) (count1578 q) 1 (meaningNeg88 q) (meaning1578 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1423 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1578 = true := counterClause1423 (baseVal q)

theorem counterClause1424 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1580 = true := by
  have hs : count1580 q = (countLit q [-86]) + (countLit q [-88, -90]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-88, -90])
  have hm := merge_right (literal (valuationOf q) (1578)) (literal (valuationOf q) (1580)) (countLit q [-86]) (countLit q [-88, -90]) (count1580 q) 1 (meaning1578 q) (meaning1580 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1424 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1580 = true := counterClause1424 (baseVal q)

theorem counterClause1425 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1578 = false ∨ valuationOf q 1581 = true := by
  have hs : count1580 q = (countLit q [-86]) + (countLit q [-88, -90]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-88, -90])
  have hm := merge_two (literal (valuationOf q) (-86)) (literal (valuationOf q) (1578)) (literal (valuationOf q) (1581)) (countLit q [-86]) (countLit q [-88, -90]) (count1580 q) 1 1 (meaningNeg86 q) (meaning1578 q) (meaning1581 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1425 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1578 = false ∨ valuation q 1581 = true := counterClause1425 (baseVal q)

theorem counterClause1426 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1583 = true := by
  have hs : count1583 q = (countLit q [-92]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-94])
  have hm := merge_right (literal (valuationOf q) (-94)) (literal (valuationOf q) (1583)) (countLit q [-92]) (countLit q [-94]) (count1583 q) 1 (meaningNeg94 q) (meaning1583 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1426 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1583 = true := counterClause1426 (baseVal q)

theorem counterClause1427 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1583 = true := by
  have hs : count1583 q = (countLit q [-92]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-94])
  have hm := merge_left (literal (valuationOf q) (-92)) (literal (valuationOf q) (1583)) (countLit q [-92]) (countLit q [-94]) (count1583 q) 1 (meaningNeg92 q) (meaning1583 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1427 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1583 = true := counterClause1427 (baseVal q)

theorem counterClause1428 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1585 = true := by
  have hs : count1585 q = (countLit q [-96]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-97])
  have hm := merge_right (literal (valuationOf q) (-97)) (literal (valuationOf q) (1585)) (countLit q [-96]) (countLit q [-97]) (count1585 q) 1 (meaningNeg97 q) (meaning1585 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1428 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1585 = true := counterClause1428 (baseVal q)

theorem counterClause1429 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1587 = true := by
  have hs : count1587 q = (countLit q [-92, -94]) + (countLit q [-96, -97]) := List.countP_append (p := literal q) (l₁ := [-92, -94]) (l₂ := [-96, -97])
  have hm := merge_left (literal (valuationOf q) (1583)) (literal (valuationOf q) (1587)) (countLit q [-92, -94]) (countLit q [-96, -97]) (count1587 q) 1 (meaning1583 q) (meaning1587 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1429 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1587 = true := counterClause1429 (baseVal q)

theorem counterClause1430 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1588 = true := by
  have hs : count1587 q = (countLit q [-92, -94]) + (countLit q [-96, -97]) := List.countP_append (p := literal q) (l₁ := [-92, -94]) (l₂ := [-96, -97])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1585)) (literal (valuationOf q) (1588)) (countLit q [-92, -94]) (countLit q [-96, -97]) (count1587 q) 1 1 (meaning1583 q) (meaning1585 q) (meaning1588 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1430 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1585 = false ∨ valuation q 1588 = true := counterClause1430 (baseVal q)

theorem counterClause1431 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1593 = true := by
  have hs : count1591 q = (countLit q [-86, -88, -90]) + (countLit q [-92, -94, -96, -97]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -90]) (l₂ := [-92, -94, -96, -97])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1588)) (literal (valuationOf q) (1593)) (countLit q [-86, -88, -90]) (countLit q [-92, -94, -96, -97]) (count1591 q) 1 2 (meaning1580 q) (meaning1588 q) (meaning1593 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1431 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1588 = false ∨ valuation q 1593 = true := counterClause1431 (baseVal q)

theorem counterClause1432 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1593 = true := by
  have hs : count1591 q = (countLit q [-86, -88, -90]) + (countLit q [-92, -94, -96, -97]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -90]) (l₂ := [-92, -94, -96, -97])
  have hm := merge_two (literal (valuationOf q) (1581)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1593)) (countLit q [-86, -88, -90]) (countLit q [-92, -94, -96, -97]) (count1591 q) 2 1 (meaning1581 q) (meaning1587 q) (meaning1593 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1432 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1587 = false ∨ valuation q 1593 = true := counterClause1432 (baseVal q)

theorem counterClause1433 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1594 = true := by
  have hs : count1591 q = (countLit q [-86, -88, -90]) + (countLit q [-92, -94, -96, -97]) := List.countP_append (p := literal q) (l₁ := [-86, -88, -90]) (l₂ := [-92, -94, -96, -97])
  have hm := merge_two (literal (valuationOf q) (1581)) (literal (valuationOf q) (1588)) (literal (valuationOf q) (1594)) (countLit q [-86, -88, -90]) (countLit q [-92, -94, -96, -97]) (count1591 q) 2 2 (meaning1581 q) (meaning1588 q) (meaning1594 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1433 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1588 = false ∨ valuation q 1594 = true := counterClause1433 (baseVal q)

theorem counterClause1434 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 1598 = true := by
  have hs : count1598 q = (countLit q [-98]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-100])
  have hm := merge_right (literal (valuationOf q) (-100)) (literal (valuationOf q) (1598)) (countLit q [-98]) (countLit q [-100]) (count1598 q) 1 (meaningNeg100 q) (meaning1598 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1434 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 1598 = true := counterClause1434 (baseVal q)

theorem counterClause1435 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1598 = true := by
  have hs : count1598 q = (countLit q [-98]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-100])
  have hm := merge_left (literal (valuationOf q) (-98)) (literal (valuationOf q) (1598)) (countLit q [-98]) (countLit q [-100]) (count1598 q) 1 (meaningNeg98 q) (meaning1598 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1435 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1598 = true := counterClause1435 (baseVal q)

theorem counterClause1436 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 100 = true ∨ valuationOf q 1599 = true := by
  have hs : count1598 q = (countLit q [-98]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-100])
  have hm := merge_two (literal (valuationOf q) (-98)) (literal (valuationOf q) (-100)) (literal (valuationOf q) (1599)) (countLit q [-98]) (countLit q [-100]) (count1598 q) 1 1 (meaningNeg98 q) (meaningNeg100 q) (meaning1599 q) hs
  change (! (valuationOf q 98)) = false ∨ (! (valuationOf q 100)) = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1436 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 100 = true ∨ valuation q 1599 = true := counterClause1436 (baseVal q)

theorem counterClause1437 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 1600 = true := by
  have hs : count1600 q = (countLit q [-103]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-104])
  have hm := merge_right (literal (valuationOf q) (-104)) (literal (valuationOf q) (1600)) (countLit q [-103]) (countLit q [-104]) (count1600 q) 1 (meaningNeg104 q) (meaning1600 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1437 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 1600 = true := counterClause1437 (baseVal q)

theorem counterClause1438 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1600 = true := by
  have hs : count1600 q = (countLit q [-103]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-104])
  have hm := merge_left (literal (valuationOf q) (-103)) (literal (valuationOf q) (1600)) (countLit q [-103]) (countLit q [-104]) (count1600 q) 1 (meaningNeg103 q) (meaning1600 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1438 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1600 = true := counterClause1438 (baseVal q)

theorem counterClause1439 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1602 = true := by
  have hs : count1602 q = (countLit q [-98, -100]) + (countLit q [-103, -104]) := List.countP_append (p := literal q) (l₁ := [-98, -100]) (l₂ := [-103, -104])
  have hm := merge_left (literal (valuationOf q) (1598)) (literal (valuationOf q) (1602)) (countLit q [-98, -100]) (countLit q [-103, -104]) (count1602 q) 1 (meaning1598 q) (meaning1602 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1439 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1602 = true := counterClause1439 (baseVal q)

theorem counterClause1440 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1603 = true := by
  have hs : count1602 q = (countLit q [-98, -100]) + (countLit q [-103, -104]) := List.countP_append (p := literal q) (l₁ := [-98, -100]) (l₂ := [-103, -104])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1603)) (countLit q [-98, -100]) (countLit q [-103, -104]) (count1602 q) 1 1 (meaning1598 q) (meaning1600 q) (meaning1603 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1440 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1600 = false ∨ valuation q 1603 = true := counterClause1440 (baseVal q)

theorem block44 (q : Snake 81) (h : Conditions q) : B112E257.Block44 (valuation q) :=
  ⟨clause1409 q h, clause1410 q h, clause1411 q h, clause1412 q h, clause1413 q h, clause1414 q h, clause1415 q h, clause1416 q h, clause1417 q h, clause1418 q h, clause1419 q h, clause1420 q h, clause1421 q h, clause1422 q h, clause1423 q h, clause1424 q h, clause1425 q h, clause1426 q h, clause1427 q h, clause1428 q h, clause1429 q h, clause1430 q h, clause1431 q h, clause1432 q h, clause1433 q h, clause1434 q h, clause1435 q h, clause1436 q h, clause1437 q h, clause1438 q h, clause1439 q h, clause1440 q h⟩

end
end Snake9.Regrowth.E112257
