import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec42 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1345 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1593 = true := by
  have hs : count1589 q = (countLit q [-74, -77, -78, -80]) + (countLit q [-82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-74, -77, -78, -80]) (l₂ := [-82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1579)) (literal (valuationOf q) (1586)) (literal (valuationOf q) (1593)) (countLit q [-74, -77, -78, -80]) (countLit q [-82, -84, -86, -87]) (count1589 q) 3 2 (meaning1579 q) (meaning1586 q) (meaning1593 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1345 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1586 = false ∨ valuation q 1593 = true := counterClause1345 (baseVal q)

theorem counterClause1346 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1594 = true := by
  have hs : count1589 q = (countLit q [-74, -77, -78, -80]) + (countLit q [-82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-74, -77, -78, -80]) (l₂ := [-82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1579)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1594)) (countLit q [-74, -77, -78, -80]) (countLit q [-82, -84, -86, -87]) (count1589 q) 3 3 (meaning1579 q) (meaning1587 q) (meaning1594 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1346 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1587 = false ∨ valuation q 1594 = true := counterClause1346 (baseVal q)

theorem counterClause1347 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1597 = true := by
  have hs : count1597 q = (countLit q [-59, -61, -63, -65, -68, -71, -73]) + (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73]) (l₂ := [-74, -77, -78, -80, -82, -84, -86, -87])
  have hm := merge_left (literal (valuationOf q) (1566)) (literal (valuationOf q) (1597)) (countLit q [-59, -61, -63, -65, -68, -71, -73]) (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) (count1597 q) 1 (meaning1566 q) (meaning1597 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1347 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1597 = true := counterClause1347 (baseVal q)

theorem counterClause1348 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1598 = true := by
  have hs : count1597 q = (countLit q [-59, -61, -63, -65, -68, -71, -73]) + (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73]) (l₂ := [-74, -77, -78, -80, -82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1598)) (countLit q [-59, -61, -63, -65, -68, -71, -73]) (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) (count1597 q) 1 1 (meaning1566 q) (meaning1589 q) (meaning1598 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1348 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1589 = false ∨ valuation q 1598 = true := counterClause1348 (baseVal q)

theorem counterClause1349 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1599 = true := by
  have hs : count1597 q = (countLit q [-59, -61, -63, -65, -68, -71, -73]) + (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73]) (l₂ := [-74, -77, -78, -80, -82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1599)) (countLit q [-59, -61, -63, -65, -68, -71, -73]) (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) (count1597 q) 1 2 (meaning1566 q) (meaning1590 q) (meaning1599 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1349 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1590 = false ∨ valuation q 1599 = true := counterClause1349 (baseVal q)

theorem counterClause1350 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1600 = true := by
  have hs : count1597 q = (countLit q [-59, -61, -63, -65, -68, -71, -73]) + (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73]) (l₂ := [-74, -77, -78, -80, -82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1600)) (countLit q [-59, -61, -63, -65, -68, -71, -73]) (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) (count1597 q) 1 3 (meaning1566 q) (meaning1591 q) (meaning1600 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1350 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1591 = false ∨ valuation q 1600 = true := counterClause1350 (baseVal q)

theorem counterClause1351 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1601 = true := by
  have hs : count1597 q = (countLit q [-59, -61, -63, -65, -68, -71, -73]) + (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73]) (l₂ := [-74, -77, -78, -80, -82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1601)) (countLit q [-59, -61, -63, -65, -68, -71, -73]) (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) (count1597 q) 1 4 (meaning1566 q) (meaning1592 q) (meaning1601 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1351 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1592 = false ∨ valuation q 1601 = true := counterClause1351 (baseVal q)

theorem counterClause1352 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1602 = true := by
  have hs : count1597 q = (countLit q [-59, -61, -63, -65, -68, -71, -73]) + (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73]) (l₂ := [-74, -77, -78, -80, -82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1593)) (literal (valuationOf q) (1602)) (countLit q [-59, -61, -63, -65, -68, -71, -73]) (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) (count1597 q) 1 5 (meaning1566 q) (meaning1593 q) (meaning1602 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1352 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1593 = false ∨ valuation q 1602 = true := counterClause1352 (baseVal q)

theorem counterClause1353 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1599 = true := by
  have hs : count1597 q = (countLit q [-59, -61, -63, -65, -68, -71, -73]) + (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73]) (l₂ := [-74, -77, -78, -80, -82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1599)) (countLit q [-59, -61, -63, -65, -68, -71, -73]) (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) (count1597 q) 2 1 (meaning1567 q) (meaning1589 q) (meaning1599 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1353 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1589 = false ∨ valuation q 1599 = true := counterClause1353 (baseVal q)

theorem counterClause1354 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1600 = true := by
  have hs : count1597 q = (countLit q [-59, -61, -63, -65, -68, -71, -73]) + (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73]) (l₂ := [-74, -77, -78, -80, -82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1600)) (countLit q [-59, -61, -63, -65, -68, -71, -73]) (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) (count1597 q) 2 2 (meaning1567 q) (meaning1590 q) (meaning1600 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1354 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1590 = false ∨ valuation q 1600 = true := counterClause1354 (baseVal q)

theorem counterClause1355 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1601 = true := by
  have hs : count1597 q = (countLit q [-59, -61, -63, -65, -68, -71, -73]) + (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73]) (l₂ := [-74, -77, -78, -80, -82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1601)) (countLit q [-59, -61, -63, -65, -68, -71, -73]) (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) (count1597 q) 2 3 (meaning1567 q) (meaning1591 q) (meaning1601 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1355 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1591 = false ∨ valuation q 1601 = true := counterClause1355 (baseVal q)

theorem counterClause1356 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1602 = true := by
  have hs : count1597 q = (countLit q [-59, -61, -63, -65, -68, -71, -73]) + (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73]) (l₂ := [-74, -77, -78, -80, -82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1602)) (countLit q [-59, -61, -63, -65, -68, -71, -73]) (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) (count1597 q) 2 4 (meaning1567 q) (meaning1592 q) (meaning1602 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1356 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1592 = false ∨ valuation q 1602 = true := counterClause1356 (baseVal q)

theorem counterClause1357 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1603 = true := by
  have hs : count1597 q = (countLit q [-59, -61, -63, -65, -68, -71, -73]) + (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73]) (l₂ := [-74, -77, -78, -80, -82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1593)) (literal (valuationOf q) (1603)) (countLit q [-59, -61, -63, -65, -68, -71, -73]) (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) (count1597 q) 2 5 (meaning1567 q) (meaning1593 q) (meaning1603 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1357 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1593 = false ∨ valuation q 1603 = true := counterClause1357 (baseVal q)

theorem counterClause1358 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1604 = true := by
  have hs : count1597 q = (countLit q [-59, -61, -63, -65, -68, -71, -73]) + (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73]) (l₂ := [-74, -77, -78, -80, -82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1594)) (literal (valuationOf q) (1604)) (countLit q [-59, -61, -63, -65, -68, -71, -73]) (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) (count1597 q) 2 6 (meaning1567 q) (meaning1594 q) (meaning1604 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1358 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1594 = false ∨ valuation q 1604 = true := counterClause1358 (baseVal q)

theorem counterClause1359 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1599 = true := by
  have hs : count1597 q = (countLit q [-59, -61, -63, -65, -68, -71, -73]) + (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73]) (l₂ := [-74, -77, -78, -80, -82, -84, -86, -87])
  have hm := merge_left (literal (valuationOf q) (1568)) (literal (valuationOf q) (1599)) (countLit q [-59, -61, -63, -65, -68, -71, -73]) (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) (count1597 q) 3 (meaning1568 q) (meaning1599 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1359 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1599 = true := counterClause1359 (baseVal q)

theorem counterClause1360 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1600 = true := by
  have hs : count1597 q = (countLit q [-59, -61, -63, -65, -68, -71, -73]) + (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73]) (l₂ := [-74, -77, -78, -80, -82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1600)) (countLit q [-59, -61, -63, -65, -68, -71, -73]) (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) (count1597 q) 3 1 (meaning1568 q) (meaning1589 q) (meaning1600 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1360 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1589 = false ∨ valuation q 1600 = true := counterClause1360 (baseVal q)

theorem counterClause1361 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1601 = true := by
  have hs : count1597 q = (countLit q [-59, -61, -63, -65, -68, -71, -73]) + (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73]) (l₂ := [-74, -77, -78, -80, -82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1601)) (countLit q [-59, -61, -63, -65, -68, -71, -73]) (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) (count1597 q) 3 2 (meaning1568 q) (meaning1590 q) (meaning1601 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1361 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1590 = false ∨ valuation q 1601 = true := counterClause1361 (baseVal q)

theorem counterClause1362 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1602 = true := by
  have hs : count1597 q = (countLit q [-59, -61, -63, -65, -68, -71, -73]) + (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73]) (l₂ := [-74, -77, -78, -80, -82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1602)) (countLit q [-59, -61, -63, -65, -68, -71, -73]) (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) (count1597 q) 3 3 (meaning1568 q) (meaning1591 q) (meaning1602 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1362 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1591 = false ∨ valuation q 1602 = true := counterClause1362 (baseVal q)

theorem counterClause1363 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1603 = true := by
  have hs : count1597 q = (countLit q [-59, -61, -63, -65, -68, -71, -73]) + (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73]) (l₂ := [-74, -77, -78, -80, -82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1603)) (countLit q [-59, -61, -63, -65, -68, -71, -73]) (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) (count1597 q) 3 4 (meaning1568 q) (meaning1592 q) (meaning1603 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1363 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1592 = false ∨ valuation q 1603 = true := counterClause1363 (baseVal q)

theorem counterClause1364 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1604 = true := by
  have hs : count1597 q = (countLit q [-59, -61, -63, -65, -68, -71, -73]) + (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73]) (l₂ := [-74, -77, -78, -80, -82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1593)) (literal (valuationOf q) (1604)) (countLit q [-59, -61, -63, -65, -68, -71, -73]) (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) (count1597 q) 3 5 (meaning1568 q) (meaning1593 q) (meaning1604 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1364 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1593 = false ∨ valuation q 1604 = true := counterClause1364 (baseVal q)

theorem counterClause1365 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1600 = true := by
  have hs : count1597 q = (countLit q [-59, -61, -63, -65, -68, -71, -73]) + (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73]) (l₂ := [-74, -77, -78, -80, -82, -84, -86, -87])
  have hm := merge_left (literal (valuationOf q) (1569)) (literal (valuationOf q) (1600)) (countLit q [-59, -61, -63, -65, -68, -71, -73]) (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) (count1597 q) 4 (meaning1569 q) (meaning1600 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1365 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1600 = true := counterClause1365 (baseVal q)

theorem counterClause1366 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1601 = true := by
  have hs : count1597 q = (countLit q [-59, -61, -63, -65, -68, -71, -73]) + (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73]) (l₂ := [-74, -77, -78, -80, -82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1601)) (countLit q [-59, -61, -63, -65, -68, -71, -73]) (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) (count1597 q) 4 1 (meaning1569 q) (meaning1589 q) (meaning1601 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1366 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1589 = false ∨ valuation q 1601 = true := counterClause1366 (baseVal q)

theorem counterClause1367 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1602 = true := by
  have hs : count1597 q = (countLit q [-59, -61, -63, -65, -68, -71, -73]) + (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73]) (l₂ := [-74, -77, -78, -80, -82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1602)) (countLit q [-59, -61, -63, -65, -68, -71, -73]) (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) (count1597 q) 4 2 (meaning1569 q) (meaning1590 q) (meaning1602 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1367 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1590 = false ∨ valuation q 1602 = true := counterClause1367 (baseVal q)

theorem counterClause1368 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1603 = true := by
  have hs : count1597 q = (countLit q [-59, -61, -63, -65, -68, -71, -73]) + (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73]) (l₂ := [-74, -77, -78, -80, -82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1603)) (countLit q [-59, -61, -63, -65, -68, -71, -73]) (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) (count1597 q) 4 3 (meaning1569 q) (meaning1591 q) (meaning1603 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1368 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1591 = false ∨ valuation q 1603 = true := counterClause1368 (baseVal q)

theorem counterClause1369 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1604 = true := by
  have hs : count1597 q = (countLit q [-59, -61, -63, -65, -68, -71, -73]) + (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73]) (l₂ := [-74, -77, -78, -80, -82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1604)) (countLit q [-59, -61, -63, -65, -68, -71, -73]) (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) (count1597 q) 4 4 (meaning1569 q) (meaning1592 q) (meaning1604 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1369 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1592 = false ∨ valuation q 1604 = true := counterClause1369 (baseVal q)

theorem counterClause1370 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1605 = true := by
  have hs : count1597 q = (countLit q [-59, -61, -63, -65, -68, -71, -73]) + (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73]) (l₂ := [-74, -77, -78, -80, -82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1593)) (literal (valuationOf q) (1605)) (countLit q [-59, -61, -63, -65, -68, -71, -73]) (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) (count1597 q) 4 5 (meaning1569 q) (meaning1593 q) (meaning1605 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1370 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1593 = false ∨ valuation q 1605 = true := counterClause1370 (baseVal q)

theorem counterClause1371 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1601 = true := by
  have hs : count1597 q = (countLit q [-59, -61, -63, -65, -68, -71, -73]) + (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73]) (l₂ := [-74, -77, -78, -80, -82, -84, -86, -87])
  have hm := merge_left (literal (valuationOf q) (1570)) (literal (valuationOf q) (1601)) (countLit q [-59, -61, -63, -65, -68, -71, -73]) (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) (count1597 q) 5 (meaning1570 q) (meaning1601 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1371 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1601 = true := counterClause1371 (baseVal q)

theorem counterClause1372 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1602 = true := by
  have hs : count1597 q = (countLit q [-59, -61, -63, -65, -68, -71, -73]) + (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73]) (l₂ := [-74, -77, -78, -80, -82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1602)) (countLit q [-59, -61, -63, -65, -68, -71, -73]) (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) (count1597 q) 5 1 (meaning1570 q) (meaning1589 q) (meaning1602 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1372 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1589 = false ∨ valuation q 1602 = true := counterClause1372 (baseVal q)

theorem counterClause1373 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1603 = true := by
  have hs : count1597 q = (countLit q [-59, -61, -63, -65, -68, -71, -73]) + (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73]) (l₂ := [-74, -77, -78, -80, -82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1603)) (countLit q [-59, -61, -63, -65, -68, -71, -73]) (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) (count1597 q) 5 2 (meaning1570 q) (meaning1590 q) (meaning1603 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1373 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1590 = false ∨ valuation q 1603 = true := counterClause1373 (baseVal q)

theorem counterClause1374 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1604 = true := by
  have hs : count1597 q = (countLit q [-59, -61, -63, -65, -68, -71, -73]) + (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73]) (l₂ := [-74, -77, -78, -80, -82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1604)) (countLit q [-59, -61, -63, -65, -68, -71, -73]) (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) (count1597 q) 5 3 (meaning1570 q) (meaning1591 q) (meaning1604 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1374 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1591 = false ∨ valuation q 1604 = true := counterClause1374 (baseVal q)

theorem counterClause1375 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1605 = true := by
  have hs : count1597 q = (countLit q [-59, -61, -63, -65, -68, -71, -73]) + (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73]) (l₂ := [-74, -77, -78, -80, -82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1605)) (countLit q [-59, -61, -63, -65, -68, -71, -73]) (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) (count1597 q) 5 4 (meaning1570 q) (meaning1592 q) (meaning1605 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1375 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1592 = false ∨ valuation q 1605 = true := counterClause1375 (baseVal q)

theorem counterClause1376 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1606 = true := by
  have hs : count1597 q = (countLit q [-59, -61, -63, -65, -68, -71, -73]) + (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73]) (l₂ := [-74, -77, -78, -80, -82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1593)) (literal (valuationOf q) (1606)) (countLit q [-59, -61, -63, -65, -68, -71, -73]) (countLit q [-74, -77, -78, -80, -82, -84, -86, -87]) (count1597 q) 5 5 (meaning1570 q) (meaning1593 q) (meaning1606 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1376 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1593 = false ∨ valuation q 1606 = true := counterClause1376 (baseVal q)

theorem block42 (q : Snake 81) (h : Conditions q) : B112E158.Block42 (valuation q) :=
  ⟨clause1345 q h, clause1346 q h, clause1347 q h, clause1348 q h, clause1349 q h, clause1350 q h, clause1351 q h, clause1352 q h, clause1353 q h, clause1354 q h, clause1355 q h, clause1356 q h, clause1357 q h, clause1358 q h, clause1359 q h, clause1360 q h, clause1361 q h, clause1362 q h, clause1363 q h, clause1364 q h, clause1365 q h, clause1366 q h, clause1367 q h, clause1368 q h, clause1369 q h, clause1370 q h, clause1371 q h, clause1372 q h, clause1373 q h, clause1374 q h, clause1375 q h, clause1376 q h⟩

end
end Snake9.Regrowth.E112158
