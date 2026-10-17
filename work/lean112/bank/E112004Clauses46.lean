import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec46 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1473 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1628 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -64, -67, -70, -71, -73]) + (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73]) (l₂ := [-75, -78, -80, -82, -83, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1628)) (countLit q [-61, -62, -64, -67, -70, -71, -73]) (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) (count1624 q) 2 3 (meaning1594 q) (meaning1618 q) (meaning1628 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1473 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1618 = false ∨ valuation q 1628 = true := counterClause1473 (baseVal q)

theorem counterClause1474 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1629 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -64, -67, -70, -71, -73]) + (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73]) (l₂ := [-75, -78, -80, -82, -83, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1629)) (countLit q [-61, -62, -64, -67, -70, -71, -73]) (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) (count1624 q) 2 4 (meaning1594 q) (meaning1619 q) (meaning1629 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1474 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1619 = false ∨ valuation q 1629 = true := counterClause1474 (baseVal q)

theorem counterClause1475 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1630 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -64, -67, -70, -71, -73]) + (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73]) (l₂ := [-75, -78, -80, -82, -83, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1630)) (countLit q [-61, -62, -64, -67, -70, -71, -73]) (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) (count1624 q) 2 5 (meaning1594 q) (meaning1620 q) (meaning1630 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1475 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1620 = false ∨ valuation q 1630 = true := counterClause1475 (baseVal q)

theorem counterClause1476 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1631 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -64, -67, -70, -71, -73]) + (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73]) (l₂ := [-75, -78, -80, -82, -83, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1621)) (literal (valuationOf q) (1631)) (countLit q [-61, -62, -64, -67, -70, -71, -73]) (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) (count1624 q) 2 6 (meaning1594 q) (meaning1621 q) (meaning1631 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1476 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1621 = false ∨ valuation q 1631 = true := counterClause1476 (baseVal q)

theorem counterClause1477 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1626 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -64, -67, -70, -71, -73]) + (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73]) (l₂ := [-75, -78, -80, -82, -83, -84, -86, -87])
  have hm := merge_left (literal (valuationOf q) (1595)) (literal (valuationOf q) (1626)) (countLit q [-61, -62, -64, -67, -70, -71, -73]) (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) (count1624 q) 3 (meaning1595 q) (meaning1626 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1477 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1626 = true := counterClause1477 (baseVal q)

theorem counterClause1478 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1627 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -64, -67, -70, -71, -73]) + (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73]) (l₂ := [-75, -78, -80, -82, -83, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1627)) (countLit q [-61, -62, -64, -67, -70, -71, -73]) (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) (count1624 q) 3 1 (meaning1595 q) (meaning1616 q) (meaning1627 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1478 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1616 = false ∨ valuation q 1627 = true := counterClause1478 (baseVal q)

theorem counterClause1479 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1628 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -64, -67, -70, -71, -73]) + (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73]) (l₂ := [-75, -78, -80, -82, -83, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1628)) (countLit q [-61, -62, -64, -67, -70, -71, -73]) (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) (count1624 q) 3 2 (meaning1595 q) (meaning1617 q) (meaning1628 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1479 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1617 = false ∨ valuation q 1628 = true := counterClause1479 (baseVal q)

theorem counterClause1480 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1629 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -64, -67, -70, -71, -73]) + (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73]) (l₂ := [-75, -78, -80, -82, -83, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1629)) (countLit q [-61, -62, -64, -67, -70, -71, -73]) (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) (count1624 q) 3 3 (meaning1595 q) (meaning1618 q) (meaning1629 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1480 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1618 = false ∨ valuation q 1629 = true := counterClause1480 (baseVal q)

theorem counterClause1481 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1630 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -64, -67, -70, -71, -73]) + (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73]) (l₂ := [-75, -78, -80, -82, -83, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1630)) (countLit q [-61, -62, -64, -67, -70, -71, -73]) (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) (count1624 q) 3 4 (meaning1595 q) (meaning1619 q) (meaning1630 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1481 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1619 = false ∨ valuation q 1630 = true := counterClause1481 (baseVal q)

theorem counterClause1482 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1631 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -64, -67, -70, -71, -73]) + (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73]) (l₂ := [-75, -78, -80, -82, -83, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1631)) (countLit q [-61, -62, -64, -67, -70, -71, -73]) (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) (count1624 q) 3 5 (meaning1595 q) (meaning1620 q) (meaning1631 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1482 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1620 = false ∨ valuation q 1631 = true := counterClause1482 (baseVal q)

theorem counterClause1483 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1632 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -64, -67, -70, -71, -73]) + (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73]) (l₂ := [-75, -78, -80, -82, -83, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1621)) (literal (valuationOf q) (1632)) (countLit q [-61, -62, -64, -67, -70, -71, -73]) (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) (count1624 q) 3 6 (meaning1595 q) (meaning1621 q) (meaning1632 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1483 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1621 = false ∨ valuation q 1632 = true := counterClause1483 (baseVal q)

theorem counterClause1484 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1627 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -64, -67, -70, -71, -73]) + (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73]) (l₂ := [-75, -78, -80, -82, -83, -84, -86, -87])
  have hm := merge_left (literal (valuationOf q) (1596)) (literal (valuationOf q) (1627)) (countLit q [-61, -62, -64, -67, -70, -71, -73]) (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) (count1624 q) 4 (meaning1596 q) (meaning1627 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1627 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1484 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1627 = true := counterClause1484 (baseVal q)

theorem counterClause1485 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1628 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -64, -67, -70, -71, -73]) + (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73]) (l₂ := [-75, -78, -80, -82, -83, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1628)) (countLit q [-61, -62, -64, -67, -70, -71, -73]) (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) (count1624 q) 4 1 (meaning1596 q) (meaning1616 q) (meaning1628 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1485 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1616 = false ∨ valuation q 1628 = true := counterClause1485 (baseVal q)

theorem counterClause1486 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1629 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -64, -67, -70, -71, -73]) + (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73]) (l₂ := [-75, -78, -80, -82, -83, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1629)) (countLit q [-61, -62, -64, -67, -70, -71, -73]) (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) (count1624 q) 4 2 (meaning1596 q) (meaning1617 q) (meaning1629 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1486 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1617 = false ∨ valuation q 1629 = true := counterClause1486 (baseVal q)

theorem counterClause1487 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1630 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -64, -67, -70, -71, -73]) + (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73]) (l₂ := [-75, -78, -80, -82, -83, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1630)) (countLit q [-61, -62, -64, -67, -70, -71, -73]) (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) (count1624 q) 4 3 (meaning1596 q) (meaning1618 q) (meaning1630 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1487 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1618 = false ∨ valuation q 1630 = true := counterClause1487 (baseVal q)

theorem counterClause1488 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1631 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -64, -67, -70, -71, -73]) + (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73]) (l₂ := [-75, -78, -80, -82, -83, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1631)) (countLit q [-61, -62, -64, -67, -70, -71, -73]) (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) (count1624 q) 4 4 (meaning1596 q) (meaning1619 q) (meaning1631 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1488 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1619 = false ∨ valuation q 1631 = true := counterClause1488 (baseVal q)

theorem counterClause1489 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1632 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -64, -67, -70, -71, -73]) + (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73]) (l₂ := [-75, -78, -80, -82, -83, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1620)) (literal (valuationOf q) (1632)) (countLit q [-61, -62, -64, -67, -70, -71, -73]) (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) (count1624 q) 4 5 (meaning1596 q) (meaning1620 q) (meaning1632 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1620 = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1489 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1620 = false ∨ valuation q 1632 = true := counterClause1489 (baseVal q)

theorem counterClause1490 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1633 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -64, -67, -70, -71, -73]) + (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73]) (l₂ := [-75, -78, -80, -82, -83, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1621)) (literal (valuationOf q) (1633)) (countLit q [-61, -62, -64, -67, -70, -71, -73]) (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) (count1624 q) 4 6 (meaning1596 q) (meaning1621 q) (meaning1633 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1621 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1490 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1621 = false ∨ valuation q 1633 = true := counterClause1490 (baseVal q)

theorem counterClause1491 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1628 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -64, -67, -70, -71, -73]) + (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73]) (l₂ := [-75, -78, -80, -82, -83, -84, -86, -87])
  have hm := merge_left (literal (valuationOf q) (1597)) (literal (valuationOf q) (1628)) (countLit q [-61, -62, -64, -67, -70, -71, -73]) (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) (count1624 q) 5 (meaning1597 q) (meaning1628 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1628 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1491 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1628 = true := counterClause1491 (baseVal q)

theorem counterClause1492 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1629 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -64, -67, -70, -71, -73]) + (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73]) (l₂ := [-75, -78, -80, -82, -83, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1629)) (countLit q [-61, -62, -64, -67, -70, -71, -73]) (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) (count1624 q) 5 1 (meaning1597 q) (meaning1616 q) (meaning1629 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1629 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1492 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1616 = false ∨ valuation q 1629 = true := counterClause1492 (baseVal q)

theorem counterClause1493 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1630 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -64, -67, -70, -71, -73]) + (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73]) (l₂ := [-75, -78, -80, -82, -83, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1630)) (countLit q [-61, -62, -64, -67, -70, -71, -73]) (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) (count1624 q) 5 2 (meaning1597 q) (meaning1617 q) (meaning1630 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1493 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1617 = false ∨ valuation q 1630 = true := counterClause1493 (baseVal q)

theorem counterClause1494 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1631 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -64, -67, -70, -71, -73]) + (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73]) (l₂ := [-75, -78, -80, -82, -83, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1631)) (countLit q [-61, -62, -64, -67, -70, -71, -73]) (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) (count1624 q) 5 3 (meaning1597 q) (meaning1618 q) (meaning1631 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1494 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1618 = false ∨ valuation q 1631 = true := counterClause1494 (baseVal q)

theorem counterClause1495 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1630 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -64, -67, -70, -71, -73]) + (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73]) (l₂ := [-75, -78, -80, -82, -83, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1630)) (countLit q [-61, -62, -64, -67, -70, -71, -73]) (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) (count1624 q) 6 1 (meaning1598 q) (meaning1616 q) (meaning1630 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1630 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1495 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1616 = false ∨ valuation q 1630 = true := counterClause1495 (baseVal q)

theorem counterClause1496 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1631 = true := by
  have hs : count1624 q = (countLit q [-61, -62, -64, -67, -70, -71, -73]) + (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -64, -67, -70, -71, -73]) (l₂ := [-75, -78, -80, -82, -83, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1631)) (countLit q [-61, -62, -64, -67, -70, -71, -73]) (countLit q [-75, -78, -80, -82, -83, -84, -86, -87]) (count1624 q) 6 2 (meaning1598 q) (meaning1617 q) (meaning1631 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1631 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1496 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1617 = false ∨ valuation q 1631 = true := counterClause1496 (baseVal q)

theorem counterClause1497 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1639 = true := by
  have hs : count1639 q = (countLit q [-90]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-91])
  have hm := merge_right (literal (valuationOf q) (-91)) (literal (valuationOf q) (1639)) (countLit q [-90]) (countLit q [-91]) (count1639 q) 1 (meaningNeg91 q) (meaning1639 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1497 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1639 = true := counterClause1497 (baseVal q)

theorem counterClause1498 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1639 = true := by
  have hs : count1639 q = (countLit q [-90]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-91])
  have hm := merge_left (literal (valuationOf q) (-90)) (literal (valuationOf q) (1639)) (countLit q [-90]) (countLit q [-91]) (count1639 q) 1 (meaningNeg90 q) (meaning1639 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1498 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1639 = true := counterClause1498 (baseVal q)

theorem counterClause1499 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 91 = true ∨ valuationOf q 1640 = true := by
  have hs : count1639 q = (countLit q [-90]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-91])
  have hm := merge_two (literal (valuationOf q) (-90)) (literal (valuationOf q) (-91)) (literal (valuationOf q) (1640)) (countLit q [-90]) (countLit q [-91]) (count1639 q) 1 1 (meaningNeg90 q) (meaningNeg91 q) (meaning1640 q) hs
  change (! (valuationOf q 90)) = false ∨ (! (valuationOf q 91)) = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1499 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 91 = true ∨ valuation q 1640 = true := counterClause1499 (baseVal q)

theorem counterClause1500 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1641 = true := by
  have hs : count1641 q = (countLit q [-97]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-98])
  have hm := merge_right (literal (valuationOf q) (-98)) (literal (valuationOf q) (1641)) (countLit q [-97]) (countLit q [-98]) (count1641 q) 1 (meaningNeg98 q) (meaning1641 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1500 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1641 = true := counterClause1500 (baseVal q)

theorem counterClause1501 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1641 = true := by
  have hs : count1641 q = (countLit q [-97]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-98])
  have hm := merge_left (literal (valuationOf q) (-97)) (literal (valuationOf q) (1641)) (countLit q [-97]) (countLit q [-98]) (count1641 q) 1 (meaningNeg97 q) (meaning1641 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1501 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1641 = true := counterClause1501 (baseVal q)

theorem counterClause1502 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 98 = true ∨ valuationOf q 1642 = true := by
  have hs : count1641 q = (countLit q [-97]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-98])
  have hm := merge_two (literal (valuationOf q) (-97)) (literal (valuationOf q) (-98)) (literal (valuationOf q) (1642)) (countLit q [-97]) (countLit q [-98]) (count1641 q) 1 1 (meaningNeg97 q) (meaningNeg98 q) (meaning1642 q) hs
  change (! (valuationOf q 97)) = false ∨ (! (valuationOf q 98)) = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1502 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 98 = true ∨ valuation q 1642 = true := counterClause1502 (baseVal q)

theorem counterClause1503 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1643 = true := by
  have hs : count1643 q = (countLit q [-90, -91]) + (countLit q [-97, -98]) := List.countP_append (p := literal q) (l₁ := [-90, -91]) (l₂ := [-97, -98])
  have hm := merge_right (literal (valuationOf q) (1641)) (literal (valuationOf q) (1643)) (countLit q [-90, -91]) (countLit q [-97, -98]) (count1643 q) 1 (meaning1641 q) (meaning1643 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1503 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1643 = true := counterClause1503 (baseVal q)

theorem counterClause1504 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1644 = true := by
  have hs : count1643 q = (countLit q [-90, -91]) + (countLit q [-97, -98]) := List.countP_append (p := literal q) (l₁ := [-90, -91]) (l₂ := [-97, -98])
  have hm := merge_right (literal (valuationOf q) (1642)) (literal (valuationOf q) (1644)) (countLit q [-90, -91]) (countLit q [-97, -98]) (count1643 q) 2 (meaning1642 q) (meaning1644 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1504 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1644 = true := counterClause1504 (baseVal q)

theorem block46 (q : Snake 81) (h : Conditions q) : B112E004.Block46 (valuation q) :=
  ⟨clause1473 q h, clause1474 q h, clause1475 q h, clause1476 q h, clause1477 q h, clause1478 q h, clause1479 q h, clause1480 q h, clause1481 q h, clause1482 q h, clause1483 q h, clause1484 q h, clause1485 q h, clause1486 q h, clause1487 q h, clause1488 q h, clause1489 q h, clause1490 q h, clause1491 q h, clause1492 q h, clause1493 q h, clause1494 q h, clause1495 q h, clause1496 q h, clause1497 q h, clause1498 q h, clause1499 q h, clause1500 q h, clause1501 q h, clause1502 q h, clause1503 q h, clause1504 q h⟩

end
end Snake9.Regrowth.E112004
