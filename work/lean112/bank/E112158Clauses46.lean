import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec46 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1473 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1663 = true := by
  have hs : count1656 q = (countLit q [-89, -92, -93, -95, -98, -100, -102]) + (countLit q [-104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-89, -92, -93, -95, -98, -100, -102]) (l₂ := [-104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1663)) (countLit q [-89, -92, -93, -95, -98, -100, -102]) (countLit q [-104, -107, -109, -110, -111, -114, -117, -118]) (count1656 q) 4 4 (meaning1628 q) (meaning1651 q) (meaning1663 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1473 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1651 = false ∨ valuation q 1663 = true := counterClause1473 (baseVal q)

theorem counterClause1474 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1662 = true := by
  have hs : count1656 q = (countLit q [-89, -92, -93, -95, -98, -100, -102]) + (countLit q [-104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-89, -92, -93, -95, -98, -100, -102]) (l₂ := [-104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1629)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1662)) (countLit q [-89, -92, -93, -95, -98, -100, -102]) (countLit q [-104, -107, -109, -110, -111, -114, -117, -118]) (count1656 q) 5 2 (meaning1629 q) (meaning1649 q) (meaning1662 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1474 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1649 = false ∨ valuation q 1662 = true := counterClause1474 (baseVal q)

theorem counterClause1475 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1677 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1677)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 1 6 (meaning1597 q) (meaning1661 q) (meaning1677 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1475 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1661 = false ∨ valuation q 1677 = true := counterClause1475 (baseVal q)

theorem counterClause1476 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1676 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1676)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 2 4 (meaning1598 q) (meaning1659 q) (meaning1676 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1676 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1476 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1659 = false ∨ valuation q 1676 = true := counterClause1476 (baseVal q)

theorem counterClause1477 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1677 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1677)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 2 5 (meaning1598 q) (meaning1660 q) (meaning1677 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1477 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1660 = false ∨ valuation q 1677 = true := counterClause1477 (baseVal q)

theorem counterClause1478 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1678 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1678)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 2 6 (meaning1598 q) (meaning1661 q) (meaning1678 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1478 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1661 = false ∨ valuation q 1678 = true := counterClause1478 (baseVal q)

theorem counterClause1479 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1679 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1679)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 2 7 (meaning1598 q) (meaning1662 q) (meaning1679 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1479 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1662 = false ∨ valuation q 1679 = true := counterClause1479 (baseVal q)

theorem counterClause1480 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1680 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1680)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 2 8 (meaning1598 q) (meaning1663 q) (meaning1680 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1480 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1663 = false ∨ valuation q 1680 = true := counterClause1480 (baseVal q)

theorem counterClause1481 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1675 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1675)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 3 2 (meaning1599 q) (meaning1657 q) (meaning1675 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1675 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1481 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1657 = false ∨ valuation q 1675 = true := counterClause1481 (baseVal q)

theorem counterClause1482 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1676 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1676)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 3 3 (meaning1599 q) (meaning1658 q) (meaning1676 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1676 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1482 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1658 = false ∨ valuation q 1676 = true := counterClause1482 (baseVal q)

theorem counterClause1483 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1677 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1677)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 3 4 (meaning1599 q) (meaning1659 q) (meaning1677 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1483 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1659 = false ∨ valuation q 1677 = true := counterClause1483 (baseVal q)

theorem counterClause1484 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1678 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1678)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 3 5 (meaning1599 q) (meaning1660 q) (meaning1678 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1484 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1660 = false ∨ valuation q 1678 = true := counterClause1484 (baseVal q)

theorem counterClause1485 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1679 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1679)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 3 6 (meaning1599 q) (meaning1661 q) (meaning1679 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1485 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1661 = false ∨ valuation q 1679 = true := counterClause1485 (baseVal q)

theorem counterClause1486 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1680 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1680)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 3 7 (meaning1599 q) (meaning1662 q) (meaning1680 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1486 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1662 = false ∨ valuation q 1680 = true := counterClause1486 (baseVal q)

theorem counterClause1487 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1676 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1676)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 4 2 (meaning1600 q) (meaning1657 q) (meaning1676 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1676 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1487 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1657 = false ∨ valuation q 1676 = true := counterClause1487 (baseVal q)

theorem counterClause1488 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1677 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1677)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 4 3 (meaning1600 q) (meaning1658 q) (meaning1677 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1488 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1658 = false ∨ valuation q 1677 = true := counterClause1488 (baseVal q)

theorem counterClause1489 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1678 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1678)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 4 4 (meaning1600 q) (meaning1659 q) (meaning1678 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1489 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1659 = false ∨ valuation q 1678 = true := counterClause1489 (baseVal q)

theorem counterClause1490 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1679 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1679)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 4 5 (meaning1600 q) (meaning1660 q) (meaning1679 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1490 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1660 = false ∨ valuation q 1679 = true := counterClause1490 (baseVal q)

theorem counterClause1491 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1680 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1680)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 4 6 (meaning1600 q) (meaning1661 q) (meaning1680 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1491 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1661 = false ∨ valuation q 1680 = true := counterClause1491 (baseVal q)

theorem counterClause1492 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1681 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1681)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 4 7 (meaning1600 q) (meaning1662 q) (meaning1681 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1492 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1662 = false ∨ valuation q 1681 = true := counterClause1492 (baseVal q)

theorem counterClause1493 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1677 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1677)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 5 2 (meaning1601 q) (meaning1657 q) (meaning1677 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1493 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1657 = false ∨ valuation q 1677 = true := counterClause1493 (baseVal q)

theorem counterClause1494 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1678 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1678)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 5 3 (meaning1601 q) (meaning1658 q) (meaning1678 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1494 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1658 = false ∨ valuation q 1678 = true := counterClause1494 (baseVal q)

theorem counterClause1495 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1679 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1679)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 5 4 (meaning1601 q) (meaning1659 q) (meaning1679 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1495 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1659 = false ∨ valuation q 1679 = true := counterClause1495 (baseVal q)

theorem counterClause1496 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1680 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1680)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 5 5 (meaning1601 q) (meaning1660 q) (meaning1680 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1496 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1660 = false ∨ valuation q 1680 = true := counterClause1496 (baseVal q)

theorem counterClause1497 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1681 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1681)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 5 6 (meaning1601 q) (meaning1661 q) (meaning1681 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1497 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1661 = false ∨ valuation q 1681 = true := counterClause1497 (baseVal q)

theorem counterClause1498 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1682 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1682)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 5 7 (meaning1601 q) (meaning1662 q) (meaning1682 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1498 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1662 = false ∨ valuation q 1682 = true := counterClause1498 (baseVal q)

theorem counterClause1499 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1678 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1602)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1678)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 6 2 (meaning1602 q) (meaning1657 q) (meaning1678 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1499 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1657 = false ∨ valuation q 1678 = true := counterClause1499 (baseVal q)

theorem counterClause1500 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1679 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1602)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1679)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 6 3 (meaning1602 q) (meaning1658 q) (meaning1679 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1500 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1658 = false ∨ valuation q 1679 = true := counterClause1500 (baseVal q)

theorem counterClause1501 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1680 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1602)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1680)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 6 4 (meaning1602 q) (meaning1659 q) (meaning1680 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1501 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1659 = false ∨ valuation q 1680 = true := counterClause1501 (baseVal q)

theorem counterClause1502 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1681 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1602)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1681)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 6 5 (meaning1602 q) (meaning1660 q) (meaning1681 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1502 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1660 = false ∨ valuation q 1681 = true := counterClause1502 (baseVal q)

theorem counterClause1503 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1682 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1602)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1682)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 6 6 (meaning1602 q) (meaning1661 q) (meaning1682 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1503 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1661 = false ∨ valuation q 1682 = true := counterClause1503 (baseVal q)

theorem counterClause1504 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1679 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1603)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1679)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 7 2 (meaning1603 q) (meaning1657 q) (meaning1679 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1504 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1657 = false ∨ valuation q 1679 = true := counterClause1504 (baseVal q)

theorem block46 (q : Snake 81) (h : Conditions q) : B112E158.Block46 (valuation q) :=
  ⟨clause1473 q h, clause1474 q h, clause1475 q h, clause1476 q h, clause1477 q h, clause1478 q h, clause1479 q h, clause1480 q h, clause1481 q h, clause1482 q h, clause1483 q h, clause1484 q h, clause1485 q h, clause1486 q h, clause1487 q h, clause1488 q h, clause1489 q h, clause1490 q h, clause1491 q h, clause1492 q h, clause1493 q h, clause1494 q h, clause1495 q h, clause1496 q h, clause1497 q h, clause1498 q h, clause1499 q h, clause1500 q h, clause1501 q h, clause1502 q h, clause1503 q h, clause1504 q h⟩

end
end Snake9.Regrowth.E112158
