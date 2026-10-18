import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec47 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1505 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1680 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1603)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1680)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 7 3 (meaning1603 q) (meaning1658 q) (meaning1680 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1505 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1658 = false ∨ valuation q 1680 = true := counterClause1505 (baseVal q)

theorem counterClause1506 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1681 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1603)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1681)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 7 4 (meaning1603 q) (meaning1659 q) (meaning1681 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1506 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1659 = false ∨ valuation q 1681 = true := counterClause1506 (baseVal q)

theorem counterClause1507 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1682 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1603)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1682)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 7 5 (meaning1603 q) (meaning1660 q) (meaning1682 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1507 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1660 = false ∨ valuation q 1682 = true := counterClause1507 (baseVal q)

theorem counterClause1508 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1683 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1603)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1683)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 7 6 (meaning1603 q) (meaning1661 q) (meaning1683 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1508 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1661 = false ∨ valuation q 1683 = true := counterClause1508 (baseVal q)

theorem counterClause1509 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1680 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1680)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 8 2 (meaning1604 q) (meaning1657 q) (meaning1680 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1509 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1657 = false ∨ valuation q 1680 = true := counterClause1509 (baseVal q)

theorem counterClause1510 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1681 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1681)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 8 3 (meaning1604 q) (meaning1658 q) (meaning1681 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1510 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1658 = false ∨ valuation q 1681 = true := counterClause1510 (baseVal q)

theorem counterClause1511 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1682 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1682)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 8 4 (meaning1604 q) (meaning1659 q) (meaning1682 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1511 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1659 = false ∨ valuation q 1682 = true := counterClause1511 (baseVal q)

theorem counterClause1512 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1683 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1683)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 8 5 (meaning1604 q) (meaning1660 q) (meaning1683 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1512 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1660 = false ∨ valuation q 1683 = true := counterClause1512 (baseVal q)

theorem counterClause1513 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1681 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1681)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 9 2 (meaning1605 q) (meaning1657 q) (meaning1681 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1513 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1657 = false ∨ valuation q 1681 = true := counterClause1513 (baseVal q)

theorem counterClause1514 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1682 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1682)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 9 3 (meaning1605 q) (meaning1658 q) (meaning1682 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1514 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1658 = false ∨ valuation q 1682 = true := counterClause1514 (baseVal q)

theorem counterClause1515 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1683 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1683)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 9 4 (meaning1605 q) (meaning1659 q) (meaning1683 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1515 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1659 = false ∨ valuation q 1683 = true := counterClause1515 (baseVal q)

theorem counterClause1516 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1682 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1682)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 10 2 (meaning1606 q) (meaning1657 q) (meaning1682 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1516 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1657 = false ∨ valuation q 1682 = true := counterClause1516 (baseVal q)

theorem counterClause1517 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1683 = true := by
  have hs : count1671 q = (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) + (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (l₂ := [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1683)) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87]) (countLit q [-89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1671 q) 10 3 (meaning1606 q) (meaning1658 q) (meaning1683 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1517 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1658 = false ∨ valuation q 1683 = true := counterClause1517 (baseVal q)

theorem counterClause1518 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1708 = true := by
  have hs : count1690 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30, -32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) + (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87, -89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30, -32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (l₂ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87, -89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1539)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1708)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30, -32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87, -89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1690 q) 6 13 (meaning1539 q) (meaning1683 q) (meaning1708 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1518 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1683 = false ∨ valuation q 1708 = true := counterClause1518 (baseVal q)

theorem counterClause1519 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1708 = true := by
  have hs : count1690 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30, -32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) + (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87, -89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30, -32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (l₂ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87, -89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1540)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1708)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30, -32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87, -89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1690 q) 7 12 (meaning1540 q) (meaning1682 q) (meaning1708 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1519 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1682 = false ∨ valuation q 1708 = true := counterClause1519 (baseVal q)

theorem counterClause1520 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1708 = true := by
  have hs : count1690 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30, -32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) + (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87, -89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30, -32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (l₂ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87, -89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1708)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30, -32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87, -89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1690 q) 8 11 (meaning1541 q) (meaning1681 q) (meaning1708 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1520 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1681 = false ∨ valuation q 1708 = true := counterClause1520 (baseVal q)

theorem counterClause1521 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1708 = true := by
  have hs : count1690 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30, -32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) + (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87, -89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30, -32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (l₂ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87, -89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1708)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30, -32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87, -89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1690 q) 9 10 (meaning1542 q) (meaning1680 q) (meaning1708 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1521 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1680 = false ∨ valuation q 1708 = true := counterClause1521 (baseVal q)

theorem counterClause1522 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1708 = true := by
  have hs : count1690 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30, -32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) + (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87, -89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30, -32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (l₂ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87, -89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1679)) (literal (valuationOf q) (1708)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30, -32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87, -89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1690 q) 10 9 (meaning1543 q) (meaning1679 q) (meaning1708 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1522 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1679 = false ∨ valuation q 1708 = true := counterClause1522 (baseVal q)

theorem counterClause1523 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1678 = false ∨ valuationOf q 1708 = true := by
  have hs : count1690 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30, -32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) + (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87, -89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30, -32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (l₂ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87, -89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1544)) (literal (valuationOf q) (1678)) (literal (valuationOf q) (1708)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30, -32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87, -89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1690 q) 11 8 (meaning1544 q) (meaning1678 q) (meaning1708 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1678 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1523 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1678 = false ∨ valuation q 1708 = true := counterClause1523 (baseVal q)

theorem counterClause1524 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1677 = false ∨ valuationOf q 1708 = true := by
  have hs : count1690 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30, -32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) + (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87, -89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30, -32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (l₂ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87, -89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1677)) (literal (valuationOf q) (1708)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30, -32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87, -89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1690 q) 12 7 (meaning1545 q) (meaning1677 q) (meaning1708 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1677 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1524 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1677 = false ∨ valuation q 1708 = true := counterClause1524 (baseVal q)

theorem counterClause1525 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1676 = false ∨ valuationOf q 1708 = true := by
  have hs : count1690 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30, -32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) + (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87, -89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30, -32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (l₂ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87, -89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1546)) (literal (valuationOf q) (1676)) (literal (valuationOf q) (1708)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30, -32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87, -89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1690 q) 13 6 (meaning1546 q) (meaning1676 q) (meaning1708 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1676 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1525 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1676 = false ∨ valuation q 1708 = true := counterClause1525 (baseVal q)

theorem counterClause1526 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1675 = false ∨ valuationOf q 1708 = true := by
  have hs : count1690 q = (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30, -32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) + (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87, -89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30, -32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (l₂ := [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87, -89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118])
  have hm := merge_two (literal (valuationOf q) (1547)) (literal (valuationOf q) (1675)) (literal (valuationOf q) (1708)) (countLit q [-3, -6, -7, -9, -11, -13, -17, -19, -20, -21, -24, -25, -28, -30, -32, -34, -35, -39, -41, -42, -44, -45, -48, -50, -51, -53, -54, -55, -58]) (countLit q [-59, -61, -63, -65, -68, -71, -73, -74, -77, -78, -80, -82, -84, -86, -87, -89, -92, -93, -95, -98, -100, -102, -104, -107, -109, -110, -111, -114, -117, -118]) (count1690 q) 14 5 (meaning1547 q) (meaning1675 q) (meaning1708 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1675 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1526 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1675 = false ∨ valuation q 1708 = true := counterClause1526 (baseVal q)

theorem clause1527 (q : Snake 81) (h : Conditions q) : valuation q 1708 = false := by
  rw [value1708]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1690 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1528 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 4 = false ∨ valuation q 37 = false ∨ valuation q 39 = false := by
  rw [value3, value4, value37, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (13 : Vertex) (15 : Vertex) (141 : Vertex) (143 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1529 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 19 = false ∨ valuation q 39 = false ∨ valuation q 60 = false := by
  rw [value4, value19, value39, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (15 : Vertex) (79 : Vertex) (143 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1530 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 50 = false ∨ valuation q 52 = false := by
  rw [value12, value13, value50, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (65 : Vertex) (67 : Vertex) (193 : Vertex) (195 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1531 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 15 = false ∨ valuation q 52 = false ∨ valuation q 54 = false := by
  rw [value13, value15, value52, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (67 : Vertex) (71 : Vertex) (195 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1532 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 21 = false ∨ valuation q 53 = false ∨ valuation q 64 = false := by
  rw [value14, value21, value53, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (68 : Vertex) (84 : Vertex) (196 : Vertex) (212 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1533 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 19 = false ∨ valuation q 54 = false ∨ valuation q 60 = false := by
  rw [value15, value19, value54, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (71 : Vertex) (79 : Vertex) (199 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1534 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 25 = false ∨ valuation q 26 = false := by
  rw [value16, value17, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (72 : Vertex) (73 : Vertex) (88 : Vertex) (89 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1535 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 19 = false ∨ valuation q 59 = false ∨ valuation q 60 = false := by
  rw [value18, value19, value59, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (78 : Vertex) (79 : Vertex) (206 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1536 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 64 = false ∨ valuation q 65 = false := by
  rw [value21, value22, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (84 : Vertex) (85 : Vertex) (212 : Vertex) (213 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block47 (q : Snake 81) (h : Conditions q) : B112E158.Block47 (valuation q) :=
  ⟨clause1505 q h, clause1506 q h, clause1507 q h, clause1508 q h, clause1509 q h, clause1510 q h, clause1511 q h, clause1512 q h, clause1513 q h, clause1514 q h, clause1515 q h, clause1516 q h, clause1517 q h, clause1518 q h, clause1519 q h, clause1520 q h, clause1521 q h, clause1522 q h, clause1523 q h, clause1524 q h, clause1525 q h, clause1526 q h, clause1527 q h, clause1528 q h, clause1529 q h, clause1530 q h, clause1531 q h, clause1532 q h, clause1533 q h, clause1534 q h, clause1535 q h, clause1536 q h⟩

end
end Snake9.Regrowth.E112158
