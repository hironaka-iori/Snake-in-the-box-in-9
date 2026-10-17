import E112027Semantics
import B112E027Inputs
namespace Snake9.Regrowth.E112027
noncomputable section
local instance blockDec43 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1377 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1682 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1682)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 4 4 (meaning1605 q) (meaning1663 q) (meaning1682 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1377 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1663 = false ∨ valuation q 1682 = true := counterClause1377 (baseVal q)

theorem counterClause1378 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1683 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1683)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 4 5 (meaning1605 q) (meaning1664 q) (meaning1683 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1378 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1664 = false ∨ valuation q 1683 = true := counterClause1378 (baseVal q)

theorem counterClause1379 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1684 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1684)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 4 6 (meaning1605 q) (meaning1665 q) (meaning1684 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1379 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1665 = false ∨ valuation q 1684 = true := counterClause1379 (baseVal q)

theorem counterClause1380 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1685 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1685)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 4 7 (meaning1605 q) (meaning1666 q) (meaning1685 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1380 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1666 = false ∨ valuation q 1685 = true := counterClause1380 (baseVal q)

theorem counterClause1381 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1681 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1681)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 5 2 (meaning1606 q) (meaning1661 q) (meaning1681 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1381 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1661 = false ∨ valuation q 1681 = true := counterClause1381 (baseVal q)

theorem counterClause1382 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1682 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1682)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 5 3 (meaning1606 q) (meaning1662 q) (meaning1682 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1382 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1662 = false ∨ valuation q 1682 = true := counterClause1382 (baseVal q)

theorem counterClause1383 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1683 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1683)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 5 4 (meaning1606 q) (meaning1663 q) (meaning1683 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1383 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1663 = false ∨ valuation q 1683 = true := counterClause1383 (baseVal q)

theorem counterClause1384 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1684 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1684)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 5 5 (meaning1606 q) (meaning1664 q) (meaning1684 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1384 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1664 = false ∨ valuation q 1684 = true := counterClause1384 (baseVal q)

theorem counterClause1385 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1685 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1685)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 5 6 (meaning1606 q) (meaning1665 q) (meaning1685 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1385 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1665 = false ∨ valuation q 1685 = true := counterClause1385 (baseVal q)

theorem counterClause1386 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1686 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1606)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1686)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 5 7 (meaning1606 q) (meaning1666 q) (meaning1686 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1386 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1666 = false ∨ valuation q 1686 = true := counterClause1386 (baseVal q)

theorem counterClause1387 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1682 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1607)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1682)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 6 2 (meaning1607 q) (meaning1661 q) (meaning1682 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1387 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1661 = false ∨ valuation q 1682 = true := counterClause1387 (baseVal q)

theorem counterClause1388 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1683 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1607)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1683)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 6 3 (meaning1607 q) (meaning1662 q) (meaning1683 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1388 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1662 = false ∨ valuation q 1683 = true := counterClause1388 (baseVal q)

theorem counterClause1389 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1684 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1607)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1684)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 6 4 (meaning1607 q) (meaning1663 q) (meaning1684 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1389 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1663 = false ∨ valuation q 1684 = true := counterClause1389 (baseVal q)

theorem counterClause1390 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1685 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1607)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1685)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 6 5 (meaning1607 q) (meaning1664 q) (meaning1685 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1390 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1664 = false ∨ valuation q 1685 = true := counterClause1390 (baseVal q)

theorem counterClause1391 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1686 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1607)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1686)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 6 6 (meaning1607 q) (meaning1665 q) (meaning1686 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1391 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1665 = false ∨ valuation q 1686 = true := counterClause1391 (baseVal q)

theorem counterClause1392 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1687 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1607)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1687)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 6 7 (meaning1607 q) (meaning1666 q) (meaning1687 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1392 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1666 = false ∨ valuation q 1687 = true := counterClause1392 (baseVal q)

theorem counterClause1393 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1682 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1682)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 7 1 (meaning1608 q) (meaning1660 q) (meaning1682 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1393 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1660 = false ∨ valuation q 1682 = true := counterClause1393 (baseVal q)

theorem counterClause1394 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1683 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1683)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 7 2 (meaning1608 q) (meaning1661 q) (meaning1683 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1394 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1661 = false ∨ valuation q 1683 = true := counterClause1394 (baseVal q)

theorem counterClause1395 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1684 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1684)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 7 3 (meaning1608 q) (meaning1662 q) (meaning1684 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1395 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1662 = false ∨ valuation q 1684 = true := counterClause1395 (baseVal q)

theorem counterClause1396 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1685 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1685)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 7 4 (meaning1608 q) (meaning1663 q) (meaning1685 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1396 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1663 = false ∨ valuation q 1685 = true := counterClause1396 (baseVal q)

theorem counterClause1397 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1686 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1686)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 7 5 (meaning1608 q) (meaning1664 q) (meaning1686 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1397 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1664 = false ∨ valuation q 1686 = true := counterClause1397 (baseVal q)

theorem counterClause1398 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1687 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1608)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1687)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 7 6 (meaning1608 q) (meaning1665 q) (meaning1687 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1398 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1665 = false ∨ valuation q 1687 = true := counterClause1398 (baseVal q)

theorem counterClause1399 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1684 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1684)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 8 2 (meaning1609 q) (meaning1661 q) (meaning1684 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1399 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1661 = false ∨ valuation q 1684 = true := counterClause1399 (baseVal q)

theorem counterClause1400 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1685 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1685)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 8 3 (meaning1609 q) (meaning1662 q) (meaning1685 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1400 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1662 = false ∨ valuation q 1685 = true := counterClause1400 (baseVal q)

theorem counterClause1401 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1686 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1686)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 8 4 (meaning1609 q) (meaning1663 q) (meaning1686 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1401 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1663 = false ∨ valuation q 1686 = true := counterClause1401 (baseVal q)

theorem counterClause1402 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1708 = true := by
  have hs : count1692 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29, -32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) + (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89, -90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29, -32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (l₂ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89, -90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1687)) (literal (valuationOf q) (1708)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29, -32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89, -90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1692 q) 4 13 (meaning1548 q) (meaning1687 q) (meaning1708 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1402 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1687 = false ∨ valuation q 1708 = true := counterClause1402 (baseVal q)

theorem counterClause1403 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1708 = true := by
  have hs : count1692 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29, -32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) + (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89, -90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29, -32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (l₂ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89, -90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1549)) (literal (valuationOf q) (1686)) (literal (valuationOf q) (1708)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29, -32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89, -90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1692 q) 5 12 (meaning1549 q) (meaning1686 q) (meaning1708 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1403 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1686 = false ∨ valuation q 1708 = true := counterClause1403 (baseVal q)

theorem counterClause1404 (q : Nat → Bool) : valuationOf q 1550 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1708 = true := by
  have hs : count1692 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29, -32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) + (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89, -90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29, -32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (l₂ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89, -90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1550)) (literal (valuationOf q) (1685)) (literal (valuationOf q) (1708)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29, -32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89, -90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1692 q) 6 11 (meaning1550 q) (meaning1685 q) (meaning1708 q) hs
  change valuationOf q 1550 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1404 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1685 = false ∨ valuation q 1708 = true := counterClause1404 (baseVal q)

theorem counterClause1405 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1708 = true := by
  have hs : count1692 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29, -32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) + (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89, -90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29, -32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (l₂ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89, -90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1551)) (literal (valuationOf q) (1684)) (literal (valuationOf q) (1708)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29, -32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89, -90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1692 q) 7 10 (meaning1551 q) (meaning1684 q) (meaning1708 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1405 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1684 = false ∨ valuation q 1708 = true := counterClause1405 (baseVal q)

theorem counterClause1406 (q : Nat → Bool) : valuationOf q 1552 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1708 = true := by
  have hs : count1692 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29, -32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) + (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89, -90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29, -32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (l₂ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89, -90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1552)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1708)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29, -32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89, -90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1692 q) 8 9 (meaning1552 q) (meaning1683 q) (meaning1708 q) hs
  change valuationOf q 1552 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1406 (q : Snake 81) (h : Conditions q) : valuation q 1552 = false ∨ valuation q 1683 = false ∨ valuation q 1708 = true := counterClause1406 (baseVal q)

theorem counterClause1407 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1708 = true := by
  have hs : count1692 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29, -32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) + (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89, -90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29, -32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (l₂ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89, -90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1553)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1708)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29, -32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89, -90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1692 q) 9 8 (meaning1553 q) (meaning1682 q) (meaning1708 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1407 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1682 = false ∨ valuation q 1708 = true := counterClause1407 (baseVal q)

theorem counterClause1408 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1708 = true := by
  have hs : count1692 q = (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29, -32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) + (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89, -90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29, -32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (l₂ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89, -90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1554)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1708)) (countLit q [-2, -3, -7, -8, -11, -13, -15, -17, -19, -22, -23, -24, -27, -29, -32, -35, -38, -39, -41, -45, -46, -47, -48, -52, -54, -55, -56, -57]) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89, -90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1692 q) 10 7 (meaning1554 q) (meaning1681 q) (meaning1708 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1408 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1681 = false ∨ valuation q 1708 = true := counterClause1408 (baseVal q)

theorem block43 (q : Snake 81) (h : Conditions q) : B112E027.Block43 (valuation q) :=
  ⟨clause1377 q h, clause1378 q h, clause1379 q h, clause1380 q h, clause1381 q h, clause1382 q h, clause1383 q h, clause1384 q h, clause1385 q h, clause1386 q h, clause1387 q h, clause1388 q h, clause1389 q h, clause1390 q h, clause1391 q h, clause1392 q h, clause1393 q h, clause1394 q h, clause1395 q h, clause1396 q h, clause1397 q h, clause1398 q h, clause1399 q h, clause1400 q h, clause1401 q h, clause1402 q h, clause1403 q h, clause1404 q h, clause1405 q h, clause1406 q h, clause1407 q h, clause1408 q h⟩

end
end Snake9.Regrowth.E112027
