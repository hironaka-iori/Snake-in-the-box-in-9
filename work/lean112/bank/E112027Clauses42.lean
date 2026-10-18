import E112027Semantics
import B112E027Inputs
namespace Snake9.Regrowth.E112027
noncomputable section
local instance blockDec42 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1345 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1666 = true := by
  have hs : count1660 q = (countLit q [-90, -92, -95, -96, -97, -98, -102]) + (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95, -96, -97, -98, -102]) (l₂ := [-104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1631)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1666)) (countLit q [-90, -92, -95, -96, -97, -98, -102]) (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) (count1660 q) 3 4 (meaning1631 q) (meaning1655 q) (meaning1666 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1345 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1655 = false ∨ valuation q 1666 = true := counterClause1345 (baseVal q)

theorem counterClause1346 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1663 = true := by
  have hs : count1660 q = (countLit q [-90, -92, -95, -96, -97, -98, -102]) + (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95, -96, -97, -98, -102]) (l₂ := [-104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_left (literal (valuationOf q) (1632)) (literal (valuationOf q) (1663)) (countLit q [-90, -92, -95, -96, -97, -98, -102]) (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) (count1660 q) 4 (meaning1632 q) (meaning1663 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1346 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1663 = true := counterClause1346 (baseVal q)

theorem counterClause1347 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1664 = true := by
  have hs : count1660 q = (countLit q [-90, -92, -95, -96, -97, -98, -102]) + (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95, -96, -97, -98, -102]) (l₂ := [-104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1632)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1664)) (countLit q [-90, -92, -95, -96, -97, -98, -102]) (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) (count1660 q) 4 1 (meaning1632 q) (meaning1652 q) (meaning1664 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1347 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1652 = false ∨ valuation q 1664 = true := counterClause1347 (baseVal q)

theorem counterClause1348 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1665 = true := by
  have hs : count1660 q = (countLit q [-90, -92, -95, -96, -97, -98, -102]) + (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95, -96, -97, -98, -102]) (l₂ := [-104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1632)) (literal (valuationOf q) (1653)) (literal (valuationOf q) (1665)) (countLit q [-90, -92, -95, -96, -97, -98, -102]) (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) (count1660 q) 4 2 (meaning1632 q) (meaning1653 q) (meaning1665 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1348 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1653 = false ∨ valuation q 1665 = true := counterClause1348 (baseVal q)

theorem counterClause1349 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1666 = true := by
  have hs : count1660 q = (countLit q [-90, -92, -95, -96, -97, -98, -102]) + (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95, -96, -97, -98, -102]) (l₂ := [-104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1632)) (literal (valuationOf q) (1654)) (literal (valuationOf q) (1666)) (countLit q [-90, -92, -95, -96, -97, -98, -102]) (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) (count1660 q) 4 3 (meaning1632 q) (meaning1654 q) (meaning1666 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1349 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1654 = false ∨ valuation q 1666 = true := counterClause1349 (baseVal q)

theorem counterClause1350 (q : Nat → Bool) : valuationOf q 1633 = false ∨ valuationOf q 1664 = true := by
  have hs : count1660 q = (countLit q [-90, -92, -95, -96, -97, -98, -102]) + (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95, -96, -97, -98, -102]) (l₂ := [-104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_left (literal (valuationOf q) (1633)) (literal (valuationOf q) (1664)) (countLit q [-90, -92, -95, -96, -97, -98, -102]) (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) (count1660 q) 5 (meaning1633 q) (meaning1664 q) hs
  change valuationOf q 1633 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1350 (q : Snake 81) (h : Conditions q) : valuation q 1633 = false ∨ valuation q 1664 = true := counterClause1350 (baseVal q)

theorem counterClause1351 (q : Nat → Bool) : valuationOf q 1633 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1665 = true := by
  have hs : count1660 q = (countLit q [-90, -92, -95, -96, -97, -98, -102]) + (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95, -96, -97, -98, -102]) (l₂ := [-104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1633)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1665)) (countLit q [-90, -92, -95, -96, -97, -98, -102]) (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) (count1660 q) 5 1 (meaning1633 q) (meaning1652 q) (meaning1665 q) hs
  change valuationOf q 1633 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1351 (q : Snake 81) (h : Conditions q) : valuation q 1633 = false ∨ valuation q 1652 = false ∨ valuation q 1665 = true := counterClause1351 (baseVal q)

theorem counterClause1352 (q : Nat → Bool) : valuationOf q 1633 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1666 = true := by
  have hs : count1660 q = (countLit q [-90, -92, -95, -96, -97, -98, -102]) + (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95, -96, -97, -98, -102]) (l₂ := [-104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1633)) (literal (valuationOf q) (1653)) (literal (valuationOf q) (1666)) (countLit q [-90, -92, -95, -96, -97, -98, -102]) (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) (count1660 q) 5 2 (meaning1633 q) (meaning1653 q) (meaning1666 q) hs
  change valuationOf q 1633 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1352 (q : Snake 81) (h : Conditions q) : valuation q 1633 = false ∨ valuation q 1653 = false ∨ valuation q 1666 = true := counterClause1352 (baseVal q)

theorem counterClause1353 (q : Nat → Bool) : valuationOf q 1633 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1667 = true := by
  have hs : count1660 q = (countLit q [-90, -92, -95, -96, -97, -98, -102]) + (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95, -96, -97, -98, -102]) (l₂ := [-104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1633)) (literal (valuationOf q) (1654)) (literal (valuationOf q) (1667)) (countLit q [-90, -92, -95, -96, -97, -98, -102]) (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) (count1660 q) 5 3 (meaning1633 q) (meaning1654 q) (meaning1667 q) hs
  change valuationOf q 1633 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1353 (q : Snake 81) (h : Conditions q) : valuation q 1633 = false ∨ valuation q 1654 = false ∨ valuation q 1667 = true := counterClause1353 (baseVal q)

theorem counterClause1354 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1665 = true := by
  have hs : count1660 q = (countLit q [-90, -92, -95, -96, -97, -98, -102]) + (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95, -96, -97, -98, -102]) (l₂ := [-104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_left (literal (valuationOf q) (1634)) (literal (valuationOf q) (1665)) (countLit q [-90, -92, -95, -96, -97, -98, -102]) (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) (count1660 q) 6 (meaning1634 q) (meaning1665 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1354 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1665 = true := counterClause1354 (baseVal q)

theorem counterClause1355 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1666 = true := by
  have hs : count1660 q = (countLit q [-90, -92, -95, -96, -97, -98, -102]) + (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95, -96, -97, -98, -102]) (l₂ := [-104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1666)) (countLit q [-90, -92, -95, -96, -97, -98, -102]) (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) (count1660 q) 6 1 (meaning1634 q) (meaning1652 q) (meaning1666 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1355 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1652 = false ∨ valuation q 1666 = true := counterClause1355 (baseVal q)

theorem counterClause1356 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1667 = true := by
  have hs : count1660 q = (countLit q [-90, -92, -95, -96, -97, -98, -102]) + (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95, -96, -97, -98, -102]) (l₂ := [-104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1653)) (literal (valuationOf q) (1667)) (countLit q [-90, -92, -95, -96, -97, -98, -102]) (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) (count1660 q) 6 2 (meaning1634 q) (meaning1653 q) (meaning1667 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1356 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1653 = false ∨ valuation q 1667 = true := counterClause1356 (baseVal q)

theorem counterClause1357 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1668 = true := by
  have hs : count1660 q = (countLit q [-90, -92, -95, -96, -97, -98, -102]) + (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95, -96, -97, -98, -102]) (l₂ := [-104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1654)) (literal (valuationOf q) (1668)) (countLit q [-90, -92, -95, -96, -97, -98, -102]) (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) (count1660 q) 6 3 (meaning1634 q) (meaning1654 q) (meaning1668 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1357 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1654 = false ∨ valuation q 1668 = true := counterClause1357 (baseVal q)

theorem counterClause1358 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1679 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1602)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1679)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 1 4 (meaning1602 q) (meaning1663 q) (meaning1679 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1358 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1663 = false ∨ valuation q 1679 = true := counterClause1358 (baseVal q)

theorem counterClause1359 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1680 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1602)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1680)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 1 5 (meaning1602 q) (meaning1664 q) (meaning1680 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1359 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1664 = false ∨ valuation q 1680 = true := counterClause1359 (baseVal q)

theorem counterClause1360 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1681 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1602)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1681)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 1 6 (meaning1602 q) (meaning1665 q) (meaning1681 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1360 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1665 = false ∨ valuation q 1681 = true := counterClause1360 (baseVal q)

theorem counterClause1361 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1682 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1602)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1682)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 1 7 (meaning1602 q) (meaning1666 q) (meaning1682 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1361 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1666 = false ∨ valuation q 1682 = true := counterClause1361 (baseVal q)

theorem counterClause1362 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1683 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1602)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1683)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 1 8 (meaning1602 q) (meaning1667 q) (meaning1683 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1362 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1667 = false ∨ valuation q 1683 = true := counterClause1362 (baseVal q)

theorem counterClause1363 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1680 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1603)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1680)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 2 4 (meaning1603 q) (meaning1663 q) (meaning1680 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1363 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1663 = false ∨ valuation q 1680 = true := counterClause1363 (baseVal q)

theorem counterClause1364 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1681 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1603)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1681)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 2 5 (meaning1603 q) (meaning1664 q) (meaning1681 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1364 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1664 = false ∨ valuation q 1681 = true := counterClause1364 (baseVal q)

theorem counterClause1365 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1682 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1603)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1682)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 2 6 (meaning1603 q) (meaning1665 q) (meaning1682 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1365 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1665 = false ∨ valuation q 1682 = true := counterClause1365 (baseVal q)

theorem counterClause1366 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1683 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1603)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1683)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 2 7 (meaning1603 q) (meaning1666 q) (meaning1683 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1366 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1666 = false ∨ valuation q 1683 = true := counterClause1366 (baseVal q)

theorem counterClause1367 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1684 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1603)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1684)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 2 8 (meaning1603 q) (meaning1667 q) (meaning1684 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1367 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1667 = false ∨ valuation q 1684 = true := counterClause1367 (baseVal q)

theorem counterClause1368 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1685 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1603)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1685)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 2 9 (meaning1603 q) (meaning1668 q) (meaning1685 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1368 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1668 = false ∨ valuation q 1685 = true := counterClause1368 (baseVal q)

theorem counterClause1369 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1680 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1680)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 3 3 (meaning1604 q) (meaning1662 q) (meaning1680 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1369 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1662 = false ∨ valuation q 1680 = true := counterClause1369 (baseVal q)

theorem counterClause1370 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1681 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1681)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 3 4 (meaning1604 q) (meaning1663 q) (meaning1681 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1370 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1663 = false ∨ valuation q 1681 = true := counterClause1370 (baseVal q)

theorem counterClause1371 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1682 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1682)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 3 5 (meaning1604 q) (meaning1664 q) (meaning1682 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1371 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1664 = false ∨ valuation q 1682 = true := counterClause1371 (baseVal q)

theorem counterClause1372 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1683 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1683)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 3 6 (meaning1604 q) (meaning1665 q) (meaning1683 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1372 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1665 = false ∨ valuation q 1683 = true := counterClause1372 (baseVal q)

theorem counterClause1373 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1684 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1684)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 3 7 (meaning1604 q) (meaning1666 q) (meaning1684 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1373 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1666 = false ∨ valuation q 1684 = true := counterClause1373 (baseVal q)

theorem counterClause1374 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1685 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1685)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 3 8 (meaning1604 q) (meaning1667 q) (meaning1685 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1374 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1667 = false ∨ valuation q 1685 = true := counterClause1374 (baseVal q)

theorem counterClause1375 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1680 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1680)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 4 2 (meaning1605 q) (meaning1661 q) (meaning1680 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1375 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1661 = false ∨ valuation q 1680 = true := counterClause1375 (baseVal q)

theorem counterClause1376 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1681 = true := by
  have hs : count1675 q = (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) + (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (l₂ := [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1605)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1681)) (countLit q [-59, -61, -64, -67, -68, -70, -74, -75, -76, -77, -81, -82, -85, -89]) (countLit q [-90, -92, -95, -96, -97, -98, -102, -104, -105, -106, -108, -111, -114, -115, -117]) (count1675 q) 4 3 (meaning1605 q) (meaning1662 q) (meaning1681 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1376 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1662 = false ∨ valuation q 1681 = true := counterClause1376 (baseVal q)

theorem block42 (q : Snake 81) (h : Conditions q) : B112E027.Block42 (valuation q) :=
  ⟨clause1345 q h, clause1346 q h, clause1347 q h, clause1348 q h, clause1349 q h, clause1350 q h, clause1351 q h, clause1352 q h, clause1353 q h, clause1354 q h, clause1355 q h, clause1356 q h, clause1357 q h, clause1358 q h, clause1359 q h, clause1360 q h, clause1361 q h, clause1362 q h, clause1363 q h, clause1364 q h, clause1365 q h, clause1366 q h, clause1367 q h, clause1368 q h, clause1369 q h, clause1370 q h, clause1371 q h, clause1372 q h, clause1373 q h, clause1374 q h, clause1375 q h, clause1376 q h⟩

end
end Snake9.Regrowth.E112027
