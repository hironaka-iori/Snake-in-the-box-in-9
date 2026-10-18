import E112078Semantics
import B112E078Inputs
namespace Snake9.Regrowth.E112078
noncomputable section
local instance blockDec36 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1153 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1698 = true := by
  have hs : count1691 q = (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1619)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1698)) (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) (count1691 q) 2 6 (meaning1619 q) (meaning1681 q) (meaning1698 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1153 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1681 = false ∨ valuation q 1698 = true := counterClause1153 (baseVal q)

theorem counterClause1154 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1699 = true := by
  have hs : count1691 q = (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1619)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1699)) (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) (count1691 q) 2 7 (meaning1619 q) (meaning1682 q) (meaning1699 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1154 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1682 = false ∨ valuation q 1699 = true := counterClause1154 (baseVal q)

theorem counterClause1155 (q : Nat → Bool) : valuationOf q 1620 = false ∨ valuationOf q 1677 = false ∨ valuationOf q 1695 = true := by
  have hs : count1691 q = (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1620)) (literal (valuationOf q) (1677)) (literal (valuationOf q) (1695)) (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) (count1691 q) 3 2 (meaning1620 q) (meaning1677 q) (meaning1695 q) hs
  change valuationOf q 1620 = false ∨ valuationOf q 1677 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1155 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1677 = false ∨ valuation q 1695 = true := counterClause1155 (baseVal q)

theorem counterClause1156 (q : Nat → Bool) : valuationOf q 1620 = false ∨ valuationOf q 1678 = false ∨ valuationOf q 1696 = true := by
  have hs : count1691 q = (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1620)) (literal (valuationOf q) (1678)) (literal (valuationOf q) (1696)) (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) (count1691 q) 3 3 (meaning1620 q) (meaning1678 q) (meaning1696 q) hs
  change valuationOf q 1620 = false ∨ valuationOf q 1678 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1156 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1678 = false ∨ valuation q 1696 = true := counterClause1156 (baseVal q)

theorem counterClause1157 (q : Nat → Bool) : valuationOf q 1620 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1697 = true := by
  have hs : count1691 q = (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1620)) (literal (valuationOf q) (1679)) (literal (valuationOf q) (1697)) (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) (count1691 q) 3 4 (meaning1620 q) (meaning1679 q) (meaning1697 q) hs
  change valuationOf q 1620 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1157 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1679 = false ∨ valuation q 1697 = true := counterClause1157 (baseVal q)

theorem counterClause1158 (q : Nat → Bool) : valuationOf q 1620 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1698 = true := by
  have hs : count1691 q = (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1620)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1698)) (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) (count1691 q) 3 5 (meaning1620 q) (meaning1680 q) (meaning1698 q) hs
  change valuationOf q 1620 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1158 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1680 = false ∨ valuation q 1698 = true := counterClause1158 (baseVal q)

theorem counterClause1159 (q : Nat → Bool) : valuationOf q 1620 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1699 = true := by
  have hs : count1691 q = (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1620)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1699)) (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) (count1691 q) 3 6 (meaning1620 q) (meaning1681 q) (meaning1699 q) hs
  change valuationOf q 1620 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1159 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1681 = false ∨ valuation q 1699 = true := counterClause1159 (baseVal q)

theorem counterClause1160 (q : Nat → Bool) : valuationOf q 1621 = false ∨ valuationOf q 1677 = false ∨ valuationOf q 1696 = true := by
  have hs : count1691 q = (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1621)) (literal (valuationOf q) (1677)) (literal (valuationOf q) (1696)) (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) (count1691 q) 4 2 (meaning1621 q) (meaning1677 q) (meaning1696 q) hs
  change valuationOf q 1621 = false ∨ valuationOf q 1677 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1160 (q : Snake 81) (h : Conditions q) : valuation q 1621 = false ∨ valuation q 1677 = false ∨ valuation q 1696 = true := counterClause1160 (baseVal q)

theorem counterClause1161 (q : Nat → Bool) : valuationOf q 1621 = false ∨ valuationOf q 1678 = false ∨ valuationOf q 1697 = true := by
  have hs : count1691 q = (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1621)) (literal (valuationOf q) (1678)) (literal (valuationOf q) (1697)) (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) (count1691 q) 4 3 (meaning1621 q) (meaning1678 q) (meaning1697 q) hs
  change valuationOf q 1621 = false ∨ valuationOf q 1678 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1161 (q : Snake 81) (h : Conditions q) : valuation q 1621 = false ∨ valuation q 1678 = false ∨ valuation q 1697 = true := counterClause1161 (baseVal q)

theorem counterClause1162 (q : Nat → Bool) : valuationOf q 1621 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1698 = true := by
  have hs : count1691 q = (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1621)) (literal (valuationOf q) (1679)) (literal (valuationOf q) (1698)) (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) (count1691 q) 4 4 (meaning1621 q) (meaning1679 q) (meaning1698 q) hs
  change valuationOf q 1621 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1162 (q : Snake 81) (h : Conditions q) : valuation q 1621 = false ∨ valuation q 1679 = false ∨ valuation q 1698 = true := counterClause1162 (baseVal q)

theorem counterClause1163 (q : Nat → Bool) : valuationOf q 1621 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1699 = true := by
  have hs : count1691 q = (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1621)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1699)) (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) (count1691 q) 4 5 (meaning1621 q) (meaning1680 q) (meaning1699 q) hs
  change valuationOf q 1621 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1163 (q : Snake 81) (h : Conditions q) : valuation q 1621 = false ∨ valuation q 1680 = false ∨ valuation q 1699 = true := counterClause1163 (baseVal q)

theorem counterClause1164 (q : Nat → Bool) : valuationOf q 1622 = false ∨ valuationOf q 1677 = false ∨ valuationOf q 1697 = true := by
  have hs : count1691 q = (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) + (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (l₂ := [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1622)) (literal (valuationOf q) (1677)) (literal (valuationOf q) (1697)) (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89]) (countLit q [-90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) (count1691 q) 5 2 (meaning1622 q) (meaning1677 q) (meaning1697 q) hs
  change valuationOf q 1622 = false ∨ valuationOf q 1677 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1164 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1677 = false ∨ valuation q 1697 = true := counterClause1164 (baseVal q)

theorem counterClause1165 (q : Nat → Bool) : valuationOf q 1568 = false ∨ valuationOf q 1699 = false ∨ valuationOf q 1726 = true := by
  have hs : count1709 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26, -27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) + (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89, -90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26, -27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (l₂ := [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89, -90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1568)) (literal (valuationOf q) (1699)) (literal (valuationOf q) (1726)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26, -27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89, -90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) (count1709 q) 9 9 (meaning1568 q) (meaning1699 q) (meaning1726 q) hs
  change valuationOf q 1568 = false ∨ valuationOf q 1699 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1165 (q : Snake 81) (h : Conditions q) : valuation q 1568 = false ∨ valuation q 1699 = false ∨ valuation q 1726 = true := counterClause1165 (baseVal q)

theorem counterClause1166 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1698 = false ∨ valuationOf q 1726 = true := by
  have hs : count1709 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26, -27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) + (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89, -90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26, -27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (l₂ := [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89, -90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1569)) (literal (valuationOf q) (1698)) (literal (valuationOf q) (1726)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26, -27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89, -90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) (count1709 q) 10 8 (meaning1569 q) (meaning1698 q) (meaning1726 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1698 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1166 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1698 = false ∨ valuation q 1726 = true := counterClause1166 (baseVal q)

theorem counterClause1167 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1726 = true := by
  have hs : count1709 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26, -27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) + (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89, -90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26, -27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (l₂ := [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89, -90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1570)) (literal (valuationOf q) (1697)) (literal (valuationOf q) (1726)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26, -27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89, -90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) (count1709 q) 11 7 (meaning1570 q) (meaning1697 q) (meaning1726 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1167 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1697 = false ∨ valuation q 1726 = true := counterClause1167 (baseVal q)

theorem counterClause1168 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1726 = true := by
  have hs : count1709 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26, -27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) + (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89, -90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26, -27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (l₂ := [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89, -90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1696)) (literal (valuationOf q) (1726)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26, -27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89, -90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) (count1709 q) 12 6 (meaning1571 q) (meaning1696 q) (meaning1726 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1168 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1696 = false ∨ valuation q 1726 = true := counterClause1168 (baseVal q)

theorem counterClause1169 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1726 = true := by
  have hs : count1709 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26, -27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) + (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89, -90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26, -27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (l₂ := [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89, -90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1695)) (literal (valuationOf q) (1726)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26, -27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89, -90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) (count1709 q) 13 5 (meaning1572 q) (meaning1695 q) (meaning1726 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1169 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1695 = false ∨ valuation q 1726 = true := counterClause1169 (baseVal q)

theorem counterClause1170 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1726 = true := by
  have hs : count1709 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26, -27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) + (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89, -90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26, -27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (l₂ := [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89, -90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1573)) (literal (valuationOf q) (1694)) (literal (valuationOf q) (1726)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26, -27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (countLit q [-61, -63, -66, -67, -70, -72, -73, -75, -79, -80, -81, -82, -86, -89, -90, -92, -96, -97, -98, -99, -103, -105, -106, -107, -109, -112, -115, -116, -118]) (count1709 q) 14 4 (meaning1573 q) (meaning1694 q) (meaning1726 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1170 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1694 = false ∨ valuation q 1726 = true := counterClause1170 (baseVal q)

theorem clause1171 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false := by
  rw [value1726]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1709 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1172 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 2 = false ∨ valuation q 39 = false ∨ valuation q 40 = false := by
  rw [value1, value2, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (66 : Vertex) (67 : Vertex) (194 : Vertex) (195 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1173 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 9 = false := by
  rw [value1, value5, value7, value9]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (66 : Vertex) (70 : Vertex) (74 : Vertex) (78 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1174 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 7 = false ∨ valuation q 39 = false ∨ valuation q 44 = false := by
  rw [value1, value7, value39, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (66 : Vertex) (74 : Vertex) (194 : Vertex) (202 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1175 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 4 = false ∨ valuation q 11 = false ∨ valuation q 12 = false := by
  rw [value3, value4, value11, value12]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (68 : Vertex) (69 : Vertex) (84 : Vertex) (85 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1176 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 5 = false ∨ valuation q 8 = false ∨ valuation q 9 = false := by
  rw [value3, value5, value8, value9]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (68 : Vertex) (70 : Vertex) (76 : Vertex) (78 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1177 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 15 = false ∨ valuation q 43 = false ∨ valuation q 55 = false := by
  rw [value6, value15, value43, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (73 : Vertex) (89 : Vertex) (201 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1178 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 43 = false ∨ valuation q 74 = false ∨ valuation q 106 = false := by
  rw [value6, value43, value74, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (73 : Vertex) (201 : Vertex) (329 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1179 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 9 = false ∨ valuation q 45 = false ∨ valuation q 47 = false := by
  rw [value8, value9, value45, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (76 : Vertex) (78 : Vertex) (204 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1180 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 14 = false ∨ valuation q 49 = false ∨ valuation q 54 = false := by
  rw [value10, value14, value49, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (80 : Vertex) (88 : Vertex) (208 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1181 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 17 = false := by
  rw [value14, value15, value16, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (88 : Vertex) (89 : Vertex) (90 : Vertex) (91 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1182 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 54 = false ∨ valuation q 55 = false := by
  rw [value14, value15, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (88 : Vertex) (89 : Vertex) (216 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1183 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 23 = false := by
  rw [value19, value20, value22, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (130 : Vertex) (131 : Vertex) (134 : Vertex) (135 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1184 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 20 = false ∨ valuation q 39 = false ∨ valuation q 40 = false := by
  rw [value19, value20, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (130 : Vertex) (131 : Vertex) (194 : Vertex) (195 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block36 (q : Snake 81) (h : Conditions q) : B112E078.Block36 (valuation q) :=
  ⟨clause1153 q h, clause1154 q h, clause1155 q h, clause1156 q h, clause1157 q h, clause1158 q h, clause1159 q h, clause1160 q h, clause1161 q h, clause1162 q h, clause1163 q h, clause1164 q h, clause1165 q h, clause1166 q h, clause1167 q h, clause1168 q h, clause1169 q h, clause1170 q h, clause1171 q h, clause1172 q h, clause1173 q h, clause1174 q h, clause1175 q h, clause1176 q h, clause1177 q h, clause1178 q h, clause1179 q h, clause1180 q h, clause1181 q h, clause1182 q h, clause1183 q h, clause1184 q h⟩

end
end Snake9.Regrowth.E112078
