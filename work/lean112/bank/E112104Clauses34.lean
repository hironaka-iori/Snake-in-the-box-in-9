import E112104Semantics
import B112E104Inputs
namespace Snake9.Regrowth.E112104
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1089 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1661 = true := by
  have hs : count1654 q = (countLit q [-90, -93, -94, -97, -99, -101, -102]) + (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -97, -99, -101, -102]) (l₂ := [-105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1661)) (countLit q [-90, -93, -94, -97, -99, -101, -102]) (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) (count1654 q) 5 3 (meaning1627 q) (meaning1648 q) (meaning1661 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1648 = false ∨ valuation q 1661 = true := counterClause1089 (baseVal q)

theorem counterClause1090 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1662 = true := by
  have hs : count1654 q = (countLit q [-90, -93, -94, -97, -99, -101, -102]) + (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -97, -99, -101, -102]) (l₂ := [-105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1662)) (countLit q [-90, -93, -94, -97, -99, -101, -102]) (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) (count1654 q) 5 4 (meaning1627 q) (meaning1649 q) (meaning1662 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1649 = false ∨ valuation q 1662 = true := counterClause1090 (baseVal q)

theorem counterClause1091 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1663 = true := by
  have hs : count1654 q = (countLit q [-90, -93, -94, -97, -99, -101, -102]) + (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-90, -93, -94, -97, -99, -101, -102]) (l₂ := [-105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1663)) (countLit q [-90, -93, -94, -97, -99, -101, -102]) (countLit q [-105, -107, -108, -109, -111, -112, -115, -118]) (count1654 q) 5 5 (meaning1627 q) (meaning1650 q) (meaning1663 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1650 = false ∨ valuation q 1663 = true := counterClause1091 (baseVal q)

theorem counterClause1092 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1676 = true := by
  have hs : count1669 q = (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) + (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (l₂ := [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1676)) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1669 q) 1 7 (meaning1595 q) (meaning1660 q) (meaning1676 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1676 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1660 = false ∨ valuation q 1676 = true := counterClause1092 (baseVal q)

theorem counterClause1093 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1677 = true := by
  have hs : count1669 q = (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) + (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (l₂ := [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1677)) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1669 q) 1 8 (meaning1595 q) (meaning1661 q) (meaning1677 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1661 = false ∨ valuation q 1677 = true := counterClause1093 (baseVal q)

theorem counterClause1094 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1678 = true := by
  have hs : count1669 q = (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) + (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (l₂ := [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1678)) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1669 q) 1 9 (meaning1595 q) (meaning1662 q) (meaning1678 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1662 = false ∨ valuation q 1678 = true := counterClause1094 (baseVal q)

theorem counterClause1095 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1679 = true := by
  have hs : count1669 q = (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) + (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (l₂ := [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1679)) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1669 q) 1 10 (meaning1595 q) (meaning1663 q) (meaning1679 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1663 = false ∨ valuation q 1679 = true := counterClause1095 (baseVal q)

theorem counterClause1096 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1675 = true := by
  have hs : count1669 q = (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) + (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (l₂ := [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1675)) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1669 q) 2 5 (meaning1596 q) (meaning1658 q) (meaning1675 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1675 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1658 = false ∨ valuation q 1675 = true := counterClause1096 (baseVal q)

theorem counterClause1097 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1676 = true := by
  have hs : count1669 q = (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) + (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (l₂ := [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1676)) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1669 q) 2 6 (meaning1596 q) (meaning1659 q) (meaning1676 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1676 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1659 = false ∨ valuation q 1676 = true := counterClause1097 (baseVal q)

theorem counterClause1098 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1677 = true := by
  have hs : count1669 q = (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) + (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (l₂ := [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1677)) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1669 q) 2 7 (meaning1596 q) (meaning1660 q) (meaning1677 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1660 = false ∨ valuation q 1677 = true := counterClause1098 (baseVal q)

theorem counterClause1099 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1678 = true := by
  have hs : count1669 q = (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) + (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (l₂ := [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1678)) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1669 q) 2 8 (meaning1596 q) (meaning1661 q) (meaning1678 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1661 = false ∨ valuation q 1678 = true := counterClause1099 (baseVal q)

theorem counterClause1100 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1679 = true := by
  have hs : count1669 q = (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) + (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (l₂ := [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1679)) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1669 q) 2 9 (meaning1596 q) (meaning1662 q) (meaning1679 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1662 = false ∨ valuation q 1679 = true := counterClause1100 (baseVal q)

theorem counterClause1101 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1676 = true := by
  have hs : count1669 q = (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) + (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (l₂ := [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1676)) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1669 q) 3 5 (meaning1597 q) (meaning1658 q) (meaning1676 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1676 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1658 = false ∨ valuation q 1676 = true := counterClause1101 (baseVal q)

theorem counterClause1102 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1677 = true := by
  have hs : count1669 q = (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) + (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (l₂ := [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1677)) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1669 q) 3 6 (meaning1597 q) (meaning1659 q) (meaning1677 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1659 = false ∨ valuation q 1677 = true := counterClause1102 (baseVal q)

theorem counterClause1103 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1678 = true := by
  have hs : count1669 q = (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) + (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (l₂ := [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1678)) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1669 q) 3 7 (meaning1597 q) (meaning1660 q) (meaning1678 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1660 = false ∨ valuation q 1678 = true := counterClause1103 (baseVal q)

theorem counterClause1104 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1679 = true := by
  have hs : count1669 q = (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) + (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (l₂ := [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1679)) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1669 q) 3 8 (meaning1597 q) (meaning1661 q) (meaning1679 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1661 = false ∨ valuation q 1679 = true := counterClause1104 (baseVal q)

theorem counterClause1105 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1680 = true := by
  have hs : count1669 q = (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) + (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (l₂ := [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1680)) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1669 q) 3 9 (meaning1597 q) (meaning1662 q) (meaning1680 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1662 = false ∨ valuation q 1680 = true := counterClause1105 (baseVal q)

theorem counterClause1106 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1675 = true := by
  have hs : count1669 q = (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) + (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (l₂ := [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1675)) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1669 q) 4 3 (meaning1598 q) (meaning1656 q) (meaning1675 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1675 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1656 = false ∨ valuation q 1675 = true := counterClause1106 (baseVal q)

theorem counterClause1107 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1676 = true := by
  have hs : count1669 q = (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) + (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (l₂ := [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1676)) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1669 q) 4 4 (meaning1598 q) (meaning1657 q) (meaning1676 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1676 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1657 = false ∨ valuation q 1676 = true := counterClause1107 (baseVal q)

theorem counterClause1108 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1677 = true := by
  have hs : count1669 q = (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) + (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (l₂ := [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1677)) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1669 q) 4 5 (meaning1598 q) (meaning1658 q) (meaning1677 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1658 = false ∨ valuation q 1677 = true := counterClause1108 (baseVal q)

theorem counterClause1109 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1678 = true := by
  have hs : count1669 q = (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) + (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (l₂ := [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1678)) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1669 q) 4 6 (meaning1598 q) (meaning1659 q) (meaning1678 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1659 = false ∨ valuation q 1678 = true := counterClause1109 (baseVal q)

theorem counterClause1110 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1679 = true := by
  have hs : count1669 q = (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) + (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (l₂ := [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1679)) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1669 q) 4 7 (meaning1598 q) (meaning1660 q) (meaning1679 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1660 = false ∨ valuation q 1679 = true := counterClause1110 (baseVal q)

theorem counterClause1111 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1680 = true := by
  have hs : count1669 q = (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) + (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (l₂ := [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1680)) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1669 q) 4 8 (meaning1598 q) (meaning1661 q) (meaning1680 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1661 = false ∨ valuation q 1680 = true := counterClause1111 (baseVal q)

theorem counterClause1112 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1675 = true := by
  have hs : count1669 q = (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) + (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (l₂ := [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1675)) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1669 q) 5 2 (meaning1599 q) (meaning1655 q) (meaning1675 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1675 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1655 = false ∨ valuation q 1675 = true := counterClause1112 (baseVal q)

theorem counterClause1113 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1676 = true := by
  have hs : count1669 q = (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) + (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (l₂ := [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1676)) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1669 q) 5 3 (meaning1599 q) (meaning1656 q) (meaning1676 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1676 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1656 = false ∨ valuation q 1676 = true := counterClause1113 (baseVal q)

theorem counterClause1114 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1677 = true := by
  have hs : count1669 q = (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) + (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (l₂ := [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1677)) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1669 q) 5 4 (meaning1599 q) (meaning1657 q) (meaning1677 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1657 = false ∨ valuation q 1677 = true := counterClause1114 (baseVal q)

theorem counterClause1115 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1678 = true := by
  have hs : count1669 q = (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) + (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (l₂ := [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1678)) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1669 q) 5 5 (meaning1599 q) (meaning1658 q) (meaning1678 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1658 = false ∨ valuation q 1678 = true := counterClause1115 (baseVal q)

theorem counterClause1116 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1679 = true := by
  have hs : count1669 q = (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) + (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (l₂ := [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1679)) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1669 q) 5 6 (meaning1599 q) (meaning1659 q) (meaning1679 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1659 = false ∨ valuation q 1679 = true := counterClause1116 (baseVal q)

theorem counterClause1117 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1680 = true := by
  have hs : count1669 q = (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) + (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (l₂ := [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1680)) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1669 q) 5 7 (meaning1599 q) (meaning1660 q) (meaning1680 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1660 = false ∨ valuation q 1680 = true := counterClause1117 (baseVal q)

theorem counterClause1118 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1678 = true := by
  have hs : count1669 q = (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) + (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (l₂ := [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1678)) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1669 q) 6 4 (meaning1600 q) (meaning1657 q) (meaning1678 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1657 = false ∨ valuation q 1678 = true := counterClause1118 (baseVal q)

theorem counterClause1119 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1679 = true := by
  have hs : count1669 q = (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) + (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (l₂ := [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1679)) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1669 q) 6 5 (meaning1600 q) (meaning1658 q) (meaning1679 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1658 = false ∨ valuation q 1679 = true := counterClause1119 (baseVal q)

theorem counterClause1120 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1680 = true := by
  have hs : count1669 q = (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) + (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) := List.countP_append (p := literal q) (l₁ := [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (l₂ := [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1680)) (countLit q [-59, -60, -63, -65, -67, -69, -72, -73, -76, -77, -80, -82, -84, -86, -89]) (countLit q [-90, -93, -94, -97, -99, -101, -102, -105, -107, -108, -109, -111, -112, -115, -118]) (count1669 q) 6 6 (meaning1600 q) (meaning1659 q) (meaning1680 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1659 = false ∨ valuation q 1680 = true := counterClause1120 (baseVal q)

theorem block34 (q : Snake 81) (h : Conditions q) : B112E104.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.E112104
