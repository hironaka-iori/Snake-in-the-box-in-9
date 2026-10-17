import E112110Semantics
import B112E110Inputs
namespace Snake9.Regrowth.E112110
noncomputable section
local instance blockDec38 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1217 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1678 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1678)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 3 7 (meaning1597 q) (meaning1660 q) (meaning1678 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1217 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1660 = false ∨ valuation q 1678 = true := counterClause1217 (baseVal q)

theorem counterClause1218 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1679 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1679)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 3 8 (meaning1597 q) (meaning1661 q) (meaning1679 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1218 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1661 = false ∨ valuation q 1679 = true := counterClause1218 (baseVal q)

theorem counterClause1219 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1680 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1680)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 3 9 (meaning1597 q) (meaning1662 q) (meaning1680 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1219 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1662 = false ∨ valuation q 1680 = true := counterClause1219 (baseVal q)

theorem counterClause1220 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1681 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1681)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 3 10 (meaning1597 q) (meaning1663 q) (meaning1681 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1220 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1663 = false ∨ valuation q 1681 = true := counterClause1220 (baseVal q)

theorem counterClause1221 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1677 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1677)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 4 5 (meaning1598 q) (meaning1658 q) (meaning1677 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1221 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1658 = false ∨ valuation q 1677 = true := counterClause1221 (baseVal q)

theorem counterClause1222 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1678 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1678)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 4 6 (meaning1598 q) (meaning1659 q) (meaning1678 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1222 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1659 = false ∨ valuation q 1678 = true := counterClause1222 (baseVal q)

theorem counterClause1223 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1679 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1679)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 4 7 (meaning1598 q) (meaning1660 q) (meaning1679 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1223 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1660 = false ∨ valuation q 1679 = true := counterClause1223 (baseVal q)

theorem counterClause1224 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1680 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1680)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 4 8 (meaning1598 q) (meaning1661 q) (meaning1680 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1224 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1661 = false ∨ valuation q 1680 = true := counterClause1224 (baseVal q)

theorem counterClause1225 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1681 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1681)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 4 9 (meaning1598 q) (meaning1662 q) (meaning1681 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1225 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1662 = false ∨ valuation q 1681 = true := counterClause1225 (baseVal q)

theorem counterClause1226 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1682 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1682)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 4 10 (meaning1598 q) (meaning1663 q) (meaning1682 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1226 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1663 = false ∨ valuation q 1682 = true := counterClause1226 (baseVal q)

theorem counterClause1227 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1677 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1677)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 5 4 (meaning1599 q) (meaning1657 q) (meaning1677 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1227 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1657 = false ∨ valuation q 1677 = true := counterClause1227 (baseVal q)

theorem counterClause1228 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1678 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1678)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 5 5 (meaning1599 q) (meaning1658 q) (meaning1678 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1228 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1658 = false ∨ valuation q 1678 = true := counterClause1228 (baseVal q)

theorem counterClause1229 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1679 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1679)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 5 6 (meaning1599 q) (meaning1659 q) (meaning1679 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1229 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1659 = false ∨ valuation q 1679 = true := counterClause1229 (baseVal q)

theorem counterClause1230 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1680 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1680)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 5 7 (meaning1599 q) (meaning1660 q) (meaning1680 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1230 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1660 = false ∨ valuation q 1680 = true := counterClause1230 (baseVal q)

theorem counterClause1231 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1681 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1681)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 5 8 (meaning1599 q) (meaning1661 q) (meaning1681 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1231 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1661 = false ∨ valuation q 1681 = true := counterClause1231 (baseVal q)

theorem counterClause1232 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1682 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1682)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 5 9 (meaning1599 q) (meaning1662 q) (meaning1682 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1232 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1662 = false ∨ valuation q 1682 = true := counterClause1232 (baseVal q)

theorem counterClause1233 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1678 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1678)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 6 4 (meaning1600 q) (meaning1657 q) (meaning1678 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1233 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1657 = false ∨ valuation q 1678 = true := counterClause1233 (baseVal q)

theorem counterClause1234 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1679 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1679)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 6 5 (meaning1600 q) (meaning1658 q) (meaning1679 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1234 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1658 = false ∨ valuation q 1679 = true := counterClause1234 (baseVal q)

theorem counterClause1235 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1680 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1680)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 6 6 (meaning1600 q) (meaning1659 q) (meaning1680 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1235 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1659 = false ∨ valuation q 1680 = true := counterClause1235 (baseVal q)

theorem counterClause1236 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1681 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1681)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 6 7 (meaning1600 q) (meaning1660 q) (meaning1681 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1236 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1660 = false ∨ valuation q 1681 = true := counterClause1236 (baseVal q)

theorem counterClause1237 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1682 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1682)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 6 8 (meaning1600 q) (meaning1661 q) (meaning1682 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1237 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1661 = false ∨ valuation q 1682 = true := counterClause1237 (baseVal q)

theorem counterClause1238 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1679 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1679)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 7 4 (meaning1601 q) (meaning1657 q) (meaning1679 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1238 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1657 = false ∨ valuation q 1679 = true := counterClause1238 (baseVal q)

theorem counterClause1239 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1680 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1680)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 7 5 (meaning1601 q) (meaning1658 q) (meaning1680 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1239 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1658 = false ∨ valuation q 1680 = true := counterClause1239 (baseVal q)

theorem counterClause1240 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1681 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1681)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 7 6 (meaning1601 q) (meaning1659 q) (meaning1681 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1240 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1659 = false ∨ valuation q 1681 = true := counterClause1240 (baseVal q)

theorem counterClause1241 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1682 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1682)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 7 7 (meaning1601 q) (meaning1660 q) (meaning1682 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1241 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1660 = false ∨ valuation q 1682 = true := counterClause1241 (baseVal q)

theorem counterClause1242 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1683 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1683)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 7 8 (meaning1601 q) (meaning1661 q) (meaning1683 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1242 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1661 = false ∨ valuation q 1683 = true := counterClause1242 (baseVal q)

theorem counterClause1243 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1680 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1602)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1680)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 8 4 (meaning1602 q) (meaning1657 q) (meaning1680 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1243 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1657 = false ∨ valuation q 1680 = true := counterClause1243 (baseVal q)

theorem counterClause1244 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1681 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1602)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1681)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 8 5 (meaning1602 q) (meaning1658 q) (meaning1681 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1244 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1658 = false ∨ valuation q 1681 = true := counterClause1244 (baseVal q)

theorem counterClause1245 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1682 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1602)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1682)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 8 6 (meaning1602 q) (meaning1659 q) (meaning1682 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1245 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1659 = false ∨ valuation q 1682 = true := counterClause1245 (baseVal q)

theorem counterClause1246 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1681 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1603)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1681)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 9 4 (meaning1603 q) (meaning1657 q) (meaning1681 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1246 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1657 = false ∨ valuation q 1681 = true := counterClause1246 (baseVal q)

theorem counterClause1247 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1682 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1603)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1682)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 9 5 (meaning1603 q) (meaning1658 q) (meaning1682 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1247 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1658 = false ∨ valuation q 1682 = true := counterClause1247 (baseVal q)

theorem counterClause1248 (q : Nat → Bool) : valuationOf q 1535 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1708 = true := by
  have hs : count1689 q = (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) + (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86, -88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (l₂ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86, -88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1535)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1708)) (countLit q [-2, -4, -5, -6, -9, -11, -13, -14, -16, -19, -20, -22, -25, -27, -29, -30, -32, -35, -37, -38, -40, -42, -45, -46, -48, -49, -52, -54, -55, -58]) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86, -88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1689 q) 5 15 (meaning1535 q) (meaning1683 q) (meaning1708 q) hs
  change valuationOf q 1535 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1248 (q : Snake 81) (h : Conditions q) : valuation q 1535 = false ∨ valuation q 1683 = false ∨ valuation q 1708 = true := counterClause1248 (baseVal q)

theorem block38 (q : Snake 81) (h : Conditions q) : B112E110.Block38 (valuation q) :=
  ⟨clause1217 q h, clause1218 q h, clause1219 q h, clause1220 q h, clause1221 q h, clause1222 q h, clause1223 q h, clause1224 q h, clause1225 q h, clause1226 q h, clause1227 q h, clause1228 q h, clause1229 q h, clause1230 q h, clause1231 q h, clause1232 q h, clause1233 q h, clause1234 q h, clause1235 q h, clause1236 q h, clause1237 q h, clause1238 q h, clause1239 q h, clause1240 q h, clause1241 q h, clause1242 q h, clause1243 q h, clause1244 q h, clause1245 q h, clause1246 q h, clause1247 q h, clause1248 q h⟩

end
end Snake9.Regrowth.E112110
