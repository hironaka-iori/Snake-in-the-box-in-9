import E112096Semantics
import B112E096Inputs
namespace Snake9.Regrowth.E112096
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1679 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) + (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (l₂ := [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1679)) (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) (count1669 q) 2 9 (meaning1596 q) (meaning1662 q) (meaning1679 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1662 = false ∨ valuation q 1679 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1680 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) + (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (l₂ := [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1680)) (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) (count1669 q) 2 10 (meaning1596 q) (meaning1663 q) (meaning1680 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1663 = false ∨ valuation q 1680 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1677 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) + (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (l₂ := [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1677)) (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) (count1669 q) 3 6 (meaning1597 q) (meaning1659 q) (meaning1677 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1659 = false ∨ valuation q 1677 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1678 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) + (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (l₂ := [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1678)) (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) (count1669 q) 3 7 (meaning1597 q) (meaning1660 q) (meaning1678 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1660 = false ∨ valuation q 1678 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1679 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) + (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (l₂ := [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1679)) (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) (count1669 q) 3 8 (meaning1597 q) (meaning1661 q) (meaning1679 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1661 = false ∨ valuation q 1679 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1680 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) + (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (l₂ := [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1680)) (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) (count1669 q) 3 9 (meaning1597 q) (meaning1662 q) (meaning1680 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1662 = false ∨ valuation q 1680 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1681 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) + (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (l₂ := [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1681)) (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) (count1669 q) 3 10 (meaning1597 q) (meaning1663 q) (meaning1681 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1663 = false ∨ valuation q 1681 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1678 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) + (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (l₂ := [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1678)) (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) (count1669 q) 4 6 (meaning1598 q) (meaning1659 q) (meaning1678 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1659 = false ∨ valuation q 1678 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1679 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) + (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (l₂ := [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1679)) (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) (count1669 q) 4 7 (meaning1598 q) (meaning1660 q) (meaning1679 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1660 = false ∨ valuation q 1679 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1680 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) + (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (l₂ := [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1680)) (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) (count1669 q) 4 8 (meaning1598 q) (meaning1661 q) (meaning1680 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1661 = false ∨ valuation q 1680 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1681 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) + (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (l₂ := [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1681)) (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) (count1669 q) 4 9 (meaning1598 q) (meaning1662 q) (meaning1681 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1662 = false ∨ valuation q 1681 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1682 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) + (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (l₂ := [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1682)) (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) (count1669 q) 4 10 (meaning1598 q) (meaning1663 q) (meaning1682 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1663 = false ∨ valuation q 1682 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1678 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) + (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (l₂ := [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1678)) (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) (count1669 q) 5 5 (meaning1599 q) (meaning1658 q) (meaning1678 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1658 = false ∨ valuation q 1678 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1679 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) + (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (l₂ := [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1679)) (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) (count1669 q) 5 6 (meaning1599 q) (meaning1659 q) (meaning1679 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1659 = false ∨ valuation q 1679 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1680 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) + (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (l₂ := [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1680)) (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) (count1669 q) 5 7 (meaning1599 q) (meaning1660 q) (meaning1680 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1660 = false ∨ valuation q 1680 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1681 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) + (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (l₂ := [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1681)) (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) (count1669 q) 5 8 (meaning1599 q) (meaning1661 q) (meaning1681 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1661 = false ∨ valuation q 1681 = true := counterClause976 (baseVal q)

theorem counterClause977 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1682 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) + (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (l₂ := [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1682)) (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) (count1669 q) 5 9 (meaning1599 q) (meaning1662 q) (meaning1682 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1662 = false ∨ valuation q 1682 = true := counterClause977 (baseVal q)

theorem counterClause978 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1679 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) + (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (l₂ := [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1679)) (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) (count1669 q) 6 5 (meaning1600 q) (meaning1658 q) (meaning1679 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1658 = false ∨ valuation q 1679 = true := counterClause978 (baseVal q)

theorem counterClause979 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1680 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) + (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (l₂ := [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1680)) (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) (count1669 q) 6 6 (meaning1600 q) (meaning1659 q) (meaning1680 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1659 = false ∨ valuation q 1680 = true := counterClause979 (baseVal q)

theorem counterClause980 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1681 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) + (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (l₂ := [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1681)) (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) (count1669 q) 6 7 (meaning1600 q) (meaning1660 q) (meaning1681 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1660 = false ∨ valuation q 1681 = true := counterClause980 (baseVal q)

theorem counterClause981 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1682 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) + (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (l₂ := [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1682)) (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) (count1669 q) 6 8 (meaning1600 q) (meaning1661 q) (meaning1682 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1661 = false ∨ valuation q 1682 = true := counterClause981 (baseVal q)

theorem counterClause982 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1679 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) + (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (l₂ := [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1679)) (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) (count1669 q) 7 4 (meaning1601 q) (meaning1657 q) (meaning1679 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1657 = false ∨ valuation q 1679 = true := counterClause982 (baseVal q)

theorem counterClause983 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1680 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) + (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (l₂ := [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1680)) (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) (count1669 q) 7 5 (meaning1601 q) (meaning1658 q) (meaning1680 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1658 = false ∨ valuation q 1680 = true := counterClause983 (baseVal q)

theorem counterClause984 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1681 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) + (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (l₂ := [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1601)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1681)) (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) (count1669 q) 7 6 (meaning1601 q) (meaning1659 q) (meaning1681 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1659 = false ∨ valuation q 1681 = true := counterClause984 (baseVal q)

theorem counterClause985 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1680 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) + (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (l₂ := [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1602)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1680)) (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) (count1669 q) 8 4 (meaning1602 q) (meaning1657 q) (meaning1680 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1657 = false ∨ valuation q 1680 = true := counterClause985 (baseVal q)

theorem counterClause986 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1681 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) + (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (l₂ := [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1602)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1681)) (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86]) (countLit q [-88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) (count1669 q) 8 5 (meaning1602 q) (meaning1658 q) (meaning1681 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1658 = false ∨ valuation q 1681 = true := counterClause986 (baseVal q)

theorem counterClause987 (q : Nat → Bool) : valuationOf q 1536 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1708 = true := by
  have hs : count1689 q = (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29, -31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) + (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86, -88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29, -31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) (l₂ := [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86, -88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1536)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1708)) (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29, -31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86, -88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) (count1689 q) 6 14 (meaning1536 q) (meaning1682 q) (meaning1708 q) hs
  change valuationOf q 1536 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 1536 = false ∨ valuation q 1682 = false ∨ valuation q 1708 = true := counterClause987 (baseVal q)

theorem counterClause988 (q : Nat → Bool) : valuationOf q 1537 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1708 = true := by
  have hs : count1689 q = (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29, -31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) + (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86, -88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29, -31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) (l₂ := [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86, -88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1537)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1708)) (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29, -31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86, -88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) (count1689 q) 7 13 (meaning1537 q) (meaning1681 q) (meaning1708 q) hs
  change valuationOf q 1537 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 1537 = false ∨ valuation q 1681 = false ∨ valuation q 1708 = true := counterClause988 (baseVal q)

theorem counterClause989 (q : Nat → Bool) : valuationOf q 1538 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1708 = true := by
  have hs : count1689 q = (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29, -31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) + (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86, -88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29, -31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) (l₂ := [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86, -88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1538)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1708)) (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29, -31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86, -88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) (count1689 q) 8 12 (meaning1538 q) (meaning1680 q) (meaning1708 q) hs
  change valuationOf q 1538 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 1538 = false ∨ valuation q 1680 = false ∨ valuation q 1708 = true := counterClause989 (baseVal q)

theorem counterClause990 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1708 = true := by
  have hs : count1689 q = (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29, -31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) + (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86, -88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29, -31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) (l₂ := [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86, -88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1539)) (literal (valuationOf q) (1679)) (literal (valuationOf q) (1708)) (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29, -31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86, -88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) (count1689 q) 9 11 (meaning1539 q) (meaning1679 q) (meaning1708 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1679 = false ∨ valuation q 1708 = true := counterClause990 (baseVal q)

theorem counterClause991 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1678 = false ∨ valuationOf q 1708 = true := by
  have hs : count1689 q = (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29, -31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) + (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86, -88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29, -31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) (l₂ := [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86, -88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1540)) (literal (valuationOf q) (1678)) (literal (valuationOf q) (1708)) (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29, -31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86, -88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) (count1689 q) 10 10 (meaning1540 q) (meaning1678 q) (meaning1708 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1678 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1678 = false ∨ valuation q 1708 = true := counterClause991 (baseVal q)

theorem counterClause992 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1677 = false ∨ valuationOf q 1708 = true := by
  have hs : count1689 q = (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29, -31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) + (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86, -88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29, -31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) (l₂ := [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86, -88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1677)) (literal (valuationOf q) (1708)) (countLit q [-3, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -24, -26, -28, -29, -31, -34, -35, -37, -39, -41, -43, -44, -47, -48, -51, -52, -54, -56, -58]) (countLit q [-60, -61, -62, -63, -66, -69, -70, -72, -73, -77, -78, -80, -81, -85, -86, -88, -90, -92, -93, -96, -99, -102, -104, -107, -109, -111, -113, -114, -116, -117]) (count1689 q) 11 9 (meaning1541 q) (meaning1677 q) (meaning1708 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1677 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1677 = false ∨ valuation q 1708 = true := counterClause992 (baseVal q)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E096.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112096
