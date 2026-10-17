import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec54 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1729 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1716 = false ∨ valuationOf q 1738 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1657)) (literal (valuationOf q) (1716)) (literal (valuationOf q) (1738)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 7 7 (meaning1657 q) (meaning1716 q) (meaning1738 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1716 = false ∨ valuationOf q 1738 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1729 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1716 = false ∨ valuation q 1738 = true := counterClause1729 (baseVal q)

theorem counterClause1730 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1717 = false ∨ valuationOf q 1739 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1657)) (literal (valuationOf q) (1717)) (literal (valuationOf q) (1739)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 7 8 (meaning1657 q) (meaning1717 q) (meaning1739 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1717 = false ∨ valuationOf q 1739 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1730 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1717 = false ∨ valuation q 1739 = true := counterClause1730 (baseVal q)

theorem counterClause1731 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1712 = false ∨ valuationOf q 1735 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1658)) (literal (valuationOf q) (1712)) (literal (valuationOf q) (1735)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 8 3 (meaning1658 q) (meaning1712 q) (meaning1735 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1712 = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1731 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1712 = false ∨ valuation q 1735 = true := counterClause1731 (baseVal q)

theorem counterClause1732 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1713 = false ∨ valuationOf q 1736 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1658)) (literal (valuationOf q) (1713)) (literal (valuationOf q) (1736)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 8 4 (meaning1658 q) (meaning1713 q) (meaning1736 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1713 = false ∨ valuationOf q 1736 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1732 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1713 = false ∨ valuation q 1736 = true := counterClause1732 (baseVal q)

theorem counterClause1733 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1714 = false ∨ valuationOf q 1737 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1658)) (literal (valuationOf q) (1714)) (literal (valuationOf q) (1737)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 8 5 (meaning1658 q) (meaning1714 q) (meaning1737 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1714 = false ∨ valuationOf q 1737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1733 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1714 = false ∨ valuation q 1737 = true := counterClause1733 (baseVal q)

theorem counterClause1734 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1715 = false ∨ valuationOf q 1738 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1658)) (literal (valuationOf q) (1715)) (literal (valuationOf q) (1738)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 8 6 (meaning1658 q) (meaning1715 q) (meaning1738 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1715 = false ∨ valuationOf q 1738 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1734 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1715 = false ∨ valuation q 1738 = true := counterClause1734 (baseVal q)

theorem counterClause1735 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1716 = false ∨ valuationOf q 1739 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1658)) (literal (valuationOf q) (1716)) (literal (valuationOf q) (1739)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 8 7 (meaning1658 q) (meaning1716 q) (meaning1739 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1716 = false ∨ valuationOf q 1739 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1735 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1716 = false ∨ valuation q 1739 = true := counterClause1735 (baseVal q)

theorem counterClause1736 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1712 = false ∨ valuationOf q 1736 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1659)) (literal (valuationOf q) (1712)) (literal (valuationOf q) (1736)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 9 3 (meaning1659 q) (meaning1712 q) (meaning1736 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1712 = false ∨ valuationOf q 1736 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1736 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1712 = false ∨ valuation q 1736 = true := counterClause1736 (baseVal q)

theorem counterClause1737 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1713 = false ∨ valuationOf q 1737 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1659)) (literal (valuationOf q) (1713)) (literal (valuationOf q) (1737)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 9 4 (meaning1659 q) (meaning1713 q) (meaning1737 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1713 = false ∨ valuationOf q 1737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1737 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1713 = false ∨ valuation q 1737 = true := counterClause1737 (baseVal q)

theorem counterClause1738 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1714 = false ∨ valuationOf q 1738 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1659)) (literal (valuationOf q) (1714)) (literal (valuationOf q) (1738)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 9 5 (meaning1659 q) (meaning1714 q) (meaning1738 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1714 = false ∨ valuationOf q 1738 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1738 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1714 = false ∨ valuation q 1738 = true := counterClause1738 (baseVal q)

theorem counterClause1739 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1715 = false ∨ valuationOf q 1739 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1659)) (literal (valuationOf q) (1715)) (literal (valuationOf q) (1739)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 9 6 (meaning1659 q) (meaning1715 q) (meaning1739 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1715 = false ∨ valuationOf q 1739 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1739 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1715 = false ∨ valuation q 1739 = true := counterClause1739 (baseVal q)

theorem counterClause1740 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1713 = false ∨ valuationOf q 1738 = true := by
  have hs : count1725 q = (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) + (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (l₂ := [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1660)) (literal (valuationOf q) (1713)) (literal (valuationOf q) (1738)) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89]) (countLit q [-91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1725 q) 10 4 (meaning1660 q) (meaning1713 q) (meaning1738 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1713 = false ∨ valuationOf q 1738 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1740 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1713 = false ∨ valuation q 1738 = true := counterClause1740 (baseVal q)

theorem counterClause1741 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1739 = false ∨ valuationOf q 1762 = true := by
  have hs : count1744 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31, -33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) + (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89, -91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31, -33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (l₂ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89, -91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1591)) (literal (valuationOf q) (1739)) (literal (valuationOf q) (1762)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31, -33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89, -91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1744 q) 4 15 (meaning1591 q) (meaning1739 q) (meaning1762 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1739 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1741 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1739 = false ∨ valuation q 1762 = true := counterClause1741 (baseVal q)

theorem counterClause1742 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1738 = false ∨ valuationOf q 1762 = true := by
  have hs : count1744 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31, -33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) + (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89, -91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31, -33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (l₂ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89, -91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1592)) (literal (valuationOf q) (1738)) (literal (valuationOf q) (1762)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31, -33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89, -91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1744 q) 5 14 (meaning1592 q) (meaning1738 q) (meaning1762 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1738 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1742 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1738 = false ∨ valuation q 1762 = true := counterClause1742 (baseVal q)

theorem counterClause1743 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1762 = true := by
  have hs : count1744 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31, -33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) + (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89, -91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31, -33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (l₂ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89, -91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1737)) (literal (valuationOf q) (1762)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31, -33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89, -91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1744 q) 6 13 (meaning1593 q) (meaning1737 q) (meaning1762 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1743 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1737 = false ∨ valuation q 1762 = true := counterClause1743 (baseVal q)

theorem counterClause1744 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1762 = true := by
  have hs : count1744 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31, -33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) + (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89, -91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31, -33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (l₂ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89, -91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1736)) (literal (valuationOf q) (1762)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31, -33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89, -91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1744 q) 7 12 (meaning1594 q) (meaning1736 q) (meaning1762 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1744 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1736 = false ∨ valuation q 1762 = true := counterClause1744 (baseVal q)

theorem counterClause1745 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1762 = true := by
  have hs : count1744 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31, -33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) + (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89, -91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31, -33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (l₂ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89, -91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1735)) (literal (valuationOf q) (1762)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31, -33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89, -91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1744 q) 8 11 (meaning1595 q) (meaning1735 q) (meaning1762 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1745 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1735 = false ∨ valuation q 1762 = true := counterClause1745 (baseVal q)

theorem counterClause1746 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1762 = true := by
  have hs : count1744 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31, -33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) + (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89, -91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31, -33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (l₂ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89, -91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1734)) (literal (valuationOf q) (1762)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31, -33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89, -91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1744 q) 9 10 (meaning1596 q) (meaning1734 q) (meaning1762 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1746 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1734 = false ∨ valuation q 1762 = true := counterClause1746 (baseVal q)

theorem counterClause1747 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1762 = true := by
  have hs : count1744 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31, -33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) + (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89, -91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31, -33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (l₂ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89, -91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1733)) (literal (valuationOf q) (1762)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31, -33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89, -91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1744 q) 10 9 (meaning1597 q) (meaning1733 q) (meaning1762 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1747 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1733 = false ∨ valuation q 1762 = true := counterClause1747 (baseVal q)

theorem counterClause1748 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1762 = true := by
  have hs : count1744 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31, -33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) + (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89, -91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31, -33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (l₂ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89, -91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1732)) (literal (valuationOf q) (1762)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31, -33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89, -91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1744 q) 11 8 (meaning1598 q) (meaning1732 q) (meaning1762 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1748 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1732 = false ∨ valuation q 1762 = true := counterClause1748 (baseVal q)

theorem counterClause1749 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1762 = true := by
  have hs : count1744 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31, -33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) + (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89, -91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31, -33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (l₂ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89, -91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1599)) (literal (valuationOf q) (1731)) (literal (valuationOf q) (1762)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31, -33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89, -91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1744 q) 12 7 (meaning1599 q) (meaning1731 q) (meaning1762 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1749 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1731 = false ∨ valuation q 1762 = true := counterClause1749 (baseVal q)

theorem counterClause1750 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1730 = false ∨ valuationOf q 1762 = true := by
  have hs : count1744 q = (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31, -33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) + (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89, -91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31, -33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (l₂ := [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89, -91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1730)) (literal (valuationOf q) (1762)) (countLit q [-2, -5, -7, -9, -11, -14, -16, -18, -19, -21, -24, -26, -28, -31, -33, -35, -36, -38, -41, -43, -44, -46, -48, -51, -52, -54, -55, -58, -61]) (countLit q [-63, -64, -66, -67, -69, -71, -72, -75, -76, -80, -81, -82, -85, -87, -89, -91, -92, -95, -98, -99, -102, -103, -107, -110, -112, -113, -115, -116, -118, -120]) (count1744 q) 13 6 (meaning1600 q) (meaning1730 q) (meaning1762 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1730 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1750 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1730 = false ∨ valuation q 1762 = true := counterClause1750 (baseVal q)

theorem clause1751 (q : Snake 81) (h : Conditions q) : valuation q 1762 = false := by
  rw [value1762]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1744 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1752 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 28 = false ∨ valuation q 58 = false ∨ valuation q 86 = false := by
  rw [value3, value28, value58, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (10 : Vertex) (138 : Vertex) (266 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1753 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 11 = false ∨ valuation q 12 = false := by
  rw [value6, value7, value11, value12]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (66 : Vertex) (67 : Vertex) (74 : Vertex) (75 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1754 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 10 = false ∨ valuation q 12 = false ∨ valuation q 14 = false := by
  rw [value7, value10, value12, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (67 : Vertex) (71 : Vertex) (75 : Vertex) (79 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1755 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 10 = false ∨ valuation q 13 = false ∨ valuation q 14 = false := by
  rw [value9, value10, value13, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (69 : Vertex) (71 : Vertex) (77 : Vertex) (79 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1756 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 46 = false ∨ valuation q 67 = false ∨ valuation q 106 = false := by
  rw [value12, value46, value67, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (75 : Vertex) (203 : Vertex) (331 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1757 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 27 = false ∨ valuation q 29 = false ∨ valuation q 31 = false := by
  rw [value24, value27, value29, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (131 : Vertex) (135 : Vertex) (139 : Vertex) (143 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1758 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 26 = false ∨ valuation q 82 = false ∨ valuation q 83 = false := by
  rw [value25, value26, value82, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (132 : Vertex) (133 : Vertex) (388 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1759 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 27 = false ∨ valuation q 30 = false ∨ valuation q 31 = false := by
  rw [value26, value27, value30, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (133 : Vertex) (135 : Vertex) (141 : Vertex) (143 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1760 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 46 = false ∨ valuation q 87 = false ∨ valuation q 106 = false := by
  rw [value29, value46, value87, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (139 : Vertex) (203 : Vertex) (395 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block54 (q : Snake 81) (h : Conditions q) : B112E019.Block54 (valuation q) :=
  ⟨clause1729 q h, clause1730 q h, clause1731 q h, clause1732 q h, clause1733 q h, clause1734 q h, clause1735 q h, clause1736 q h, clause1737 q h, clause1738 q h, clause1739 q h, clause1740 q h, clause1741 q h, clause1742 q h, clause1743 q h, clause1744 q h, clause1745 q h, clause1746 q h, clause1747 q h, clause1748 q h, clause1749 q h, clause1750 q h, clause1751 q h, clause1752 q h, clause1753 q h, clause1754 q h, clause1755 q h, clause1756 q h, clause1757 q h, clause1758 q h, clause1759 q h, clause1760 q h⟩

end
end Snake9.Regrowth.E112019
