import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec56 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1793 (q : Nat → Bool) : valuationOf q 1733 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1768 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1733)) (literal (valuationOf q) (1753)) (literal (valuationOf q) (1768)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 7 3 (meaning1733 q) (meaning1753 q) (meaning1768 q) hs
  change valuationOf q 1733 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1768 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1793 (q : Snake 81) (h : Conditions q) : valuation q 1733 = false ∨ valuation q 1753 = false ∨ valuation q 1768 = true := counterClause1793 (baseVal q)

theorem counterClause1794 (q : Nat → Bool) : valuationOf q 1733 = false ∨ valuationOf q 1754 = false ∨ valuationOf q 1769 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1733)) (literal (valuationOf q) (1754)) (literal (valuationOf q) (1769)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 7 4 (meaning1733 q) (meaning1754 q) (meaning1769 q) hs
  change valuationOf q 1733 = false ∨ valuationOf q 1754 = false ∨ valuationOf q 1769 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1794 (q : Snake 81) (h : Conditions q) : valuation q 1733 = false ∨ valuation q 1754 = false ∨ valuation q 1769 = true := counterClause1794 (baseVal q)

theorem counterClause1795 (q : Nat → Bool) : valuationOf q 1733 = false ∨ valuationOf q 1755 = false ∨ valuationOf q 1770 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1733)) (literal (valuationOf q) (1755)) (literal (valuationOf q) (1770)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 7 5 (meaning1733 q) (meaning1755 q) (meaning1770 q) hs
  change valuationOf q 1733 = false ∨ valuationOf q 1755 = false ∨ valuationOf q 1770 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1795 (q : Snake 81) (h : Conditions q) : valuation q 1733 = false ∨ valuation q 1755 = false ∨ valuation q 1770 = true := counterClause1795 (baseVal q)

theorem counterClause1796 (q : Nat → Bool) : valuationOf q 1733 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1772 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1733)) (literal (valuationOf q) (1757)) (literal (valuationOf q) (1772)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 7 7 (meaning1733 q) (meaning1757 q) (meaning1772 q) hs
  change valuationOf q 1733 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1772 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1796 (q : Snake 81) (h : Conditions q) : valuation q 1733 = false ∨ valuation q 1757 = false ∨ valuation q 1772 = true := counterClause1796 (baseVal q)

theorem counterClause1797 (q : Nat → Bool) : valuationOf q 1734 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1769 = true := by
  have hs : count1759 q = (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) + (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-95, -98, -99, -101, -102, -105, -106, -107]) (l₂ := [-108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1734)) (literal (valuationOf q) (1753)) (literal (valuationOf q) (1769)) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107]) (countLit q [-108, -110, -113, -115, -116, -117, -122, -123]) (count1759 q) 8 3 (meaning1734 q) (meaning1753 q) (meaning1769 q) hs
  change valuationOf q 1734 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1769 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1797 (q : Snake 81) (h : Conditions q) : valuation q 1734 = false ∨ valuation q 1753 = false ∨ valuation q 1769 = true := counterClause1797 (baseVal q)

theorem counterClause1798 (q : Nat → Bool) : valuationOf q 1768 = false ∨ valuationOf q 1784 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_right (literal (valuationOf q) (1768)) (literal (valuationOf q) (1784)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 10 (meaning1768 q) (meaning1784 q) hs
  change valuationOf q 1768 = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1798 (q : Snake 81) (h : Conditions q) : valuation q 1768 = false ∨ valuation q 1784 = true := counterClause1798 (baseVal q)

theorem counterClause1799 (q : Nat → Bool) : valuationOf q 1770 = false ∨ valuationOf q 1786 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_right (literal (valuationOf q) (1770)) (literal (valuationOf q) (1786)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 12 (meaning1770 q) (meaning1786 q) hs
  change valuationOf q 1770 = false ∨ valuationOf q 1786 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1799 (q : Snake 81) (h : Conditions q) : valuation q 1770 = false ∨ valuation q 1786 = true := counterClause1799 (baseVal q)

theorem counterClause1800 (q : Nat → Bool) : valuationOf q 1771 = false ∨ valuationOf q 1787 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_right (literal (valuationOf q) (1771)) (literal (valuationOf q) (1787)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 13 (meaning1771 q) (meaning1787 q) hs
  change valuationOf q 1771 = false ∨ valuationOf q 1787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1800 (q : Snake 81) (h : Conditions q) : valuation q 1771 = false ∨ valuation q 1787 = true := counterClause1800 (baseVal q)

theorem counterClause1801 (q : Nat → Bool) : valuationOf q 1772 = false ∨ valuationOf q 1788 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_right (literal (valuationOf q) (1772)) (literal (valuationOf q) (1788)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 14 (meaning1772 q) (meaning1788 q) hs
  change valuationOf q 1772 = false ∨ valuationOf q 1788 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1801 (q : Snake 81) (h : Conditions q) : valuation q 1772 = false ∨ valuation q 1788 = true := counterClause1801 (baseVal q)

theorem counterClause1802 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1781 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1696)) (literal (valuationOf q) (1764)) (literal (valuationOf q) (1781)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 1 6 (meaning1696 q) (meaning1764 q) (meaning1781 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1802 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1764 = false ∨ valuation q 1781 = true := counterClause1802 (baseVal q)

theorem counterClause1803 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1765 = false ∨ valuationOf q 1782 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1696)) (literal (valuationOf q) (1765)) (literal (valuationOf q) (1782)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 1 7 (meaning1696 q) (meaning1765 q) (meaning1782 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1765 = false ∨ valuationOf q 1782 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1803 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1765 = false ∨ valuation q 1782 = true := counterClause1803 (baseVal q)

theorem counterClause1804 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1766 = false ∨ valuationOf q 1783 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1696)) (literal (valuationOf q) (1766)) (literal (valuationOf q) (1783)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 1 8 (meaning1696 q) (meaning1766 q) (meaning1783 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1766 = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1804 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1766 = false ∨ valuation q 1783 = true := counterClause1804 (baseVal q)

theorem counterClause1805 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1767 = false ∨ valuationOf q 1784 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1696)) (literal (valuationOf q) (1767)) (literal (valuationOf q) (1784)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 1 9 (meaning1696 q) (meaning1767 q) (meaning1784 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1767 = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1805 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1767 = false ∨ valuation q 1784 = true := counterClause1805 (baseVal q)

theorem counterClause1806 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1768 = false ∨ valuationOf q 1785 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1696)) (literal (valuationOf q) (1768)) (literal (valuationOf q) (1785)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 1 10 (meaning1696 q) (meaning1768 q) (meaning1785 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1768 = false ∨ valuationOf q 1785 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1806 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1768 = false ∨ valuation q 1785 = true := counterClause1806 (baseVal q)

theorem counterClause1807 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1769 = false ∨ valuationOf q 1786 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1696)) (literal (valuationOf q) (1769)) (literal (valuationOf q) (1786)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 1 11 (meaning1696 q) (meaning1769 q) (meaning1786 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1769 = false ∨ valuationOf q 1786 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1807 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1769 = false ∨ valuation q 1786 = true := counterClause1807 (baseVal q)

theorem counterClause1808 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1770 = false ∨ valuationOf q 1787 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1696)) (literal (valuationOf q) (1770)) (literal (valuationOf q) (1787)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 1 12 (meaning1696 q) (meaning1770 q) (meaning1787 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1770 = false ∨ valuationOf q 1787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1808 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1770 = false ∨ valuation q 1787 = true := counterClause1808 (baseVal q)

theorem counterClause1809 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1771 = false ∨ valuationOf q 1788 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1696)) (literal (valuationOf q) (1771)) (literal (valuationOf q) (1788)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 1 13 (meaning1696 q) (meaning1771 q) (meaning1788 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1771 = false ∨ valuationOf q 1788 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1809 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1771 = false ∨ valuation q 1788 = true := counterClause1809 (baseVal q)

theorem counterClause1810 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1781 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1697)) (literal (valuationOf q) (1763)) (literal (valuationOf q) (1781)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 2 5 (meaning1697 q) (meaning1763 q) (meaning1781 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1810 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1763 = false ∨ valuation q 1781 = true := counterClause1810 (baseVal q)

theorem counterClause1811 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1782 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1697)) (literal (valuationOf q) (1764)) (literal (valuationOf q) (1782)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 2 6 (meaning1697 q) (meaning1764 q) (meaning1782 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1782 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1811 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1764 = false ∨ valuation q 1782 = true := counterClause1811 (baseVal q)

theorem counterClause1812 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1765 = false ∨ valuationOf q 1783 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1697)) (literal (valuationOf q) (1765)) (literal (valuationOf q) (1783)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 2 7 (meaning1697 q) (meaning1765 q) (meaning1783 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1765 = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1812 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1765 = false ∨ valuation q 1783 = true := counterClause1812 (baseVal q)

theorem counterClause1813 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1766 = false ∨ valuationOf q 1784 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1697)) (literal (valuationOf q) (1766)) (literal (valuationOf q) (1784)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 2 8 (meaning1697 q) (meaning1766 q) (meaning1784 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1766 = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1813 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1766 = false ∨ valuation q 1784 = true := counterClause1813 (baseVal q)

theorem counterClause1814 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1767 = false ∨ valuationOf q 1785 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1697)) (literal (valuationOf q) (1767)) (literal (valuationOf q) (1785)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 2 9 (meaning1697 q) (meaning1767 q) (meaning1785 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1767 = false ∨ valuationOf q 1785 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1814 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1767 = false ∨ valuation q 1785 = true := counterClause1814 (baseVal q)

theorem counterClause1815 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1768 = false ∨ valuationOf q 1786 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1697)) (literal (valuationOf q) (1768)) (literal (valuationOf q) (1786)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 2 10 (meaning1697 q) (meaning1768 q) (meaning1786 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1768 = false ∨ valuationOf q 1786 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1815 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1768 = false ∨ valuation q 1786 = true := counterClause1815 (baseVal q)

theorem counterClause1816 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1769 = false ∨ valuationOf q 1787 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1697)) (literal (valuationOf q) (1769)) (literal (valuationOf q) (1787)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 2 11 (meaning1697 q) (meaning1769 q) (meaning1787 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1769 = false ∨ valuationOf q 1787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1816 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1769 = false ∨ valuation q 1787 = true := counterClause1816 (baseVal q)

theorem counterClause1817 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1770 = false ∨ valuationOf q 1788 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1697)) (literal (valuationOf q) (1770)) (literal (valuationOf q) (1788)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 2 12 (meaning1697 q) (meaning1770 q) (meaning1788 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1770 = false ∨ valuationOf q 1788 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1817 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1770 = false ∨ valuation q 1788 = true := counterClause1817 (baseVal q)

theorem counterClause1818 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1771 = false ∨ valuationOf q 1789 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1697)) (literal (valuationOf q) (1771)) (literal (valuationOf q) (1789)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 2 13 (meaning1697 q) (meaning1771 q) (meaning1789 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1771 = false ∨ valuationOf q 1789 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1818 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1771 = false ∨ valuation q 1789 = true := counterClause1818 (baseVal q)

theorem counterClause1819 (q : Nat → Bool) : valuationOf q 1698 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1782 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1698)) (literal (valuationOf q) (1763)) (literal (valuationOf q) (1782)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 3 5 (meaning1698 q) (meaning1763 q) (meaning1782 q) hs
  change valuationOf q 1698 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1782 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1819 (q : Snake 81) (h : Conditions q) : valuation q 1698 = false ∨ valuation q 1763 = false ∨ valuation q 1782 = true := counterClause1819 (baseVal q)

theorem counterClause1820 (q : Nat → Bool) : valuationOf q 1698 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1783 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1698)) (literal (valuationOf q) (1764)) (literal (valuationOf q) (1783)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 3 6 (meaning1698 q) (meaning1764 q) (meaning1783 q) hs
  change valuationOf q 1698 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1820 (q : Snake 81) (h : Conditions q) : valuation q 1698 = false ∨ valuation q 1764 = false ∨ valuation q 1783 = true := counterClause1820 (baseVal q)

theorem counterClause1821 (q : Nat → Bool) : valuationOf q 1698 = false ∨ valuationOf q 1765 = false ∨ valuationOf q 1784 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1698)) (literal (valuationOf q) (1765)) (literal (valuationOf q) (1784)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 3 7 (meaning1698 q) (meaning1765 q) (meaning1784 q) hs
  change valuationOf q 1698 = false ∨ valuationOf q 1765 = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1821 (q : Snake 81) (h : Conditions q) : valuation q 1698 = false ∨ valuation q 1765 = false ∨ valuation q 1784 = true := counterClause1821 (baseVal q)

theorem counterClause1822 (q : Nat → Bool) : valuationOf q 1698 = false ∨ valuationOf q 1766 = false ∨ valuationOf q 1785 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1698)) (literal (valuationOf q) (1766)) (literal (valuationOf q) (1785)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 3 8 (meaning1698 q) (meaning1766 q) (meaning1785 q) hs
  change valuationOf q 1698 = false ∨ valuationOf q 1766 = false ∨ valuationOf q 1785 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1822 (q : Snake 81) (h : Conditions q) : valuation q 1698 = false ∨ valuation q 1766 = false ∨ valuation q 1785 = true := counterClause1822 (baseVal q)

theorem counterClause1823 (q : Nat → Bool) : valuationOf q 1698 = false ∨ valuationOf q 1767 = false ∨ valuationOf q 1786 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1698)) (literal (valuationOf q) (1767)) (literal (valuationOf q) (1786)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 3 9 (meaning1698 q) (meaning1767 q) (meaning1786 q) hs
  change valuationOf q 1698 = false ∨ valuationOf q 1767 = false ∨ valuationOf q 1786 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1823 (q : Snake 81) (h : Conditions q) : valuation q 1698 = false ∨ valuation q 1767 = false ∨ valuation q 1786 = true := counterClause1823 (baseVal q)

theorem counterClause1824 (q : Nat → Bool) : valuationOf q 1698 = false ∨ valuationOf q 1768 = false ∨ valuationOf q 1787 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1698)) (literal (valuationOf q) (1768)) (literal (valuationOf q) (1787)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 3 10 (meaning1698 q) (meaning1768 q) (meaning1787 q) hs
  change valuationOf q 1698 = false ∨ valuationOf q 1768 = false ∨ valuationOf q 1787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1824 (q : Snake 81) (h : Conditions q) : valuation q 1698 = false ∨ valuation q 1768 = false ∨ valuation q 1787 = true := counterClause1824 (baseVal q)

theorem block56 (q : Snake 81) (h : Conditions q) : B112E105.Block56 (valuation q) :=
  ⟨clause1793 q h, clause1794 q h, clause1795 q h, clause1796 q h, clause1797 q h, clause1798 q h, clause1799 q h, clause1800 q h, clause1801 q h, clause1802 q h, clause1803 q h, clause1804 q h, clause1805 q h, clause1806 q h, clause1807 q h, clause1808 q h, clause1809 q h, clause1810 q h, clause1811 q h, clause1812 q h, clause1813 q h, clause1814 q h, clause1815 q h, clause1816 q h, clause1817 q h, clause1818 q h, clause1819 q h, clause1820 q h, clause1821 q h, clause1822 q h, clause1823 q h, clause1824 q h⟩

end
end Snake9.Regrowth.E112105
