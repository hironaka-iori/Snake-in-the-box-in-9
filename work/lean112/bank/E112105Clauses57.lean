import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec57 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1825 (q : Nat → Bool) : valuationOf q 1698 = false ∨ valuationOf q 1769 = false ∨ valuationOf q 1788 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1698)) (literal (valuationOf q) (1769)) (literal (valuationOf q) (1788)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 3 11 (meaning1698 q) (meaning1769 q) (meaning1788 q) hs
  change valuationOf q 1698 = false ∨ valuationOf q 1769 = false ∨ valuationOf q 1788 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1825 (q : Snake 81) (h : Conditions q) : valuation q 1698 = false ∨ valuation q 1769 = false ∨ valuation q 1788 = true := counterClause1825 (baseVal q)

theorem counterClause1826 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1782 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1762)) (literal (valuationOf q) (1782)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 4 4 (meaning1699 q) (meaning1762 q) (meaning1782 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1782 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1826 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1762 = false ∨ valuation q 1782 = true := counterClause1826 (baseVal q)

theorem counterClause1827 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1783 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1763)) (literal (valuationOf q) (1783)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 4 5 (meaning1699 q) (meaning1763 q) (meaning1783 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1827 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1763 = false ∨ valuation q 1783 = true := counterClause1827 (baseVal q)

theorem counterClause1828 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1784 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1764)) (literal (valuationOf q) (1784)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 4 6 (meaning1699 q) (meaning1764 q) (meaning1784 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1828 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1764 = false ∨ valuation q 1784 = true := counterClause1828 (baseVal q)

theorem counterClause1829 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1765 = false ∨ valuationOf q 1785 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1765)) (literal (valuationOf q) (1785)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 4 7 (meaning1699 q) (meaning1765 q) (meaning1785 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1765 = false ∨ valuationOf q 1785 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1829 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1765 = false ∨ valuation q 1785 = true := counterClause1829 (baseVal q)

theorem counterClause1830 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1766 = false ∨ valuationOf q 1786 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1766)) (literal (valuationOf q) (1786)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 4 8 (meaning1699 q) (meaning1766 q) (meaning1786 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1766 = false ∨ valuationOf q 1786 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1830 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1766 = false ∨ valuation q 1786 = true := counterClause1830 (baseVal q)

theorem counterClause1831 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1767 = false ∨ valuationOf q 1787 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1767)) (literal (valuationOf q) (1787)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 4 9 (meaning1699 q) (meaning1767 q) (meaning1787 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1767 = false ∨ valuationOf q 1787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1831 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1767 = false ∨ valuation q 1787 = true := counterClause1831 (baseVal q)

theorem counterClause1832 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1768 = false ∨ valuationOf q 1788 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1768)) (literal (valuationOf q) (1788)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 4 10 (meaning1699 q) (meaning1768 q) (meaning1788 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1768 = false ∨ valuationOf q 1788 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1832 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1768 = false ∨ valuation q 1788 = true := counterClause1832 (baseVal q)

theorem counterClause1833 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1784 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1700)) (literal (valuationOf q) (1763)) (literal (valuationOf q) (1784)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 5 5 (meaning1700 q) (meaning1763 q) (meaning1784 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1833 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1763 = false ∨ valuation q 1784 = true := counterClause1833 (baseVal q)

theorem counterClause1834 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1785 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1700)) (literal (valuationOf q) (1764)) (literal (valuationOf q) (1785)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 5 6 (meaning1700 q) (meaning1764 q) (meaning1785 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1785 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1834 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1764 = false ∨ valuation q 1785 = true := counterClause1834 (baseVal q)

theorem counterClause1835 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1765 = false ∨ valuationOf q 1786 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1700)) (literal (valuationOf q) (1765)) (literal (valuationOf q) (1786)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 5 7 (meaning1700 q) (meaning1765 q) (meaning1786 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1765 = false ∨ valuationOf q 1786 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1835 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1765 = false ∨ valuation q 1786 = true := counterClause1835 (baseVal q)

theorem counterClause1836 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1766 = false ∨ valuationOf q 1787 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1700)) (literal (valuationOf q) (1766)) (literal (valuationOf q) (1787)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 5 8 (meaning1700 q) (meaning1766 q) (meaning1787 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1766 = false ∨ valuationOf q 1787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1836 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1766 = false ∨ valuation q 1787 = true := counterClause1836 (baseVal q)

theorem counterClause1837 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1767 = false ∨ valuationOf q 1788 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1700)) (literal (valuationOf q) (1767)) (literal (valuationOf q) (1788)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 5 9 (meaning1700 q) (meaning1767 q) (meaning1788 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1767 = false ∨ valuationOf q 1788 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1837 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1767 = false ∨ valuation q 1788 = true := counterClause1837 (baseVal q)

theorem counterClause1838 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1768 = false ∨ valuationOf q 1789 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1700)) (literal (valuationOf q) (1768)) (literal (valuationOf q) (1789)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 5 10 (meaning1700 q) (meaning1768 q) (meaning1789 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1768 = false ∨ valuationOf q 1789 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1838 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1768 = false ∨ valuation q 1789 = true := counterClause1838 (baseVal q)

theorem counterClause1839 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1784 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1701)) (literal (valuationOf q) (1762)) (literal (valuationOf q) (1784)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 6 4 (meaning1701 q) (meaning1762 q) (meaning1784 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1839 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1762 = false ∨ valuation q 1784 = true := counterClause1839 (baseVal q)

theorem counterClause1840 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1785 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1701)) (literal (valuationOf q) (1763)) (literal (valuationOf q) (1785)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 6 5 (meaning1701 q) (meaning1763 q) (meaning1785 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1785 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1840 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1763 = false ∨ valuation q 1785 = true := counterClause1840 (baseVal q)

theorem counterClause1841 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1786 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1701)) (literal (valuationOf q) (1764)) (literal (valuationOf q) (1786)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 6 6 (meaning1701 q) (meaning1764 q) (meaning1786 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1786 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1841 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1764 = false ∨ valuation q 1786 = true := counterClause1841 (baseVal q)

theorem counterClause1842 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1765 = false ∨ valuationOf q 1787 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1701)) (literal (valuationOf q) (1765)) (literal (valuationOf q) (1787)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 6 7 (meaning1701 q) (meaning1765 q) (meaning1787 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1765 = false ∨ valuationOf q 1787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1842 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1765 = false ∨ valuation q 1787 = true := counterClause1842 (baseVal q)

theorem counterClause1843 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1766 = false ∨ valuationOf q 1788 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1701)) (literal (valuationOf q) (1766)) (literal (valuationOf q) (1788)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 6 8 (meaning1701 q) (meaning1766 q) (meaning1788 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1766 = false ∨ valuationOf q 1788 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1843 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1766 = false ∨ valuation q 1788 = true := counterClause1843 (baseVal q)

theorem counterClause1844 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1767 = false ∨ valuationOf q 1789 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1701)) (literal (valuationOf q) (1767)) (literal (valuationOf q) (1789)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 6 9 (meaning1701 q) (meaning1767 q) (meaning1789 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1767 = false ∨ valuationOf q 1789 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1844 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1767 = false ∨ valuation q 1789 = true := counterClause1844 (baseVal q)

theorem counterClause1845 (q : Nat → Bool) : valuationOf q 1702 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1785 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1702)) (literal (valuationOf q) (1762)) (literal (valuationOf q) (1785)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 7 4 (meaning1702 q) (meaning1762 q) (meaning1785 q) hs
  change valuationOf q 1702 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1785 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1845 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1762 = false ∨ valuation q 1785 = true := counterClause1845 (baseVal q)

theorem counterClause1846 (q : Nat → Bool) : valuationOf q 1702 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1786 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1702)) (literal (valuationOf q) (1763)) (literal (valuationOf q) (1786)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 7 5 (meaning1702 q) (meaning1763 q) (meaning1786 q) hs
  change valuationOf q 1702 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1786 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1846 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1763 = false ∨ valuation q 1786 = true := counterClause1846 (baseVal q)

theorem counterClause1847 (q : Nat → Bool) : valuationOf q 1702 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1787 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1702)) (literal (valuationOf q) (1764)) (literal (valuationOf q) (1787)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 7 6 (meaning1702 q) (meaning1764 q) (meaning1787 q) hs
  change valuationOf q 1702 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1847 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1764 = false ∨ valuation q 1787 = true := counterClause1847 (baseVal q)

theorem counterClause1848 (q : Nat → Bool) : valuationOf q 1702 = false ∨ valuationOf q 1765 = false ∨ valuationOf q 1788 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1702)) (literal (valuationOf q) (1765)) (literal (valuationOf q) (1788)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 7 7 (meaning1702 q) (meaning1765 q) (meaning1788 q) hs
  change valuationOf q 1702 = false ∨ valuationOf q 1765 = false ∨ valuationOf q 1788 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1848 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1765 = false ∨ valuation q 1788 = true := counterClause1848 (baseVal q)

theorem counterClause1849 (q : Nat → Bool) : valuationOf q 1702 = false ∨ valuationOf q 1766 = false ∨ valuationOf q 1789 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1702)) (literal (valuationOf q) (1766)) (literal (valuationOf q) (1789)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 7 8 (meaning1702 q) (meaning1766 q) (meaning1789 q) hs
  change valuationOf q 1702 = false ∨ valuationOf q 1766 = false ∨ valuationOf q 1789 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1849 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1766 = false ∨ valuation q 1789 = true := counterClause1849 (baseVal q)

theorem counterClause1850 (q : Nat → Bool) : valuationOf q 1703 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1786 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1703)) (literal (valuationOf q) (1762)) (literal (valuationOf q) (1786)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 8 4 (meaning1703 q) (meaning1762 q) (meaning1786 q) hs
  change valuationOf q 1703 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1786 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1850 (q : Snake 81) (h : Conditions q) : valuation q 1703 = false ∨ valuation q 1762 = false ∨ valuation q 1786 = true := counterClause1850 (baseVal q)

theorem counterClause1851 (q : Nat → Bool) : valuationOf q 1703 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1787 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1703)) (literal (valuationOf q) (1763)) (literal (valuationOf q) (1787)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 8 5 (meaning1703 q) (meaning1763 q) (meaning1787 q) hs
  change valuationOf q 1703 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1851 (q : Snake 81) (h : Conditions q) : valuation q 1703 = false ∨ valuation q 1763 = false ∨ valuation q 1787 = true := counterClause1851 (baseVal q)

theorem counterClause1852 (q : Nat → Bool) : valuationOf q 1703 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1788 = true := by
  have hs : count1775 q = (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) + (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (l₂ := [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1703)) (literal (valuationOf q) (1764)) (literal (valuationOf q) (1788)) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93]) (countLit q [-95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1775 q) 8 6 (meaning1703 q) (meaning1764 q) (meaning1788 q) hs
  change valuationOf q 1703 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1788 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1852 (q : Snake 81) (h : Conditions q) : valuation q 1703 = false ∨ valuation q 1764 = false ∨ valuation q 1788 = true := counterClause1852 (baseVal q)

theorem counterClause1853 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1789 = false ∨ valuationOf q 1816 = true := by
  have hs : count1796 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31, -33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) + (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93, -95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31, -33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (l₂ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93, -95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1789)) (literal (valuationOf q) (1816)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31, -33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93, -95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1796 q) 6 15 (meaning1636 q) (meaning1789 q) (meaning1816 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1789 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1853 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1789 = false ∨ valuation q 1816 = true := counterClause1853 (baseVal q)

theorem counterClause1854 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1788 = false ∨ valuationOf q 1816 = true := by
  have hs : count1796 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31, -33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) + (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93, -95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31, -33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (l₂ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93, -95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1788)) (literal (valuationOf q) (1816)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31, -33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93, -95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1796 q) 7 14 (meaning1637 q) (meaning1788 q) (meaning1816 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1788 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1854 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1788 = false ∨ valuation q 1816 = true := counterClause1854 (baseVal q)

theorem counterClause1855 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1787 = false ∨ valuationOf q 1816 = true := by
  have hs : count1796 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31, -33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) + (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93, -95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31, -33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (l₂ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93, -95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1787)) (literal (valuationOf q) (1816)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31, -33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93, -95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1796 q) 8 13 (meaning1638 q) (meaning1787 q) (meaning1816 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1787 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1855 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1787 = false ∨ valuation q 1816 = true := counterClause1855 (baseVal q)

theorem counterClause1856 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1786 = false ∨ valuationOf q 1816 = true := by
  have hs : count1796 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31, -33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) + (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93, -95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31, -33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (l₂ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93, -95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1786)) (literal (valuationOf q) (1816)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31, -33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93, -95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1796 q) 9 12 (meaning1639 q) (meaning1786 q) (meaning1816 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1786 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1856 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1786 = false ∨ valuation q 1816 = true := counterClause1856 (baseVal q)

theorem block57 (q : Snake 81) (h : Conditions q) : B112E105.Block57 (valuation q) :=
  ⟨clause1825 q h, clause1826 q h, clause1827 q h, clause1828 q h, clause1829 q h, clause1830 q h, clause1831 q h, clause1832 q h, clause1833 q h, clause1834 q h, clause1835 q h, clause1836 q h, clause1837 q h, clause1838 q h, clause1839 q h, clause1840 q h, clause1841 q h, clause1842 q h, clause1843 q h, clause1844 q h, clause1845 q h, clause1846 q h, clause1847 q h, clause1848 q h, clause1849 q h, clause1850 q h, clause1851 q h, clause1852 q h, clause1853 q h, clause1854 q h, clause1855 q h, clause1856 q h⟩

end
end Snake9.Regrowth.E112105
