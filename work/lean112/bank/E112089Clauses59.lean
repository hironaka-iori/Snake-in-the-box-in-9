import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec59 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1889 (q : Nat → Bool) : valuationOf q 1698 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1781 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1698)) (literal (valuationOf q) (1760)) (literal (valuationOf q) (1781)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 5 4 (meaning1698 q) (meaning1760 q) (meaning1781 q) hs
  change valuationOf q 1698 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1889 (q : Snake 81) (h : Conditions q) : valuation q 1698 = false ∨ valuation q 1760 = false ∨ valuation q 1781 = true := counterClause1889 (baseVal q)

theorem counterClause1890 (q : Nat → Bool) : valuationOf q 1698 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1782 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1698)) (literal (valuationOf q) (1761)) (literal (valuationOf q) (1782)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 5 5 (meaning1698 q) (meaning1761 q) (meaning1782 q) hs
  change valuationOf q 1698 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1782 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1890 (q : Snake 81) (h : Conditions q) : valuation q 1698 = false ∨ valuation q 1761 = false ∨ valuation q 1782 = true := counterClause1890 (baseVal q)

theorem counterClause1891 (q : Nat → Bool) : valuationOf q 1698 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1783 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1698)) (literal (valuationOf q) (1762)) (literal (valuationOf q) (1783)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 5 6 (meaning1698 q) (meaning1762 q) (meaning1783 q) hs
  change valuationOf q 1698 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1891 (q : Snake 81) (h : Conditions q) : valuation q 1698 = false ∨ valuation q 1762 = false ∨ valuation q 1783 = true := counterClause1891 (baseVal q)

theorem counterClause1892 (q : Nat → Bool) : valuationOf q 1698 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1784 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1698)) (literal (valuationOf q) (1763)) (literal (valuationOf q) (1784)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 5 7 (meaning1698 q) (meaning1763 q) (meaning1784 q) hs
  change valuationOf q 1698 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1892 (q : Snake 81) (h : Conditions q) : valuation q 1698 = false ∨ valuation q 1763 = false ∨ valuation q 1784 = true := counterClause1892 (baseVal q)

theorem counterClause1893 (q : Nat → Bool) : valuationOf q 1698 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1785 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1698)) (literal (valuationOf q) (1764)) (literal (valuationOf q) (1785)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 5 8 (meaning1698 q) (meaning1764 q) (meaning1785 q) hs
  change valuationOf q 1698 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1785 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1893 (q : Snake 81) (h : Conditions q) : valuation q 1698 = false ∨ valuation q 1764 = false ∨ valuation q 1785 = true := counterClause1893 (baseVal q)

theorem counterClause1894 (q : Nat → Bool) : valuationOf q 1698 = false ∨ valuationOf q 1765 = false ∨ valuationOf q 1786 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1698)) (literal (valuationOf q) (1765)) (literal (valuationOf q) (1786)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 5 9 (meaning1698 q) (meaning1765 q) (meaning1786 q) hs
  change valuationOf q 1698 = false ∨ valuationOf q 1765 = false ∨ valuationOf q 1786 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1894 (q : Snake 81) (h : Conditions q) : valuation q 1698 = false ∨ valuation q 1765 = false ∨ valuation q 1786 = true := counterClause1894 (baseVal q)

theorem counterClause1895 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1780 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1780)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 6 2 (meaning1699 q) (meaning1758 q) (meaning1780 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1895 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1758 = false ∨ valuation q 1780 = true := counterClause1895 (baseVal q)

theorem counterClause1896 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1781 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1759)) (literal (valuationOf q) (1781)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 6 3 (meaning1699 q) (meaning1759 q) (meaning1781 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1896 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1759 = false ∨ valuation q 1781 = true := counterClause1896 (baseVal q)

theorem counterClause1897 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1782 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1760)) (literal (valuationOf q) (1782)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 6 4 (meaning1699 q) (meaning1760 q) (meaning1782 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1782 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1897 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1760 = false ∨ valuation q 1782 = true := counterClause1897 (baseVal q)

theorem counterClause1898 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1783 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1761)) (literal (valuationOf q) (1783)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 6 5 (meaning1699 q) (meaning1761 q) (meaning1783 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1898 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1761 = false ∨ valuation q 1783 = true := counterClause1898 (baseVal q)

theorem counterClause1899 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1784 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1762)) (literal (valuationOf q) (1784)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 6 6 (meaning1699 q) (meaning1762 q) (meaning1784 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1899 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1762 = false ∨ valuation q 1784 = true := counterClause1899 (baseVal q)

theorem counterClause1900 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1785 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1763)) (literal (valuationOf q) (1785)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 6 7 (meaning1699 q) (meaning1763 q) (meaning1785 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1785 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1900 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1763 = false ∨ valuation q 1785 = true := counterClause1900 (baseVal q)

theorem counterClause1901 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1786 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1764)) (literal (valuationOf q) (1786)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 6 8 (meaning1699 q) (meaning1764 q) (meaning1786 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1786 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1901 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1764 = false ∨ valuation q 1786 = true := counterClause1901 (baseVal q)

theorem counterClause1902 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1765 = false ∨ valuationOf q 1787 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1765)) (literal (valuationOf q) (1787)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 6 9 (meaning1699 q) (meaning1765 q) (meaning1787 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1765 = false ∨ valuationOf q 1787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1902 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1765 = false ∨ valuation q 1787 = true := counterClause1902 (baseVal q)

theorem counterClause1903 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1781 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1700)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1781)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 7 2 (meaning1700 q) (meaning1758 q) (meaning1781 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1903 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1758 = false ∨ valuation q 1781 = true := counterClause1903 (baseVal q)

theorem counterClause1904 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1782 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1700)) (literal (valuationOf q) (1759)) (literal (valuationOf q) (1782)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 7 3 (meaning1700 q) (meaning1759 q) (meaning1782 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1782 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1904 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1759 = false ∨ valuation q 1782 = true := counterClause1904 (baseVal q)

theorem counterClause1905 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1783 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1700)) (literal (valuationOf q) (1760)) (literal (valuationOf q) (1783)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 7 4 (meaning1700 q) (meaning1760 q) (meaning1783 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1905 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1760 = false ∨ valuation q 1783 = true := counterClause1905 (baseVal q)

theorem counterClause1906 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1784 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1700)) (literal (valuationOf q) (1761)) (literal (valuationOf q) (1784)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 7 5 (meaning1700 q) (meaning1761 q) (meaning1784 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1906 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1761 = false ∨ valuation q 1784 = true := counterClause1906 (baseVal q)

theorem counterClause1907 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1785 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1700)) (literal (valuationOf q) (1762)) (literal (valuationOf q) (1785)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 7 6 (meaning1700 q) (meaning1762 q) (meaning1785 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1785 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1907 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1762 = false ∨ valuation q 1785 = true := counterClause1907 (baseVal q)

theorem counterClause1908 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1786 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1700)) (literal (valuationOf q) (1763)) (literal (valuationOf q) (1786)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 7 7 (meaning1700 q) (meaning1763 q) (meaning1786 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1786 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1908 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1763 = false ∨ valuation q 1786 = true := counterClause1908 (baseVal q)

theorem counterClause1909 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1787 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1700)) (literal (valuationOf q) (1764)) (literal (valuationOf q) (1787)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 7 8 (meaning1700 q) (meaning1764 q) (meaning1787 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1909 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1764 = false ∨ valuation q 1787 = true := counterClause1909 (baseVal q)

theorem counterClause1910 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1781 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1701)) (literal (valuationOf q) (1757)) (literal (valuationOf q) (1781)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 8 1 (meaning1701 q) (meaning1757 q) (meaning1781 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1910 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1757 = false ∨ valuation q 1781 = true := counterClause1910 (baseVal q)

theorem counterClause1911 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1782 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1701)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1782)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 8 2 (meaning1701 q) (meaning1758 q) (meaning1782 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1782 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1911 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1758 = false ∨ valuation q 1782 = true := counterClause1911 (baseVal q)

theorem counterClause1912 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1783 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1701)) (literal (valuationOf q) (1759)) (literal (valuationOf q) (1783)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 8 3 (meaning1701 q) (meaning1759 q) (meaning1783 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1912 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1759 = false ∨ valuation q 1783 = true := counterClause1912 (baseVal q)

theorem counterClause1913 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1784 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1701)) (literal (valuationOf q) (1760)) (literal (valuationOf q) (1784)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 8 4 (meaning1701 q) (meaning1760 q) (meaning1784 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1913 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1760 = false ∨ valuation q 1784 = true := counterClause1913 (baseVal q)

theorem counterClause1914 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1785 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1701)) (literal (valuationOf q) (1761)) (literal (valuationOf q) (1785)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 8 5 (meaning1701 q) (meaning1761 q) (meaning1785 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1785 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1914 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1761 = false ∨ valuation q 1785 = true := counterClause1914 (baseVal q)

theorem counterClause1915 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1786 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1701)) (literal (valuationOf q) (1762)) (literal (valuationOf q) (1786)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 8 6 (meaning1701 q) (meaning1762 q) (meaning1786 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1786 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1915 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1762 = false ∨ valuation q 1786 = true := counterClause1915 (baseVal q)

theorem counterClause1916 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1787 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1701)) (literal (valuationOf q) (1763)) (literal (valuationOf q) (1787)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 8 7 (meaning1701 q) (meaning1763 q) (meaning1787 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1916 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1763 = false ∨ valuation q 1787 = true := counterClause1916 (baseVal q)

theorem counterClause1917 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1788 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1701)) (literal (valuationOf q) (1764)) (literal (valuationOf q) (1788)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 8 8 (meaning1701 q) (meaning1764 q) (meaning1788 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1788 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1917 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1764 = false ∨ valuation q 1788 = true := counterClause1917 (baseVal q)

theorem counterClause1918 (q : Nat → Bool) : valuationOf q 1702 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1782 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1702)) (literal (valuationOf q) (1757)) (literal (valuationOf q) (1782)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 9 1 (meaning1702 q) (meaning1757 q) (meaning1782 q) hs
  change valuationOf q 1702 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1782 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1918 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1757 = false ∨ valuation q 1782 = true := counterClause1918 (baseVal q)

theorem counterClause1919 (q : Nat → Bool) : valuationOf q 1702 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1783 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1702)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1783)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 9 2 (meaning1702 q) (meaning1758 q) (meaning1783 q) hs
  change valuationOf q 1702 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1919 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1758 = false ∨ valuation q 1783 = true := counterClause1919 (baseVal q)

theorem counterClause1920 (q : Nat → Bool) : valuationOf q 1702 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1784 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1702)) (literal (valuationOf q) (1759)) (literal (valuationOf q) (1784)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 9 3 (meaning1702 q) (meaning1759 q) (meaning1784 q) hs
  change valuationOf q 1702 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1920 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1759 = false ∨ valuation q 1784 = true := counterClause1920 (baseVal q)

theorem block59 (q : Snake 81) (h : Conditions q) : B112E089.Block59 (valuation q) :=
  ⟨clause1889 q h, clause1890 q h, clause1891 q h, clause1892 q h, clause1893 q h, clause1894 q h, clause1895 q h, clause1896 q h, clause1897 q h, clause1898 q h, clause1899 q h, clause1900 q h, clause1901 q h, clause1902 q h, clause1903 q h, clause1904 q h, clause1905 q h, clause1906 q h, clause1907 q h, clause1908 q h, clause1909 q h, clause1910 q h, clause1911 q h, clause1912 q h, clause1913 q h, clause1914 q h, clause1915 q h, clause1916 q h, clause1917 q h, clause1918 q h, clause1919 q h, clause1920 q h⟩

end
end Snake9.Regrowth.E112089
