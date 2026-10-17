import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec60 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1921 (q : Nat → Bool) : valuationOf q 1702 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1785 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1702)) (literal (valuationOf q) (1760)) (literal (valuationOf q) (1785)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 9 4 (meaning1702 q) (meaning1760 q) (meaning1785 q) hs
  change valuationOf q 1702 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1785 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1921 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1760 = false ∨ valuation q 1785 = true := counterClause1921 (baseVal q)

theorem counterClause1922 (q : Nat → Bool) : valuationOf q 1702 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1786 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1702)) (literal (valuationOf q) (1761)) (literal (valuationOf q) (1786)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 9 5 (meaning1702 q) (meaning1761 q) (meaning1786 q) hs
  change valuationOf q 1702 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1786 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1922 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1761 = false ∨ valuation q 1786 = true := counterClause1922 (baseVal q)

theorem counterClause1923 (q : Nat → Bool) : valuationOf q 1702 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1787 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1702)) (literal (valuationOf q) (1762)) (literal (valuationOf q) (1787)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 9 6 (meaning1702 q) (meaning1762 q) (meaning1787 q) hs
  change valuationOf q 1702 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1923 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1762 = false ∨ valuation q 1787 = true := counterClause1923 (baseVal q)

theorem counterClause1924 (q : Nat → Bool) : valuationOf q 1702 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1788 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1702)) (literal (valuationOf q) (1763)) (literal (valuationOf q) (1788)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 9 7 (meaning1702 q) (meaning1763 q) (meaning1788 q) hs
  change valuationOf q 1702 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1788 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1924 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1763 = false ∨ valuation q 1788 = true := counterClause1924 (baseVal q)

theorem counterClause1925 (q : Nat → Bool) : valuationOf q 1703 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1783 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1703)) (literal (valuationOf q) (1757)) (literal (valuationOf q) (1783)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 10 1 (meaning1703 q) (meaning1757 q) (meaning1783 q) hs
  change valuationOf q 1703 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1925 (q : Snake 81) (h : Conditions q) : valuation q 1703 = false ∨ valuation q 1757 = false ∨ valuation q 1783 = true := counterClause1925 (baseVal q)

theorem counterClause1926 (q : Nat → Bool) : valuationOf q 1703 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1784 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1703)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1784)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 10 2 (meaning1703 q) (meaning1758 q) (meaning1784 q) hs
  change valuationOf q 1703 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1926 (q : Snake 81) (h : Conditions q) : valuation q 1703 = false ∨ valuation q 1758 = false ∨ valuation q 1784 = true := counterClause1926 (baseVal q)

theorem counterClause1927 (q : Nat → Bool) : valuationOf q 1703 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1785 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1703)) (literal (valuationOf q) (1759)) (literal (valuationOf q) (1785)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 10 3 (meaning1703 q) (meaning1759 q) (meaning1785 q) hs
  change valuationOf q 1703 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1785 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1927 (q : Snake 81) (h : Conditions q) : valuation q 1703 = false ∨ valuation q 1759 = false ∨ valuation q 1785 = true := counterClause1927 (baseVal q)

theorem counterClause1928 (q : Nat → Bool) : valuationOf q 1703 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1786 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1703)) (literal (valuationOf q) (1760)) (literal (valuationOf q) (1786)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 10 4 (meaning1703 q) (meaning1760 q) (meaning1786 q) hs
  change valuationOf q 1703 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1786 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1928 (q : Snake 81) (h : Conditions q) : valuation q 1703 = false ∨ valuation q 1760 = false ∨ valuation q 1786 = true := counterClause1928 (baseVal q)

theorem counterClause1929 (q : Nat → Bool) : valuationOf q 1703 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1787 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1703)) (literal (valuationOf q) (1761)) (literal (valuationOf q) (1787)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 10 5 (meaning1703 q) (meaning1761 q) (meaning1787 q) hs
  change valuationOf q 1703 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1929 (q : Snake 81) (h : Conditions q) : valuation q 1703 = false ∨ valuation q 1761 = false ∨ valuation q 1787 = true := counterClause1929 (baseVal q)

theorem counterClause1930 (q : Nat → Bool) : valuationOf q 1703 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1788 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1703)) (literal (valuationOf q) (1762)) (literal (valuationOf q) (1788)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 10 6 (meaning1703 q) (meaning1762 q) (meaning1788 q) hs
  change valuationOf q 1703 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1788 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1930 (q : Snake 81) (h : Conditions q) : valuation q 1703 = false ∨ valuation q 1762 = false ∨ valuation q 1788 = true := counterClause1930 (baseVal q)

theorem counterClause1931 (q : Nat → Bool) : valuationOf q 1704 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1784 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1704)) (literal (valuationOf q) (1757)) (literal (valuationOf q) (1784)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 11 1 (meaning1704 q) (meaning1757 q) (meaning1784 q) hs
  change valuationOf q 1704 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1931 (q : Snake 81) (h : Conditions q) : valuation q 1704 = false ∨ valuation q 1757 = false ∨ valuation q 1784 = true := counterClause1931 (baseVal q)

theorem counterClause1932 (q : Nat → Bool) : valuationOf q 1704 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1785 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1704)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1785)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 11 2 (meaning1704 q) (meaning1758 q) (meaning1785 q) hs
  change valuationOf q 1704 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1785 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1932 (q : Snake 81) (h : Conditions q) : valuation q 1704 = false ∨ valuation q 1758 = false ∨ valuation q 1785 = true := counterClause1932 (baseVal q)

theorem counterClause1933 (q : Nat → Bool) : valuationOf q 1704 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1786 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1704)) (literal (valuationOf q) (1759)) (literal (valuationOf q) (1786)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 11 3 (meaning1704 q) (meaning1759 q) (meaning1786 q) hs
  change valuationOf q 1704 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1786 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1933 (q : Snake 81) (h : Conditions q) : valuation q 1704 = false ∨ valuation q 1759 = false ∨ valuation q 1786 = true := counterClause1933 (baseVal q)

theorem counterClause1934 (q : Nat → Bool) : valuationOf q 1704 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1787 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1704)) (literal (valuationOf q) (1760)) (literal (valuationOf q) (1787)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 11 4 (meaning1704 q) (meaning1760 q) (meaning1787 q) hs
  change valuationOf q 1704 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1934 (q : Snake 81) (h : Conditions q) : valuation q 1704 = false ∨ valuation q 1760 = false ∨ valuation q 1787 = true := counterClause1934 (baseVal q)

theorem counterClause1935 (q : Nat → Bool) : valuationOf q 1704 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1788 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1704)) (literal (valuationOf q) (1761)) (literal (valuationOf q) (1788)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 11 5 (meaning1704 q) (meaning1761 q) (meaning1788 q) hs
  change valuationOf q 1704 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1788 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1935 (q : Snake 81) (h : Conditions q) : valuation q 1704 = false ∨ valuation q 1761 = false ∨ valuation q 1788 = true := counterClause1935 (baseVal q)

theorem counterClause1936 (q : Nat → Bool) : valuationOf q 1705 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1786 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1705)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1786)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 12 2 (meaning1705 q) (meaning1758 q) (meaning1786 q) hs
  change valuationOf q 1705 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1786 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1936 (q : Snake 81) (h : Conditions q) : valuation q 1705 = false ∨ valuation q 1758 = false ∨ valuation q 1786 = true := counterClause1936 (baseVal q)

theorem counterClause1937 (q : Nat → Bool) : valuationOf q 1705 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1787 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1705)) (literal (valuationOf q) (1759)) (literal (valuationOf q) (1787)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 12 3 (meaning1705 q) (meaning1759 q) (meaning1787 q) hs
  change valuationOf q 1705 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1937 (q : Snake 81) (h : Conditions q) : valuation q 1705 = false ∨ valuation q 1759 = false ∨ valuation q 1787 = true := counterClause1937 (baseVal q)

theorem counterClause1938 (q : Nat → Bool) : valuationOf q 1705 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1788 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1705)) (literal (valuationOf q) (1760)) (literal (valuationOf q) (1788)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 12 4 (meaning1705 q) (meaning1760 q) (meaning1788 q) hs
  change valuationOf q 1705 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1788 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1938 (q : Snake 81) (h : Conditions q) : valuation q 1705 = false ∨ valuation q 1760 = false ∨ valuation q 1788 = true := counterClause1938 (baseVal q)

theorem counterClause1939 (q : Nat → Bool) : valuationOf q 1706 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1787 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1706)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1787)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 13 2 (meaning1706 q) (meaning1758 q) (meaning1787 q) hs
  change valuationOf q 1706 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1939 (q : Snake 81) (h : Conditions q) : valuation q 1706 = false ∨ valuation q 1758 = false ∨ valuation q 1787 = true := counterClause1939 (baseVal q)

theorem counterClause1940 (q : Nat → Bool) : valuationOf q 1706 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1788 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1706)) (literal (valuationOf q) (1759)) (literal (valuationOf q) (1788)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 13 3 (meaning1706 q) (meaning1759 q) (meaning1788 q) hs
  change valuationOf q 1706 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1788 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1940 (q : Snake 81) (h : Conditions q) : valuation q 1706 = false ∨ valuation q 1759 = false ∨ valuation q 1788 = true := counterClause1940 (baseVal q)

theorem counterClause1941 (q : Nat → Bool) : valuationOf q 1707 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1788 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1707)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1788)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 14 2 (meaning1707 q) (meaning1758 q) (meaning1788 q) hs
  change valuationOf q 1707 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1788 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1941 (q : Snake 81) (h : Conditions q) : valuation q 1707 = false ∨ valuation q 1758 = false ∨ valuation q 1788 = true := counterClause1941 (baseVal q)

theorem counterClause1942 (q : Nat → Bool) : valuationOf q 1633 = false ∨ valuationOf q 1788 = false ∨ valuationOf q 1816 = true := by
  have hs : count1795 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29, -31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) + (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91, -94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29, -31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (l₂ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91, -94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1633)) (literal (valuationOf q) (1788)) (literal (valuationOf q) (1816)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29, -31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91, -94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1795 q) 6 16 (meaning1633 q) (meaning1788 q) (meaning1816 q) hs
  change valuationOf q 1633 = false ∨ valuationOf q 1788 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1942 (q : Snake 81) (h : Conditions q) : valuation q 1633 = false ∨ valuation q 1788 = false ∨ valuation q 1816 = true := counterClause1942 (baseVal q)

theorem counterClause1943 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1787 = false ∨ valuationOf q 1816 = true := by
  have hs : count1795 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29, -31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) + (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91, -94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29, -31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (l₂ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91, -94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1787)) (literal (valuationOf q) (1816)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29, -31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91, -94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1795 q) 7 15 (meaning1634 q) (meaning1787 q) (meaning1816 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1787 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1943 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1787 = false ∨ valuation q 1816 = true := counterClause1943 (baseVal q)

theorem counterClause1944 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1786 = false ∨ valuationOf q 1816 = true := by
  have hs : count1795 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29, -31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) + (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91, -94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29, -31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (l₂ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91, -94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1786)) (literal (valuationOf q) (1816)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29, -31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91, -94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1795 q) 8 14 (meaning1635 q) (meaning1786 q) (meaning1816 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1786 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1944 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1786 = false ∨ valuation q 1816 = true := counterClause1944 (baseVal q)

theorem counterClause1945 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1785 = false ∨ valuationOf q 1816 = true := by
  have hs : count1795 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29, -31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) + (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91, -94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29, -31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (l₂ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91, -94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1785)) (literal (valuationOf q) (1816)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29, -31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91, -94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1795 q) 9 13 (meaning1636 q) (meaning1785 q) (meaning1816 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1785 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1945 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1785 = false ∨ valuation q 1816 = true := counterClause1945 (baseVal q)

theorem counterClause1946 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1784 = false ∨ valuationOf q 1816 = true := by
  have hs : count1795 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29, -31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) + (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91, -94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29, -31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (l₂ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91, -94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1784)) (literal (valuationOf q) (1816)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29, -31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91, -94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1795 q) 10 12 (meaning1637 q) (meaning1784 q) (meaning1816 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1784 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1946 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1784 = false ∨ valuation q 1816 = true := counterClause1946 (baseVal q)

theorem counterClause1947 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1783 = false ∨ valuationOf q 1816 = true := by
  have hs : count1795 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29, -31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) + (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91, -94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29, -31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (l₂ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91, -94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1783)) (literal (valuationOf q) (1816)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29, -31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91, -94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1795 q) 11 11 (meaning1638 q) (meaning1783 q) (meaning1816 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1783 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1947 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1783 = false ∨ valuation q 1816 = true := counterClause1947 (baseVal q)

theorem counterClause1948 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1782 = false ∨ valuationOf q 1816 = true := by
  have hs : count1795 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29, -31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) + (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91, -94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29, -31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (l₂ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91, -94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1782)) (literal (valuationOf q) (1816)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29, -31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91, -94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1795 q) 12 10 (meaning1639 q) (meaning1782 q) (meaning1816 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1782 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1948 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1782 = false ∨ valuation q 1816 = true := counterClause1948 (baseVal q)

theorem counterClause1949 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1781 = false ∨ valuationOf q 1816 = true := by
  have hs : count1795 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29, -31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) + (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91, -94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29, -31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (l₂ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91, -94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1781)) (literal (valuationOf q) (1816)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29, -31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91, -94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1795 q) 13 9 (meaning1640 q) (meaning1781 q) (meaning1816 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1781 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1949 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1781 = false ∨ valuation q 1816 = true := counterClause1949 (baseVal q)

theorem counterClause1950 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1780 = false ∨ valuationOf q 1816 = true := by
  have hs : count1795 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29, -31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) + (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91, -94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29, -31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (l₂ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91, -94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1641)) (literal (valuationOf q) (1780)) (literal (valuationOf q) (1816)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29, -31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91, -94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1795 q) 14 8 (meaning1641 q) (meaning1780 q) (meaning1816 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1780 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1950 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1780 = false ∨ valuation q 1816 = true := counterClause1950 (baseVal q)

theorem counterClause1951 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1779 = false ∨ valuationOf q 1816 = true := by
  have hs : count1795 q = (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29, -31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) + (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91, -94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29, -31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (l₂ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91, -94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1642)) (literal (valuationOf q) (1779)) (literal (valuationOf q) (1816)) (countLit q [-2, -5, -8, -9, -10, -11, -13, -14, -15, -18, -22, -24, -25, -27, -29, -31, -32, -34, -39, -41, -42, -44, -45, -46, -47, -50, -51, -54, -56, -57, -61]) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91, -94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1795 q) 15 7 (meaning1642 q) (meaning1779 q) (meaning1816 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1779 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1951 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1779 = false ∨ valuation q 1816 = true := counterClause1951 (baseVal q)

theorem clause1952 (q : Snake 81) (h : Conditions q) : valuation q 1816 = false := by
  rw [value1816]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1795 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem block60 (q : Snake 81) (h : Conditions q) : B112E089.Block60 (valuation q) :=
  ⟨clause1921 q h, clause1922 q h, clause1923 q h, clause1924 q h, clause1925 q h, clause1926 q h, clause1927 q h, clause1928 q h, clause1929 q h, clause1930 q h, clause1931 q h, clause1932 q h, clause1933 q h, clause1934 q h, clause1935 q h, clause1936 q h, clause1937 q h, clause1938 q h, clause1939 q h, clause1940 q h, clause1941 q h, clause1942 q h, clause1943 q h, clause1944 q h, clause1945 q h, clause1946 q h, clause1947 q h, clause1948 q h, clause1949 q h, clause1950 q h, clause1951 q h, clause1952 q h⟩

end
end Snake9.Regrowth.E112089
