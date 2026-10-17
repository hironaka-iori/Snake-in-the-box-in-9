import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec50 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1601 (q : Nat → Bool) : valuationOf q 1800 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1818 = true := by
  have hs : count1815 q = (countLit q [-112, -113, -117, -118]) + (countLit q [-120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -117, -118]) (l₂ := [-120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1800)) (literal (valuationOf q) (1811)) (literal (valuationOf q) (1818)) (countLit q [-112, -113, -117, -118]) (countLit q [-120, -121, -122, -125, -126]) (count1815 q) 2 2 (meaning1800 q) (meaning1811 q) (meaning1818 q) hs
  change valuationOf q 1800 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1818 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1601 (q : Snake 81) (h : Conditions q) : valuation q 1800 = false ∨ valuation q 1811 = false ∨ valuation q 1818 = true := counterClause1601 (baseVal q)

theorem counterClause1602 (q : Nat → Bool) : valuationOf q 1800 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1819 = true := by
  have hs : count1815 q = (countLit q [-112, -113, -117, -118]) + (countLit q [-120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -117, -118]) (l₂ := [-120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1800)) (literal (valuationOf q) (1812)) (literal (valuationOf q) (1819)) (countLit q [-112, -113, -117, -118]) (countLit q [-120, -121, -122, -125, -126]) (count1815 q) 2 3 (meaning1800 q) (meaning1812 q) (meaning1819 q) hs
  change valuationOf q 1800 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1819 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1602 (q : Snake 81) (h : Conditions q) : valuation q 1800 = false ∨ valuation q 1812 = false ∨ valuation q 1819 = true := counterClause1602 (baseVal q)

theorem counterClause1603 (q : Nat → Bool) : valuationOf q 1800 = false ∨ valuationOf q 1813 = false ∨ valuationOf q 1820 = true := by
  have hs : count1815 q = (countLit q [-112, -113, -117, -118]) + (countLit q [-120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -117, -118]) (l₂ := [-120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1800)) (literal (valuationOf q) (1813)) (literal (valuationOf q) (1820)) (countLit q [-112, -113, -117, -118]) (countLit q [-120, -121, -122, -125, -126]) (count1815 q) 2 4 (meaning1800 q) (meaning1813 q) (meaning1820 q) hs
  change valuationOf q 1800 = false ∨ valuationOf q 1813 = false ∨ valuationOf q 1820 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1603 (q : Snake 81) (h : Conditions q) : valuation q 1800 = false ∨ valuation q 1813 = false ∨ valuation q 1820 = true := counterClause1603 (baseVal q)

theorem counterClause1604 (q : Nat → Bool) : valuationOf q 1800 = false ∨ valuationOf q 1814 = false ∨ valuationOf q 1821 = true := by
  have hs : count1815 q = (countLit q [-112, -113, -117, -118]) + (countLit q [-120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -117, -118]) (l₂ := [-120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1800)) (literal (valuationOf q) (1814)) (literal (valuationOf q) (1821)) (countLit q [-112, -113, -117, -118]) (countLit q [-120, -121, -122, -125, -126]) (count1815 q) 2 5 (meaning1800 q) (meaning1814 q) (meaning1821 q) hs
  change valuationOf q 1800 = false ∨ valuationOf q 1814 = false ∨ valuationOf q 1821 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1604 (q : Snake 81) (h : Conditions q) : valuation q 1800 = false ∨ valuation q 1814 = false ∨ valuation q 1821 = true := counterClause1604 (baseVal q)

theorem counterClause1605 (q : Nat → Bool) : valuationOf q 1801 = false ∨ valuationOf q 1817 = true := by
  have hs : count1815 q = (countLit q [-112, -113, -117, -118]) + (countLit q [-120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -117, -118]) (l₂ := [-120, -121, -122, -125, -126])
  have hm := merge_left (literal (valuationOf q) (1801)) (literal (valuationOf q) (1817)) (countLit q [-112, -113, -117, -118]) (countLit q [-120, -121, -122, -125, -126]) (count1815 q) 3 (meaning1801 q) (meaning1817 q) hs
  change valuationOf q 1801 = false ∨ valuationOf q 1817 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1605 (q : Snake 81) (h : Conditions q) : valuation q 1801 = false ∨ valuation q 1817 = true := counterClause1605 (baseVal q)

theorem counterClause1606 (q : Nat → Bool) : valuationOf q 1801 = false ∨ valuationOf q 1810 = false ∨ valuationOf q 1818 = true := by
  have hs : count1815 q = (countLit q [-112, -113, -117, -118]) + (countLit q [-120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -117, -118]) (l₂ := [-120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1801)) (literal (valuationOf q) (1810)) (literal (valuationOf q) (1818)) (countLit q [-112, -113, -117, -118]) (countLit q [-120, -121, -122, -125, -126]) (count1815 q) 3 1 (meaning1801 q) (meaning1810 q) (meaning1818 q) hs
  change valuationOf q 1801 = false ∨ valuationOf q 1810 = false ∨ valuationOf q 1818 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1606 (q : Snake 81) (h : Conditions q) : valuation q 1801 = false ∨ valuation q 1810 = false ∨ valuation q 1818 = true := counterClause1606 (baseVal q)

theorem counterClause1607 (q : Nat → Bool) : valuationOf q 1801 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1819 = true := by
  have hs : count1815 q = (countLit q [-112, -113, -117, -118]) + (countLit q [-120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -117, -118]) (l₂ := [-120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1801)) (literal (valuationOf q) (1811)) (literal (valuationOf q) (1819)) (countLit q [-112, -113, -117, -118]) (countLit q [-120, -121, -122, -125, -126]) (count1815 q) 3 2 (meaning1801 q) (meaning1811 q) (meaning1819 q) hs
  change valuationOf q 1801 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1819 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1607 (q : Snake 81) (h : Conditions q) : valuation q 1801 = false ∨ valuation q 1811 = false ∨ valuation q 1819 = true := counterClause1607 (baseVal q)

theorem counterClause1608 (q : Nat → Bool) : valuationOf q 1801 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1820 = true := by
  have hs : count1815 q = (countLit q [-112, -113, -117, -118]) + (countLit q [-120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -117, -118]) (l₂ := [-120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1801)) (literal (valuationOf q) (1812)) (literal (valuationOf q) (1820)) (countLit q [-112, -113, -117, -118]) (countLit q [-120, -121, -122, -125, -126]) (count1815 q) 3 3 (meaning1801 q) (meaning1812 q) (meaning1820 q) hs
  change valuationOf q 1801 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1820 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1608 (q : Snake 81) (h : Conditions q) : valuation q 1801 = false ∨ valuation q 1812 = false ∨ valuation q 1820 = true := counterClause1608 (baseVal q)

theorem counterClause1609 (q : Nat → Bool) : valuationOf q 1801 = false ∨ valuationOf q 1813 = false ∨ valuationOf q 1821 = true := by
  have hs : count1815 q = (countLit q [-112, -113, -117, -118]) + (countLit q [-120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -117, -118]) (l₂ := [-120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1801)) (literal (valuationOf q) (1813)) (literal (valuationOf q) (1821)) (countLit q [-112, -113, -117, -118]) (countLit q [-120, -121, -122, -125, -126]) (count1815 q) 3 4 (meaning1801 q) (meaning1813 q) (meaning1821 q) hs
  change valuationOf q 1801 = false ∨ valuationOf q 1813 = false ∨ valuationOf q 1821 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1609 (q : Snake 81) (h : Conditions q) : valuation q 1801 = false ∨ valuation q 1813 = false ∨ valuation q 1821 = true := counterClause1609 (baseVal q)

theorem counterClause1610 (q : Nat → Bool) : valuationOf q 1801 = false ∨ valuationOf q 1814 = false ∨ valuationOf q 1822 = true := by
  have hs : count1815 q = (countLit q [-112, -113, -117, -118]) + (countLit q [-120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -117, -118]) (l₂ := [-120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1801)) (literal (valuationOf q) (1814)) (literal (valuationOf q) (1822)) (countLit q [-112, -113, -117, -118]) (countLit q [-120, -121, -122, -125, -126]) (count1815 q) 3 5 (meaning1801 q) (meaning1814 q) (meaning1822 q) hs
  change valuationOf q 1801 = false ∨ valuationOf q 1814 = false ∨ valuationOf q 1822 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1610 (q : Snake 81) (h : Conditions q) : valuation q 1801 = false ∨ valuation q 1814 = false ∨ valuation q 1822 = true := counterClause1610 (baseVal q)

theorem counterClause1611 (q : Nat → Bool) : valuationOf q 1802 = false ∨ valuationOf q 1818 = true := by
  have hs : count1815 q = (countLit q [-112, -113, -117, -118]) + (countLit q [-120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -117, -118]) (l₂ := [-120, -121, -122, -125, -126])
  have hm := merge_left (literal (valuationOf q) (1802)) (literal (valuationOf q) (1818)) (countLit q [-112, -113, -117, -118]) (countLit q [-120, -121, -122, -125, -126]) (count1815 q) 4 (meaning1802 q) (meaning1818 q) hs
  change valuationOf q 1802 = false ∨ valuationOf q 1818 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1611 (q : Snake 81) (h : Conditions q) : valuation q 1802 = false ∨ valuation q 1818 = true := counterClause1611 (baseVal q)

theorem counterClause1612 (q : Nat → Bool) : valuationOf q 1802 = false ∨ valuationOf q 1810 = false ∨ valuationOf q 1819 = true := by
  have hs : count1815 q = (countLit q [-112, -113, -117, -118]) + (countLit q [-120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -117, -118]) (l₂ := [-120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1802)) (literal (valuationOf q) (1810)) (literal (valuationOf q) (1819)) (countLit q [-112, -113, -117, -118]) (countLit q [-120, -121, -122, -125, -126]) (count1815 q) 4 1 (meaning1802 q) (meaning1810 q) (meaning1819 q) hs
  change valuationOf q 1802 = false ∨ valuationOf q 1810 = false ∨ valuationOf q 1819 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1612 (q : Snake 81) (h : Conditions q) : valuation q 1802 = false ∨ valuation q 1810 = false ∨ valuation q 1819 = true := counterClause1612 (baseVal q)

theorem counterClause1613 (q : Nat → Bool) : valuationOf q 1802 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1820 = true := by
  have hs : count1815 q = (countLit q [-112, -113, -117, -118]) + (countLit q [-120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -117, -118]) (l₂ := [-120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1802)) (literal (valuationOf q) (1811)) (literal (valuationOf q) (1820)) (countLit q [-112, -113, -117, -118]) (countLit q [-120, -121, -122, -125, -126]) (count1815 q) 4 2 (meaning1802 q) (meaning1811 q) (meaning1820 q) hs
  change valuationOf q 1802 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1820 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1613 (q : Snake 81) (h : Conditions q) : valuation q 1802 = false ∨ valuation q 1811 = false ∨ valuation q 1820 = true := counterClause1613 (baseVal q)

theorem counterClause1614 (q : Nat → Bool) : valuationOf q 1802 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1821 = true := by
  have hs : count1815 q = (countLit q [-112, -113, -117, -118]) + (countLit q [-120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -117, -118]) (l₂ := [-120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1802)) (literal (valuationOf q) (1812)) (literal (valuationOf q) (1821)) (countLit q [-112, -113, -117, -118]) (countLit q [-120, -121, -122, -125, -126]) (count1815 q) 4 3 (meaning1802 q) (meaning1812 q) (meaning1821 q) hs
  change valuationOf q 1802 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1821 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1614 (q : Snake 81) (h : Conditions q) : valuation q 1802 = false ∨ valuation q 1812 = false ∨ valuation q 1821 = true := counterClause1614 (baseVal q)

theorem counterClause1615 (q : Nat → Bool) : valuationOf q 1802 = false ∨ valuationOf q 1813 = false ∨ valuationOf q 1822 = true := by
  have hs : count1815 q = (countLit q [-112, -113, -117, -118]) + (countLit q [-120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -117, -118]) (l₂ := [-120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1802)) (literal (valuationOf q) (1813)) (literal (valuationOf q) (1822)) (countLit q [-112, -113, -117, -118]) (countLit q [-120, -121, -122, -125, -126]) (count1815 q) 4 4 (meaning1802 q) (meaning1813 q) (meaning1822 q) hs
  change valuationOf q 1802 = false ∨ valuationOf q 1813 = false ∨ valuationOf q 1822 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1615 (q : Snake 81) (h : Conditions q) : valuation q 1802 = false ∨ valuation q 1813 = false ∨ valuation q 1822 = true := counterClause1615 (baseVal q)

theorem counterClause1616 (q : Nat → Bool) : valuationOf q 1819 = false ∨ valuationOf q 1828 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_right (literal (valuationOf q) (1819)) (literal (valuationOf q) (1828)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 5 (meaning1819 q) (meaning1828 q) hs
  change valuationOf q 1819 = false ∨ valuationOf q 1828 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1616 (q : Snake 81) (h : Conditions q) : valuation q 1819 = false ∨ valuation q 1828 = true := counterClause1616 (baseVal q)

theorem counterClause1617 (q : Nat → Bool) : valuationOf q 1820 = false ∨ valuationOf q 1829 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_right (literal (valuationOf q) (1820)) (literal (valuationOf q) (1829)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 6 (meaning1820 q) (meaning1829 q) hs
  change valuationOf q 1820 = false ∨ valuationOf q 1829 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1617 (q : Snake 81) (h : Conditions q) : valuation q 1820 = false ∨ valuation q 1829 = true := counterClause1617 (baseVal q)

theorem counterClause1618 (q : Nat → Bool) : valuationOf q 1787 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1827 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1787)) (literal (valuationOf q) (1817)) (literal (valuationOf q) (1827)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 1 3 (meaning1787 q) (meaning1817 q) (meaning1827 q) hs
  change valuationOf q 1787 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1827 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1618 (q : Snake 81) (h : Conditions q) : valuation q 1787 = false ∨ valuation q 1817 = false ∨ valuation q 1827 = true := counterClause1618 (baseVal q)

theorem counterClause1619 (q : Nat → Bool) : valuationOf q 1787 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1828 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1787)) (literal (valuationOf q) (1818)) (literal (valuationOf q) (1828)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 1 4 (meaning1787 q) (meaning1818 q) (meaning1828 q) hs
  change valuationOf q 1787 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1828 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1619 (q : Snake 81) (h : Conditions q) : valuation q 1787 = false ∨ valuation q 1818 = false ∨ valuation q 1828 = true := counterClause1619 (baseVal q)

theorem counterClause1620 (q : Nat → Bool) : valuationOf q 1787 = false ∨ valuationOf q 1819 = false ∨ valuationOf q 1829 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1787)) (literal (valuationOf q) (1819)) (literal (valuationOf q) (1829)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 1 5 (meaning1787 q) (meaning1819 q) (meaning1829 q) hs
  change valuationOf q 1787 = false ∨ valuationOf q 1819 = false ∨ valuationOf q 1829 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1620 (q : Snake 81) (h : Conditions q) : valuation q 1787 = false ∨ valuation q 1819 = false ∨ valuation q 1829 = true := counterClause1620 (baseVal q)

theorem counterClause1621 (q : Nat → Bool) : valuationOf q 1787 = false ∨ valuationOf q 1820 = false ∨ valuationOf q 1830 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1787)) (literal (valuationOf q) (1820)) (literal (valuationOf q) (1830)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 1 6 (meaning1787 q) (meaning1820 q) (meaning1830 q) hs
  change valuationOf q 1787 = false ∨ valuationOf q 1820 = false ∨ valuationOf q 1830 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1621 (q : Snake 81) (h : Conditions q) : valuation q 1787 = false ∨ valuation q 1820 = false ∨ valuation q 1830 = true := counterClause1621 (baseVal q)

theorem counterClause1622 (q : Nat → Bool) : valuationOf q 1787 = false ∨ valuationOf q 1821 = false ∨ valuationOf q 1831 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1787)) (literal (valuationOf q) (1821)) (literal (valuationOf q) (1831)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 1 7 (meaning1787 q) (meaning1821 q) (meaning1831 q) hs
  change valuationOf q 1787 = false ∨ valuationOf q 1821 = false ∨ valuationOf q 1831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1622 (q : Snake 81) (h : Conditions q) : valuation q 1787 = false ∨ valuation q 1821 = false ∨ valuation q 1831 = true := counterClause1622 (baseVal q)

theorem counterClause1623 (q : Nat → Bool) : valuationOf q 1788 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1828 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1788)) (literal (valuationOf q) (1817)) (literal (valuationOf q) (1828)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 2 3 (meaning1788 q) (meaning1817 q) (meaning1828 q) hs
  change valuationOf q 1788 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1828 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1623 (q : Snake 81) (h : Conditions q) : valuation q 1788 = false ∨ valuation q 1817 = false ∨ valuation q 1828 = true := counterClause1623 (baseVal q)

theorem counterClause1624 (q : Nat → Bool) : valuationOf q 1788 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1829 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1788)) (literal (valuationOf q) (1818)) (literal (valuationOf q) (1829)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 2 4 (meaning1788 q) (meaning1818 q) (meaning1829 q) hs
  change valuationOf q 1788 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1829 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1624 (q : Snake 81) (h : Conditions q) : valuation q 1788 = false ∨ valuation q 1818 = false ∨ valuation q 1829 = true := counterClause1624 (baseVal q)

theorem counterClause1625 (q : Nat → Bool) : valuationOf q 1788 = false ∨ valuationOf q 1819 = false ∨ valuationOf q 1830 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1788)) (literal (valuationOf q) (1819)) (literal (valuationOf q) (1830)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 2 5 (meaning1788 q) (meaning1819 q) (meaning1830 q) hs
  change valuationOf q 1788 = false ∨ valuationOf q 1819 = false ∨ valuationOf q 1830 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1625 (q : Snake 81) (h : Conditions q) : valuation q 1788 = false ∨ valuation q 1819 = false ∨ valuation q 1830 = true := counterClause1625 (baseVal q)

theorem counterClause1626 (q : Nat → Bool) : valuationOf q 1788 = false ∨ valuationOf q 1820 = false ∨ valuationOf q 1831 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1788)) (literal (valuationOf q) (1820)) (literal (valuationOf q) (1831)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 2 6 (meaning1788 q) (meaning1820 q) (meaning1831 q) hs
  change valuationOf q 1788 = false ∨ valuationOf q 1820 = false ∨ valuationOf q 1831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1626 (q : Snake 81) (h : Conditions q) : valuation q 1788 = false ∨ valuation q 1820 = false ∨ valuation q 1831 = true := counterClause1626 (baseVal q)

theorem counterClause1627 (q : Nat → Bool) : valuationOf q 1788 = false ∨ valuationOf q 1821 = false ∨ valuationOf q 1832 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1788)) (literal (valuationOf q) (1821)) (literal (valuationOf q) (1832)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 2 7 (meaning1788 q) (meaning1821 q) (meaning1832 q) hs
  change valuationOf q 1788 = false ∨ valuationOf q 1821 = false ∨ valuationOf q 1832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1627 (q : Snake 81) (h : Conditions q) : valuation q 1788 = false ∨ valuation q 1821 = false ∨ valuation q 1832 = true := counterClause1627 (baseVal q)

theorem counterClause1628 (q : Nat → Bool) : valuationOf q 1789 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1828 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1789)) (literal (valuationOf q) (1816)) (literal (valuationOf q) (1828)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 3 2 (meaning1789 q) (meaning1816 q) (meaning1828 q) hs
  change valuationOf q 1789 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1828 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1628 (q : Snake 81) (h : Conditions q) : valuation q 1789 = false ∨ valuation q 1816 = false ∨ valuation q 1828 = true := counterClause1628 (baseVal q)

theorem counterClause1629 (q : Nat → Bool) : valuationOf q 1789 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1829 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1789)) (literal (valuationOf q) (1817)) (literal (valuationOf q) (1829)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 3 3 (meaning1789 q) (meaning1817 q) (meaning1829 q) hs
  change valuationOf q 1789 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1829 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1629 (q : Snake 81) (h : Conditions q) : valuation q 1789 = false ∨ valuation q 1817 = false ∨ valuation q 1829 = true := counterClause1629 (baseVal q)

theorem counterClause1630 (q : Nat → Bool) : valuationOf q 1789 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1830 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1789)) (literal (valuationOf q) (1818)) (literal (valuationOf q) (1830)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 3 4 (meaning1789 q) (meaning1818 q) (meaning1830 q) hs
  change valuationOf q 1789 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1830 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1630 (q : Snake 81) (h : Conditions q) : valuation q 1789 = false ∨ valuation q 1818 = false ∨ valuation q 1830 = true := counterClause1630 (baseVal q)

theorem counterClause1631 (q : Nat → Bool) : valuationOf q 1789 = false ∨ valuationOf q 1819 = false ∨ valuationOf q 1831 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1789)) (literal (valuationOf q) (1819)) (literal (valuationOf q) (1831)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 3 5 (meaning1789 q) (meaning1819 q) (meaning1831 q) hs
  change valuationOf q 1789 = false ∨ valuationOf q 1819 = false ∨ valuationOf q 1831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1631 (q : Snake 81) (h : Conditions q) : valuation q 1789 = false ∨ valuation q 1819 = false ∨ valuation q 1831 = true := counterClause1631 (baseVal q)

theorem counterClause1632 (q : Nat → Bool) : valuationOf q 1789 = false ∨ valuationOf q 1820 = false ∨ valuationOf q 1832 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1789)) (literal (valuationOf q) (1820)) (literal (valuationOf q) (1832)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 3 6 (meaning1789 q) (meaning1820 q) (meaning1832 q) hs
  change valuationOf q 1789 = false ∨ valuationOf q 1820 = false ∨ valuationOf q 1832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1632 (q : Snake 81) (h : Conditions q) : valuation q 1789 = false ∨ valuation q 1820 = false ∨ valuation q 1832 = true := counterClause1632 (baseVal q)

theorem block50 (q : Snake 81) (h : Conditions q) : B112E034.Block50 (valuation q) :=
  ⟨clause1601 q h, clause1602 q h, clause1603 q h, clause1604 q h, clause1605 q h, clause1606 q h, clause1607 q h, clause1608 q h, clause1609 q h, clause1610 q h, clause1611 q h, clause1612 q h, clause1613 q h, clause1614 q h, clause1615 q h, clause1616 q h, clause1617 q h, clause1618 q h, clause1619 q h, clause1620 q h, clause1621 q h, clause1622 q h, clause1623 q h, clause1624 q h, clause1625 q h, clause1626 q h, clause1627 q h, clause1628 q h, clause1629 q h, clause1630 q h, clause1631 q h, clause1632 q h⟩

end
end Snake9.Regrowth.E112034
