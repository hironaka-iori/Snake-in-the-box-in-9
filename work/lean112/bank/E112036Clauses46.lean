import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec46 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1473 (q : Nat → Bool) : valuationOf q 1810 = false ∨ valuationOf q 1815 = true := by
  have hs : count1815 q = (countLit q [-112, -114, -115, -117]) + (countLit q [-118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -115, -117]) (l₂ := [-118, -122, -124, -125, -126])
  have hm := merge_right (literal (valuationOf q) (1810)) (literal (valuationOf q) (1815)) (countLit q [-112, -114, -115, -117]) (countLit q [-118, -122, -124, -125, -126]) (count1815 q) 1 (meaning1810 q) (meaning1815 q) hs
  change valuationOf q 1810 = false ∨ valuationOf q 1815 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1473 (q : Snake 81) (h : Conditions q) : valuation q 1810 = false ∨ valuation q 1815 = true := counterClause1473 (baseVal q)

theorem counterClause1474 (q : Nat → Bool) : valuationOf q 1811 = false ∨ valuationOf q 1816 = true := by
  have hs : count1815 q = (countLit q [-112, -114, -115, -117]) + (countLit q [-118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -115, -117]) (l₂ := [-118, -122, -124, -125, -126])
  have hm := merge_right (literal (valuationOf q) (1811)) (literal (valuationOf q) (1816)) (countLit q [-112, -114, -115, -117]) (countLit q [-118, -122, -124, -125, -126]) (count1815 q) 2 (meaning1811 q) (meaning1816 q) hs
  change valuationOf q 1811 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1474 (q : Snake 81) (h : Conditions q) : valuation q 1811 = false ∨ valuation q 1816 = true := counterClause1474 (baseVal q)

theorem counterClause1475 (q : Nat → Bool) : valuationOf q 1812 = false ∨ valuationOf q 1817 = true := by
  have hs : count1815 q = (countLit q [-112, -114, -115, -117]) + (countLit q [-118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -115, -117]) (l₂ := [-118, -122, -124, -125, -126])
  have hm := merge_right (literal (valuationOf q) (1812)) (literal (valuationOf q) (1817)) (countLit q [-112, -114, -115, -117]) (countLit q [-118, -122, -124, -125, -126]) (count1815 q) 3 (meaning1812 q) (meaning1817 q) hs
  change valuationOf q 1812 = false ∨ valuationOf q 1817 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1475 (q : Snake 81) (h : Conditions q) : valuation q 1812 = false ∨ valuation q 1817 = true := counterClause1475 (baseVal q)

theorem counterClause1476 (q : Nat → Bool) : valuationOf q 1799 = false ∨ valuationOf q 1815 = true := by
  have hs : count1815 q = (countLit q [-112, -114, -115, -117]) + (countLit q [-118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -115, -117]) (l₂ := [-118, -122, -124, -125, -126])
  have hm := merge_left (literal (valuationOf q) (1799)) (literal (valuationOf q) (1815)) (countLit q [-112, -114, -115, -117]) (countLit q [-118, -122, -124, -125, -126]) (count1815 q) 1 (meaning1799 q) (meaning1815 q) hs
  change valuationOf q 1799 = false ∨ valuationOf q 1815 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1476 (q : Snake 81) (h : Conditions q) : valuation q 1799 = false ∨ valuation q 1815 = true := counterClause1476 (baseVal q)

theorem counterClause1477 (q : Nat → Bool) : valuationOf q 1799 = false ∨ valuationOf q 1810 = false ∨ valuationOf q 1816 = true := by
  have hs : count1815 q = (countLit q [-112, -114, -115, -117]) + (countLit q [-118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -115, -117]) (l₂ := [-118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1799)) (literal (valuationOf q) (1810)) (literal (valuationOf q) (1816)) (countLit q [-112, -114, -115, -117]) (countLit q [-118, -122, -124, -125, -126]) (count1815 q) 1 1 (meaning1799 q) (meaning1810 q) (meaning1816 q) hs
  change valuationOf q 1799 = false ∨ valuationOf q 1810 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1477 (q : Snake 81) (h : Conditions q) : valuation q 1799 = false ∨ valuation q 1810 = false ∨ valuation q 1816 = true := counterClause1477 (baseVal q)

theorem counterClause1478 (q : Nat → Bool) : valuationOf q 1799 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1817 = true := by
  have hs : count1815 q = (countLit q [-112, -114, -115, -117]) + (countLit q [-118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -115, -117]) (l₂ := [-118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1799)) (literal (valuationOf q) (1811)) (literal (valuationOf q) (1817)) (countLit q [-112, -114, -115, -117]) (countLit q [-118, -122, -124, -125, -126]) (count1815 q) 1 2 (meaning1799 q) (meaning1811 q) (meaning1817 q) hs
  change valuationOf q 1799 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1817 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1478 (q : Snake 81) (h : Conditions q) : valuation q 1799 = false ∨ valuation q 1811 = false ∨ valuation q 1817 = true := counterClause1478 (baseVal q)

theorem counterClause1479 (q : Nat → Bool) : valuationOf q 1799 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1818 = true := by
  have hs : count1815 q = (countLit q [-112, -114, -115, -117]) + (countLit q [-118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -115, -117]) (l₂ := [-118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1799)) (literal (valuationOf q) (1812)) (literal (valuationOf q) (1818)) (countLit q [-112, -114, -115, -117]) (countLit q [-118, -122, -124, -125, -126]) (count1815 q) 1 3 (meaning1799 q) (meaning1812 q) (meaning1818 q) hs
  change valuationOf q 1799 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1818 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1479 (q : Snake 81) (h : Conditions q) : valuation q 1799 = false ∨ valuation q 1812 = false ∨ valuation q 1818 = true := counterClause1479 (baseVal q)

theorem counterClause1480 (q : Nat → Bool) : valuationOf q 1799 = false ∨ valuationOf q 1813 = false ∨ valuationOf q 1819 = true := by
  have hs : count1815 q = (countLit q [-112, -114, -115, -117]) + (countLit q [-118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -115, -117]) (l₂ := [-118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1799)) (literal (valuationOf q) (1813)) (literal (valuationOf q) (1819)) (countLit q [-112, -114, -115, -117]) (countLit q [-118, -122, -124, -125, -126]) (count1815 q) 1 4 (meaning1799 q) (meaning1813 q) (meaning1819 q) hs
  change valuationOf q 1799 = false ∨ valuationOf q 1813 = false ∨ valuationOf q 1819 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1480 (q : Snake 81) (h : Conditions q) : valuation q 1799 = false ∨ valuation q 1813 = false ∨ valuation q 1819 = true := counterClause1480 (baseVal q)

theorem counterClause1481 (q : Nat → Bool) : valuationOf q 1800 = false ∨ valuationOf q 1816 = true := by
  have hs : count1815 q = (countLit q [-112, -114, -115, -117]) + (countLit q [-118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -115, -117]) (l₂ := [-118, -122, -124, -125, -126])
  have hm := merge_left (literal (valuationOf q) (1800)) (literal (valuationOf q) (1816)) (countLit q [-112, -114, -115, -117]) (countLit q [-118, -122, -124, -125, -126]) (count1815 q) 2 (meaning1800 q) (meaning1816 q) hs
  change valuationOf q 1800 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1481 (q : Snake 81) (h : Conditions q) : valuation q 1800 = false ∨ valuation q 1816 = true := counterClause1481 (baseVal q)

theorem counterClause1482 (q : Nat → Bool) : valuationOf q 1800 = false ∨ valuationOf q 1810 = false ∨ valuationOf q 1817 = true := by
  have hs : count1815 q = (countLit q [-112, -114, -115, -117]) + (countLit q [-118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -115, -117]) (l₂ := [-118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1800)) (literal (valuationOf q) (1810)) (literal (valuationOf q) (1817)) (countLit q [-112, -114, -115, -117]) (countLit q [-118, -122, -124, -125, -126]) (count1815 q) 2 1 (meaning1800 q) (meaning1810 q) (meaning1817 q) hs
  change valuationOf q 1800 = false ∨ valuationOf q 1810 = false ∨ valuationOf q 1817 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1482 (q : Snake 81) (h : Conditions q) : valuation q 1800 = false ∨ valuation q 1810 = false ∨ valuation q 1817 = true := counterClause1482 (baseVal q)

theorem counterClause1483 (q : Nat → Bool) : valuationOf q 1800 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1818 = true := by
  have hs : count1815 q = (countLit q [-112, -114, -115, -117]) + (countLit q [-118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -115, -117]) (l₂ := [-118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1800)) (literal (valuationOf q) (1811)) (literal (valuationOf q) (1818)) (countLit q [-112, -114, -115, -117]) (countLit q [-118, -122, -124, -125, -126]) (count1815 q) 2 2 (meaning1800 q) (meaning1811 q) (meaning1818 q) hs
  change valuationOf q 1800 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1818 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1483 (q : Snake 81) (h : Conditions q) : valuation q 1800 = false ∨ valuation q 1811 = false ∨ valuation q 1818 = true := counterClause1483 (baseVal q)

theorem counterClause1484 (q : Nat → Bool) : valuationOf q 1800 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1819 = true := by
  have hs : count1815 q = (countLit q [-112, -114, -115, -117]) + (countLit q [-118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -115, -117]) (l₂ := [-118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1800)) (literal (valuationOf q) (1812)) (literal (valuationOf q) (1819)) (countLit q [-112, -114, -115, -117]) (countLit q [-118, -122, -124, -125, -126]) (count1815 q) 2 3 (meaning1800 q) (meaning1812 q) (meaning1819 q) hs
  change valuationOf q 1800 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1819 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1484 (q : Snake 81) (h : Conditions q) : valuation q 1800 = false ∨ valuation q 1812 = false ∨ valuation q 1819 = true := counterClause1484 (baseVal q)

theorem counterClause1485 (q : Nat → Bool) : valuationOf q 1800 = false ∨ valuationOf q 1813 = false ∨ valuationOf q 1820 = true := by
  have hs : count1815 q = (countLit q [-112, -114, -115, -117]) + (countLit q [-118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -115, -117]) (l₂ := [-118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1800)) (literal (valuationOf q) (1813)) (literal (valuationOf q) (1820)) (countLit q [-112, -114, -115, -117]) (countLit q [-118, -122, -124, -125, -126]) (count1815 q) 2 4 (meaning1800 q) (meaning1813 q) (meaning1820 q) hs
  change valuationOf q 1800 = false ∨ valuationOf q 1813 = false ∨ valuationOf q 1820 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1485 (q : Snake 81) (h : Conditions q) : valuation q 1800 = false ∨ valuation q 1813 = false ∨ valuation q 1820 = true := counterClause1485 (baseVal q)

theorem counterClause1486 (q : Nat → Bool) : valuationOf q 1801 = false ∨ valuationOf q 1817 = true := by
  have hs : count1815 q = (countLit q [-112, -114, -115, -117]) + (countLit q [-118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -115, -117]) (l₂ := [-118, -122, -124, -125, -126])
  have hm := merge_left (literal (valuationOf q) (1801)) (literal (valuationOf q) (1817)) (countLit q [-112, -114, -115, -117]) (countLit q [-118, -122, -124, -125, -126]) (count1815 q) 3 (meaning1801 q) (meaning1817 q) hs
  change valuationOf q 1801 = false ∨ valuationOf q 1817 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1486 (q : Snake 81) (h : Conditions q) : valuation q 1801 = false ∨ valuation q 1817 = true := counterClause1486 (baseVal q)

theorem counterClause1487 (q : Nat → Bool) : valuationOf q 1801 = false ∨ valuationOf q 1810 = false ∨ valuationOf q 1818 = true := by
  have hs : count1815 q = (countLit q [-112, -114, -115, -117]) + (countLit q [-118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -115, -117]) (l₂ := [-118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1801)) (literal (valuationOf q) (1810)) (literal (valuationOf q) (1818)) (countLit q [-112, -114, -115, -117]) (countLit q [-118, -122, -124, -125, -126]) (count1815 q) 3 1 (meaning1801 q) (meaning1810 q) (meaning1818 q) hs
  change valuationOf q 1801 = false ∨ valuationOf q 1810 = false ∨ valuationOf q 1818 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1487 (q : Snake 81) (h : Conditions q) : valuation q 1801 = false ∨ valuation q 1810 = false ∨ valuation q 1818 = true := counterClause1487 (baseVal q)

theorem counterClause1488 (q : Nat → Bool) : valuationOf q 1801 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1819 = true := by
  have hs : count1815 q = (countLit q [-112, -114, -115, -117]) + (countLit q [-118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -115, -117]) (l₂ := [-118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1801)) (literal (valuationOf q) (1811)) (literal (valuationOf q) (1819)) (countLit q [-112, -114, -115, -117]) (countLit q [-118, -122, -124, -125, -126]) (count1815 q) 3 2 (meaning1801 q) (meaning1811 q) (meaning1819 q) hs
  change valuationOf q 1801 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1819 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1488 (q : Snake 81) (h : Conditions q) : valuation q 1801 = false ∨ valuation q 1811 = false ∨ valuation q 1819 = true := counterClause1488 (baseVal q)

theorem counterClause1489 (q : Nat → Bool) : valuationOf q 1801 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1820 = true := by
  have hs : count1815 q = (countLit q [-112, -114, -115, -117]) + (countLit q [-118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -115, -117]) (l₂ := [-118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1801)) (literal (valuationOf q) (1812)) (literal (valuationOf q) (1820)) (countLit q [-112, -114, -115, -117]) (countLit q [-118, -122, -124, -125, -126]) (count1815 q) 3 3 (meaning1801 q) (meaning1812 q) (meaning1820 q) hs
  change valuationOf q 1801 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1820 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1489 (q : Snake 81) (h : Conditions q) : valuation q 1801 = false ∨ valuation q 1812 = false ∨ valuation q 1820 = true := counterClause1489 (baseVal q)

theorem counterClause1490 (q : Nat → Bool) : valuationOf q 1802 = false ∨ valuationOf q 1810 = false ∨ valuationOf q 1819 = true := by
  have hs : count1815 q = (countLit q [-112, -114, -115, -117]) + (countLit q [-118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -115, -117]) (l₂ := [-118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1802)) (literal (valuationOf q) (1810)) (literal (valuationOf q) (1819)) (countLit q [-112, -114, -115, -117]) (countLit q [-118, -122, -124, -125, -126]) (count1815 q) 4 1 (meaning1802 q) (meaning1810 q) (meaning1819 q) hs
  change valuationOf q 1802 = false ∨ valuationOf q 1810 = false ∨ valuationOf q 1819 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1490 (q : Snake 81) (h : Conditions q) : valuation q 1802 = false ∨ valuation q 1810 = false ∨ valuation q 1819 = true := counterClause1490 (baseVal q)

theorem counterClause1491 (q : Nat → Bool) : valuationOf q 1802 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1821 = true := by
  have hs : count1815 q = (countLit q [-112, -114, -115, -117]) + (countLit q [-118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-112, -114, -115, -117]) (l₂ := [-118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1802)) (literal (valuationOf q) (1812)) (literal (valuationOf q) (1821)) (countLit q [-112, -114, -115, -117]) (countLit q [-118, -122, -124, -125, -126]) (count1815 q) 4 3 (meaning1802 q) (meaning1812 q) (meaning1821 q) hs
  change valuationOf q 1802 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1821 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1491 (q : Snake 81) (h : Conditions q) : valuation q 1802 = false ∨ valuation q 1812 = false ∨ valuation q 1821 = true := counterClause1491 (baseVal q)

theorem counterClause1492 (q : Nat → Bool) : valuationOf q 1817 = false ∨ valuationOf q 1826 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_right (literal (valuationOf q) (1817)) (literal (valuationOf q) (1826)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 3 (meaning1817 q) (meaning1826 q) hs
  change valuationOf q 1817 = false ∨ valuationOf q 1826 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1492 (q : Snake 81) (h : Conditions q) : valuation q 1817 = false ∨ valuation q 1826 = true := counterClause1492 (baseVal q)

theorem counterClause1493 (q : Nat → Bool) : valuationOf q 1787 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1826 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1787)) (literal (valuationOf q) (1816)) (literal (valuationOf q) (1826)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 1 2 (meaning1787 q) (meaning1816 q) (meaning1826 q) hs
  change valuationOf q 1787 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1826 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1493 (q : Snake 81) (h : Conditions q) : valuation q 1787 = false ∨ valuation q 1816 = false ∨ valuation q 1826 = true := counterClause1493 (baseVal q)

theorem counterClause1494 (q : Nat → Bool) : valuationOf q 1787 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1827 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1787)) (literal (valuationOf q) (1817)) (literal (valuationOf q) (1827)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 1 3 (meaning1787 q) (meaning1817 q) (meaning1827 q) hs
  change valuationOf q 1787 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1827 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1494 (q : Snake 81) (h : Conditions q) : valuation q 1787 = false ∨ valuation q 1817 = false ∨ valuation q 1827 = true := counterClause1494 (baseVal q)

theorem counterClause1495 (q : Nat → Bool) : valuationOf q 1787 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1828 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1787)) (literal (valuationOf q) (1818)) (literal (valuationOf q) (1828)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 1 4 (meaning1787 q) (meaning1818 q) (meaning1828 q) hs
  change valuationOf q 1787 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1828 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1495 (q : Snake 81) (h : Conditions q) : valuation q 1787 = false ∨ valuation q 1818 = false ∨ valuation q 1828 = true := counterClause1495 (baseVal q)

theorem counterClause1496 (q : Nat → Bool) : valuationOf q 1788 = false ∨ valuationOf q 1815 = false ∨ valuationOf q 1826 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1788)) (literal (valuationOf q) (1815)) (literal (valuationOf q) (1826)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 2 1 (meaning1788 q) (meaning1815 q) (meaning1826 q) hs
  change valuationOf q 1788 = false ∨ valuationOf q 1815 = false ∨ valuationOf q 1826 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1496 (q : Snake 81) (h : Conditions q) : valuation q 1788 = false ∨ valuation q 1815 = false ∨ valuation q 1826 = true := counterClause1496 (baseVal q)

theorem counterClause1497 (q : Nat → Bool) : valuationOf q 1788 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1827 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1788)) (literal (valuationOf q) (1816)) (literal (valuationOf q) (1827)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 2 2 (meaning1788 q) (meaning1816 q) (meaning1827 q) hs
  change valuationOf q 1788 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1827 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1497 (q : Snake 81) (h : Conditions q) : valuation q 1788 = false ∨ valuation q 1816 = false ∨ valuation q 1827 = true := counterClause1497 (baseVal q)

theorem counterClause1498 (q : Nat → Bool) : valuationOf q 1788 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1828 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1788)) (literal (valuationOf q) (1817)) (literal (valuationOf q) (1828)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 2 3 (meaning1788 q) (meaning1817 q) (meaning1828 q) hs
  change valuationOf q 1788 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1828 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1498 (q : Snake 81) (h : Conditions q) : valuation q 1788 = false ∨ valuation q 1817 = false ∨ valuation q 1828 = true := counterClause1498 (baseVal q)

theorem counterClause1499 (q : Nat → Bool) : valuationOf q 1788 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1829 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1788)) (literal (valuationOf q) (1818)) (literal (valuationOf q) (1829)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 2 4 (meaning1788 q) (meaning1818 q) (meaning1829 q) hs
  change valuationOf q 1788 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1829 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1499 (q : Snake 81) (h : Conditions q) : valuation q 1788 = false ∨ valuation q 1818 = false ∨ valuation q 1829 = true := counterClause1499 (baseVal q)

theorem counterClause1500 (q : Nat → Bool) : valuationOf q 1788 = false ∨ valuationOf q 1819 = false ∨ valuationOf q 1830 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1788)) (literal (valuationOf q) (1819)) (literal (valuationOf q) (1830)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 2 5 (meaning1788 q) (meaning1819 q) (meaning1830 q) hs
  change valuationOf q 1788 = false ∨ valuationOf q 1819 = false ∨ valuationOf q 1830 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1500 (q : Snake 81) (h : Conditions q) : valuation q 1788 = false ∨ valuation q 1819 = false ∨ valuation q 1830 = true := counterClause1500 (baseVal q)

theorem counterClause1501 (q : Nat → Bool) : valuationOf q 1788 = false ∨ valuationOf q 1820 = false ∨ valuationOf q 1831 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1788)) (literal (valuationOf q) (1820)) (literal (valuationOf q) (1831)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 2 6 (meaning1788 q) (meaning1820 q) (meaning1831 q) hs
  change valuationOf q 1788 = false ∨ valuationOf q 1820 = false ∨ valuationOf q 1831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1501 (q : Snake 81) (h : Conditions q) : valuation q 1788 = false ∨ valuation q 1820 = false ∨ valuation q 1831 = true := counterClause1501 (baseVal q)

theorem counterClause1502 (q : Nat → Bool) : valuationOf q 1788 = false ∨ valuationOf q 1821 = false ∨ valuationOf q 1832 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1788)) (literal (valuationOf q) (1821)) (literal (valuationOf q) (1832)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 2 7 (meaning1788 q) (meaning1821 q) (meaning1832 q) hs
  change valuationOf q 1788 = false ∨ valuationOf q 1821 = false ∨ valuationOf q 1832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1502 (q : Snake 81) (h : Conditions q) : valuation q 1788 = false ∨ valuation q 1821 = false ∨ valuation q 1832 = true := counterClause1502 (baseVal q)

theorem counterClause1503 (q : Nat → Bool) : valuationOf q 1789 = false ∨ valuationOf q 1826 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_left (literal (valuationOf q) (1789)) (literal (valuationOf q) (1826)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 3 (meaning1789 q) (meaning1826 q) hs
  change valuationOf q 1789 = false ∨ valuationOf q 1826 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1503 (q : Snake 81) (h : Conditions q) : valuation q 1789 = false ∨ valuation q 1826 = true := counterClause1503 (baseVal q)

theorem counterClause1504 (q : Nat → Bool) : valuationOf q 1789 = false ∨ valuationOf q 1815 = false ∨ valuationOf q 1827 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1789)) (literal (valuationOf q) (1815)) (literal (valuationOf q) (1827)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 3 1 (meaning1789 q) (meaning1815 q) (meaning1827 q) hs
  change valuationOf q 1789 = false ∨ valuationOf q 1815 = false ∨ valuationOf q 1827 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1504 (q : Snake 81) (h : Conditions q) : valuation q 1789 = false ∨ valuation q 1815 = false ∨ valuation q 1827 = true := counterClause1504 (baseVal q)

theorem block46 (q : Snake 81) (h : Conditions q) : B112E036.Block46 (valuation q) :=
  ⟨clause1473 q h, clause1474 q h, clause1475 q h, clause1476 q h, clause1477 q h, clause1478 q h, clause1479 q h, clause1480 q h, clause1481 q h, clause1482 q h, clause1483 q h, clause1484 q h, clause1485 q h, clause1486 q h, clause1487 q h, clause1488 q h, clause1489 q h, clause1490 q h, clause1491 q h, clause1492 q h, clause1493 q h, clause1494 q h, clause1495 q h, clause1496 q h, clause1497 q h, clause1498 q h, clause1499 q h, clause1500 q h, clause1501 q h, clause1502 q h, clause1503 q h, clause1504 q h⟩

end
end Snake9.Regrowth.E112036
