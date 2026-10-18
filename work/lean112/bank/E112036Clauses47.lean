import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec47 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1505 (q : Nat → Bool) : valuationOf q 1789 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1828 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1789)) (literal (valuationOf q) (1816)) (literal (valuationOf q) (1828)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 3 2 (meaning1789 q) (meaning1816 q) (meaning1828 q) hs
  change valuationOf q 1789 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1828 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1505 (q : Snake 81) (h : Conditions q) : valuation q 1789 = false ∨ valuation q 1816 = false ∨ valuation q 1828 = true := counterClause1505 (baseVal q)

theorem counterClause1506 (q : Nat → Bool) : valuationOf q 1789 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1829 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1789)) (literal (valuationOf q) (1817)) (literal (valuationOf q) (1829)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 3 3 (meaning1789 q) (meaning1817 q) (meaning1829 q) hs
  change valuationOf q 1789 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1829 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1506 (q : Snake 81) (h : Conditions q) : valuation q 1789 = false ∨ valuation q 1817 = false ∨ valuation q 1829 = true := counterClause1506 (baseVal q)

theorem counterClause1507 (q : Nat → Bool) : valuationOf q 1789 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1830 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1789)) (literal (valuationOf q) (1818)) (literal (valuationOf q) (1830)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 3 4 (meaning1789 q) (meaning1818 q) (meaning1830 q) hs
  change valuationOf q 1789 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1830 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1507 (q : Snake 81) (h : Conditions q) : valuation q 1789 = false ∨ valuation q 1818 = false ∨ valuation q 1830 = true := counterClause1507 (baseVal q)

theorem counterClause1508 (q : Nat → Bool) : valuationOf q 1789 = false ∨ valuationOf q 1819 = false ∨ valuationOf q 1831 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1789)) (literal (valuationOf q) (1819)) (literal (valuationOf q) (1831)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 3 5 (meaning1789 q) (meaning1819 q) (meaning1831 q) hs
  change valuationOf q 1789 = false ∨ valuationOf q 1819 = false ∨ valuationOf q 1831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1508 (q : Snake 81) (h : Conditions q) : valuation q 1789 = false ∨ valuation q 1819 = false ∨ valuation q 1831 = true := counterClause1508 (baseVal q)

theorem counterClause1509 (q : Nat → Bool) : valuationOf q 1789 = false ∨ valuationOf q 1820 = false ∨ valuationOf q 1832 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1789)) (literal (valuationOf q) (1820)) (literal (valuationOf q) (1832)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 3 6 (meaning1789 q) (meaning1820 q) (meaning1832 q) hs
  change valuationOf q 1789 = false ∨ valuationOf q 1820 = false ∨ valuationOf q 1832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1509 (q : Snake 81) (h : Conditions q) : valuation q 1789 = false ∨ valuation q 1820 = false ∨ valuation q 1832 = true := counterClause1509 (baseVal q)

theorem counterClause1510 (q : Nat → Bool) : valuationOf q 1790 = false ∨ valuationOf q 1827 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_left (literal (valuationOf q) (1790)) (literal (valuationOf q) (1827)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 4 (meaning1790 q) (meaning1827 q) hs
  change valuationOf q 1790 = false ∨ valuationOf q 1827 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1510 (q : Snake 81) (h : Conditions q) : valuation q 1790 = false ∨ valuation q 1827 = true := counterClause1510 (baseVal q)

theorem counterClause1511 (q : Nat → Bool) : valuationOf q 1790 = false ∨ valuationOf q 1815 = false ∨ valuationOf q 1828 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1790)) (literal (valuationOf q) (1815)) (literal (valuationOf q) (1828)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 4 1 (meaning1790 q) (meaning1815 q) (meaning1828 q) hs
  change valuationOf q 1790 = false ∨ valuationOf q 1815 = false ∨ valuationOf q 1828 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1511 (q : Snake 81) (h : Conditions q) : valuation q 1790 = false ∨ valuation q 1815 = false ∨ valuation q 1828 = true := counterClause1511 (baseVal q)

theorem counterClause1512 (q : Nat → Bool) : valuationOf q 1790 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1829 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1790)) (literal (valuationOf q) (1816)) (literal (valuationOf q) (1829)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 4 2 (meaning1790 q) (meaning1816 q) (meaning1829 q) hs
  change valuationOf q 1790 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1829 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1512 (q : Snake 81) (h : Conditions q) : valuation q 1790 = false ∨ valuation q 1816 = false ∨ valuation q 1829 = true := counterClause1512 (baseVal q)

theorem counterClause1513 (q : Nat → Bool) : valuationOf q 1790 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1830 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1790)) (literal (valuationOf q) (1817)) (literal (valuationOf q) (1830)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 4 3 (meaning1790 q) (meaning1817 q) (meaning1830 q) hs
  change valuationOf q 1790 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1830 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1513 (q : Snake 81) (h : Conditions q) : valuation q 1790 = false ∨ valuation q 1817 = false ∨ valuation q 1830 = true := counterClause1513 (baseVal q)

theorem counterClause1514 (q : Nat → Bool) : valuationOf q 1790 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1831 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1790)) (literal (valuationOf q) (1818)) (literal (valuationOf q) (1831)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 4 4 (meaning1790 q) (meaning1818 q) (meaning1831 q) hs
  change valuationOf q 1790 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1514 (q : Snake 81) (h : Conditions q) : valuation q 1790 = false ∨ valuation q 1818 = false ∨ valuation q 1831 = true := counterClause1514 (baseVal q)

theorem counterClause1515 (q : Nat → Bool) : valuationOf q 1790 = false ∨ valuationOf q 1819 = false ∨ valuationOf q 1832 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1790)) (literal (valuationOf q) (1819)) (literal (valuationOf q) (1832)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 4 5 (meaning1790 q) (meaning1819 q) (meaning1832 q) hs
  change valuationOf q 1790 = false ∨ valuationOf q 1819 = false ∨ valuationOf q 1832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1515 (q : Snake 81) (h : Conditions q) : valuation q 1790 = false ∨ valuation q 1819 = false ∨ valuation q 1832 = true := counterClause1515 (baseVal q)

theorem counterClause1516 (q : Nat → Bool) : valuationOf q 1790 = false ∨ valuationOf q 1820 = false ∨ valuationOf q 1833 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1790)) (literal (valuationOf q) (1820)) (literal (valuationOf q) (1833)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 4 6 (meaning1790 q) (meaning1820 q) (meaning1833 q) hs
  change valuationOf q 1790 = false ∨ valuationOf q 1820 = false ∨ valuationOf q 1833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1516 (q : Snake 81) (h : Conditions q) : valuation q 1790 = false ∨ valuation q 1820 = false ∨ valuation q 1833 = true := counterClause1516 (baseVal q)

theorem counterClause1517 (q : Nat → Bool) : valuationOf q 1791 = false ∨ valuationOf q 1815 = false ∨ valuationOf q 1829 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1791)) (literal (valuationOf q) (1815)) (literal (valuationOf q) (1829)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 5 1 (meaning1791 q) (meaning1815 q) (meaning1829 q) hs
  change valuationOf q 1791 = false ∨ valuationOf q 1815 = false ∨ valuationOf q 1829 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1517 (q : Snake 81) (h : Conditions q) : valuation q 1791 = false ∨ valuation q 1815 = false ∨ valuation q 1829 = true := counterClause1517 (baseVal q)

theorem counterClause1518 (q : Nat → Bool) : valuationOf q 1791 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1830 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1791)) (literal (valuationOf q) (1816)) (literal (valuationOf q) (1830)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 5 2 (meaning1791 q) (meaning1816 q) (meaning1830 q) hs
  change valuationOf q 1791 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1830 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1518 (q : Snake 81) (h : Conditions q) : valuation q 1791 = false ∨ valuation q 1816 = false ∨ valuation q 1830 = true := counterClause1518 (baseVal q)

theorem counterClause1519 (q : Nat → Bool) : valuationOf q 1791 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1831 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1791)) (literal (valuationOf q) (1817)) (literal (valuationOf q) (1831)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 5 3 (meaning1791 q) (meaning1817 q) (meaning1831 q) hs
  change valuationOf q 1791 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1519 (q : Snake 81) (h : Conditions q) : valuation q 1791 = false ∨ valuation q 1817 = false ∨ valuation q 1831 = true := counterClause1519 (baseVal q)

theorem counterClause1520 (q : Nat → Bool) : valuationOf q 1791 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1832 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1791)) (literal (valuationOf q) (1818)) (literal (valuationOf q) (1832)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 5 4 (meaning1791 q) (meaning1818 q) (meaning1832 q) hs
  change valuationOf q 1791 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1520 (q : Snake 81) (h : Conditions q) : valuation q 1791 = false ∨ valuation q 1818 = false ∨ valuation q 1832 = true := counterClause1520 (baseVal q)

theorem counterClause1521 (q : Nat → Bool) : valuationOf q 1791 = false ∨ valuationOf q 1819 = false ∨ valuationOf q 1833 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1791)) (literal (valuationOf q) (1819)) (literal (valuationOf q) (1833)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 5 5 (meaning1791 q) (meaning1819 q) (meaning1833 q) hs
  change valuationOf q 1791 = false ∨ valuationOf q 1819 = false ∨ valuationOf q 1833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1521 (q : Snake 81) (h : Conditions q) : valuation q 1791 = false ∨ valuation q 1819 = false ∨ valuation q 1833 = true := counterClause1521 (baseVal q)

theorem counterClause1522 (q : Nat → Bool) : valuationOf q 1792 = false ∨ valuationOf q 1815 = false ∨ valuationOf q 1830 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1792)) (literal (valuationOf q) (1815)) (literal (valuationOf q) (1830)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 6 1 (meaning1792 q) (meaning1815 q) (meaning1830 q) hs
  change valuationOf q 1792 = false ∨ valuationOf q 1815 = false ∨ valuationOf q 1830 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1522 (q : Snake 81) (h : Conditions q) : valuation q 1792 = false ∨ valuation q 1815 = false ∨ valuation q 1830 = true := counterClause1522 (baseVal q)

theorem counterClause1523 (q : Nat → Bool) : valuationOf q 1792 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1831 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1792)) (literal (valuationOf q) (1816)) (literal (valuationOf q) (1831)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 6 2 (meaning1792 q) (meaning1816 q) (meaning1831 q) hs
  change valuationOf q 1792 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1523 (q : Snake 81) (h : Conditions q) : valuation q 1792 = false ∨ valuation q 1816 = false ∨ valuation q 1831 = true := counterClause1523 (baseVal q)

theorem counterClause1524 (q : Nat → Bool) : valuationOf q 1792 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1832 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1792)) (literal (valuationOf q) (1817)) (literal (valuationOf q) (1832)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 6 3 (meaning1792 q) (meaning1817 q) (meaning1832 q) hs
  change valuationOf q 1792 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1524 (q : Snake 81) (h : Conditions q) : valuation q 1792 = false ∨ valuation q 1817 = false ∨ valuation q 1832 = true := counterClause1524 (baseVal q)

theorem counterClause1525 (q : Nat → Bool) : valuationOf q 1792 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1833 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1792)) (literal (valuationOf q) (1818)) (literal (valuationOf q) (1833)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 6 4 (meaning1792 q) (meaning1818 q) (meaning1833 q) hs
  change valuationOf q 1792 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1525 (q : Snake 81) (h : Conditions q) : valuation q 1792 = false ∨ valuation q 1818 = false ∨ valuation q 1833 = true := counterClause1525 (baseVal q)

theorem counterClause1526 (q : Nat → Bool) : valuationOf q 1792 = false ∨ valuationOf q 1819 = false ∨ valuationOf q 1834 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1792)) (literal (valuationOf q) (1819)) (literal (valuationOf q) (1834)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 6 5 (meaning1792 q) (meaning1819 q) (meaning1834 q) hs
  change valuationOf q 1792 = false ∨ valuationOf q 1819 = false ∨ valuationOf q 1834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1526 (q : Snake 81) (h : Conditions q) : valuation q 1792 = false ∨ valuation q 1819 = false ∨ valuation q 1834 = true := counterClause1526 (baseVal q)

theorem counterClause1527 (q : Nat → Bool) : valuationOf q 1793 = false ∨ valuationOf q 1830 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_left (literal (valuationOf q) (1793)) (literal (valuationOf q) (1830)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 7 (meaning1793 q) (meaning1830 q) hs
  change valuationOf q 1793 = false ∨ valuationOf q 1830 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1527 (q : Snake 81) (h : Conditions q) : valuation q 1793 = false ∨ valuation q 1830 = true := counterClause1527 (baseVal q)

theorem counterClause1528 (q : Nat → Bool) : valuationOf q 1793 = false ∨ valuationOf q 1815 = false ∨ valuationOf q 1831 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1793)) (literal (valuationOf q) (1815)) (literal (valuationOf q) (1831)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 7 1 (meaning1793 q) (meaning1815 q) (meaning1831 q) hs
  change valuationOf q 1793 = false ∨ valuationOf q 1815 = false ∨ valuationOf q 1831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1528 (q : Snake 81) (h : Conditions q) : valuation q 1793 = false ∨ valuation q 1815 = false ∨ valuation q 1831 = true := counterClause1528 (baseVal q)

theorem counterClause1529 (q : Nat → Bool) : valuationOf q 1793 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1832 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1793)) (literal (valuationOf q) (1816)) (literal (valuationOf q) (1832)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 7 2 (meaning1793 q) (meaning1816 q) (meaning1832 q) hs
  change valuationOf q 1793 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1529 (q : Snake 81) (h : Conditions q) : valuation q 1793 = false ∨ valuation q 1816 = false ∨ valuation q 1832 = true := counterClause1529 (baseVal q)

theorem counterClause1530 (q : Nat → Bool) : valuationOf q 1793 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1833 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1793)) (literal (valuationOf q) (1817)) (literal (valuationOf q) (1833)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 7 3 (meaning1793 q) (meaning1817 q) (meaning1833 q) hs
  change valuationOf q 1793 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1530 (q : Snake 81) (h : Conditions q) : valuation q 1793 = false ∨ valuation q 1817 = false ∨ valuation q 1833 = true := counterClause1530 (baseVal q)

theorem counterClause1531 (q : Nat → Bool) : valuationOf q 1793 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1834 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1793)) (literal (valuationOf q) (1818)) (literal (valuationOf q) (1834)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 7 4 (meaning1793 q) (meaning1818 q) (meaning1834 q) hs
  change valuationOf q 1793 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1531 (q : Snake 81) (h : Conditions q) : valuation q 1793 = false ∨ valuation q 1818 = false ∨ valuation q 1834 = true := counterClause1531 (baseVal q)

theorem counterClause1532 (q : Nat → Bool) : valuationOf q 1793 = false ∨ valuationOf q 1819 = false ∨ valuationOf q 1835 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1793)) (literal (valuationOf q) (1819)) (literal (valuationOf q) (1835)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 7 5 (meaning1793 q) (meaning1819 q) (meaning1835 q) hs
  change valuationOf q 1793 = false ∨ valuationOf q 1819 = false ∨ valuationOf q 1835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1532 (q : Snake 81) (h : Conditions q) : valuation q 1793 = false ∨ valuation q 1819 = false ∨ valuation q 1835 = true := counterClause1532 (baseVal q)

theorem counterClause1533 (q : Nat → Bool) : valuationOf q 1794 = false ∨ valuationOf q 1815 = false ∨ valuationOf q 1832 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1794)) (literal (valuationOf q) (1815)) (literal (valuationOf q) (1832)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 8 1 (meaning1794 q) (meaning1815 q) (meaning1832 q) hs
  change valuationOf q 1794 = false ∨ valuationOf q 1815 = false ∨ valuationOf q 1832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1533 (q : Snake 81) (h : Conditions q) : valuation q 1794 = false ∨ valuation q 1815 = false ∨ valuation q 1832 = true := counterClause1533 (baseVal q)

theorem counterClause1534 (q : Nat → Bool) : valuationOf q 1794 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1833 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1794)) (literal (valuationOf q) (1816)) (literal (valuationOf q) (1833)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 8 2 (meaning1794 q) (meaning1816 q) (meaning1833 q) hs
  change valuationOf q 1794 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1534 (q : Snake 81) (h : Conditions q) : valuation q 1794 = false ∨ valuation q 1816 = false ∨ valuation q 1833 = true := counterClause1534 (baseVal q)

theorem counterClause1535 (q : Nat → Bool) : valuationOf q 1794 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1835 = true := by
  have hs : count1824 q = (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) + (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-96, -98, -100, -101, -103, -105, -106, -109]) (l₂ := [-112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1794)) (literal (valuationOf q) (1818)) (literal (valuationOf q) (1835)) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109]) (countLit q [-112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1824 q) 8 4 (meaning1794 q) (meaning1818 q) (meaning1835 q) hs
  change valuationOf q 1794 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1535 (q : Snake 81) (h : Conditions q) : valuation q 1794 = false ∨ valuation q 1818 = false ∨ valuation q 1835 = true := counterClause1535 (baseVal q)

theorem counterClause1536 (q : Nat → Bool) : valuationOf q 1756 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1849 = true := by
  have hs : count1841 q = (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) + (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (l₂ := [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1756)) (literal (valuationOf q) (1830)) (literal (valuationOf q) (1849)) (countLit q [-63, -64, -67, -70, -72, -73, -75, -76, -80, -82, -83, -84, -87, -88, -92, -93]) (countLit q [-96, -98, -100, -101, -103, -105, -106, -109, -112, -114, -115, -117, -118, -122, -124, -125, -126]) (count1841 q) 2 7 (meaning1756 q) (meaning1830 q) (meaning1849 q) hs
  change valuationOf q 1756 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1849 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1536 (q : Snake 81) (h : Conditions q) : valuation q 1756 = false ∨ valuation q 1830 = false ∨ valuation q 1849 = true := counterClause1536 (baseVal q)

theorem block47 (q : Snake 81) (h : Conditions q) : B112E036.Block47 (valuation q) :=
  ⟨clause1505 q h, clause1506 q h, clause1507 q h, clause1508 q h, clause1509 q h, clause1510 q h, clause1511 q h, clause1512 q h, clause1513 q h, clause1514 q h, clause1515 q h, clause1516 q h, clause1517 q h, clause1518 q h, clause1519 q h, clause1520 q h, clause1521 q h, clause1522 q h, clause1523 q h, clause1524 q h, clause1525 q h, clause1526 q h, clause1527 q h, clause1528 q h, clause1529 q h, clause1530 q h, clause1531 q h, clause1532 q h, clause1533 q h, clause1534 q h, clause1535 q h, clause1536 q h⟩

end
end Snake9.Regrowth.E112036
