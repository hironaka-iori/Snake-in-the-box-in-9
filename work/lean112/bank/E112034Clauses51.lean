import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec51 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1633 (q : Nat → Bool) : valuationOf q 1789 = false ∨ valuationOf q 1821 = false ∨ valuationOf q 1833 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1789)) (literal (valuationOf q) (1821)) (literal (valuationOf q) (1833)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 3 7 (meaning1789 q) (meaning1821 q) (meaning1833 q) hs
  change valuationOf q 1789 = false ∨ valuationOf q 1821 = false ∨ valuationOf q 1833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1633 (q : Snake 81) (h : Conditions q) : valuation q 1789 = false ∨ valuation q 1821 = false ∨ valuation q 1833 = true := counterClause1633 (baseVal q)

theorem counterClause1634 (q : Nat → Bool) : valuationOf q 1789 = false ∨ valuationOf q 1822 = false ∨ valuationOf q 1834 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1789)) (literal (valuationOf q) (1822)) (literal (valuationOf q) (1834)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 3 8 (meaning1789 q) (meaning1822 q) (meaning1834 q) hs
  change valuationOf q 1789 = false ∨ valuationOf q 1822 = false ∨ valuationOf q 1834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1634 (q : Snake 81) (h : Conditions q) : valuation q 1789 = false ∨ valuation q 1822 = false ∨ valuation q 1834 = true := counterClause1634 (baseVal q)

theorem counterClause1635 (q : Nat → Bool) : valuationOf q 1790 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1829 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1790)) (literal (valuationOf q) (1816)) (literal (valuationOf q) (1829)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 4 2 (meaning1790 q) (meaning1816 q) (meaning1829 q) hs
  change valuationOf q 1790 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1829 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1635 (q : Snake 81) (h : Conditions q) : valuation q 1790 = false ∨ valuation q 1816 = false ∨ valuation q 1829 = true := counterClause1635 (baseVal q)

theorem counterClause1636 (q : Nat → Bool) : valuationOf q 1790 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1830 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1790)) (literal (valuationOf q) (1817)) (literal (valuationOf q) (1830)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 4 3 (meaning1790 q) (meaning1817 q) (meaning1830 q) hs
  change valuationOf q 1790 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1830 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1636 (q : Snake 81) (h : Conditions q) : valuation q 1790 = false ∨ valuation q 1817 = false ∨ valuation q 1830 = true := counterClause1636 (baseVal q)

theorem counterClause1637 (q : Nat → Bool) : valuationOf q 1790 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1831 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1790)) (literal (valuationOf q) (1818)) (literal (valuationOf q) (1831)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 4 4 (meaning1790 q) (meaning1818 q) (meaning1831 q) hs
  change valuationOf q 1790 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1637 (q : Snake 81) (h : Conditions q) : valuation q 1790 = false ∨ valuation q 1818 = false ∨ valuation q 1831 = true := counterClause1637 (baseVal q)

theorem counterClause1638 (q : Nat → Bool) : valuationOf q 1790 = false ∨ valuationOf q 1819 = false ∨ valuationOf q 1832 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1790)) (literal (valuationOf q) (1819)) (literal (valuationOf q) (1832)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 4 5 (meaning1790 q) (meaning1819 q) (meaning1832 q) hs
  change valuationOf q 1790 = false ∨ valuationOf q 1819 = false ∨ valuationOf q 1832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1638 (q : Snake 81) (h : Conditions q) : valuation q 1790 = false ∨ valuation q 1819 = false ∨ valuation q 1832 = true := counterClause1638 (baseVal q)

theorem counterClause1639 (q : Nat → Bool) : valuationOf q 1790 = false ∨ valuationOf q 1820 = false ∨ valuationOf q 1833 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1790)) (literal (valuationOf q) (1820)) (literal (valuationOf q) (1833)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 4 6 (meaning1790 q) (meaning1820 q) (meaning1833 q) hs
  change valuationOf q 1790 = false ∨ valuationOf q 1820 = false ∨ valuationOf q 1833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1639 (q : Snake 81) (h : Conditions q) : valuation q 1790 = false ∨ valuation q 1820 = false ∨ valuation q 1833 = true := counterClause1639 (baseVal q)

theorem counterClause1640 (q : Nat → Bool) : valuationOf q 1790 = false ∨ valuationOf q 1821 = false ∨ valuationOf q 1834 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1790)) (literal (valuationOf q) (1821)) (literal (valuationOf q) (1834)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 4 7 (meaning1790 q) (meaning1821 q) (meaning1834 q) hs
  change valuationOf q 1790 = false ∨ valuationOf q 1821 = false ∨ valuationOf q 1834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1640 (q : Snake 81) (h : Conditions q) : valuation q 1790 = false ∨ valuation q 1821 = false ∨ valuation q 1834 = true := counterClause1640 (baseVal q)

theorem counterClause1641 (q : Nat → Bool) : valuationOf q 1790 = false ∨ valuationOf q 1822 = false ∨ valuationOf q 1835 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1790)) (literal (valuationOf q) (1822)) (literal (valuationOf q) (1835)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 4 8 (meaning1790 q) (meaning1822 q) (meaning1835 q) hs
  change valuationOf q 1790 = false ∨ valuationOf q 1822 = false ∨ valuationOf q 1835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1641 (q : Snake 81) (h : Conditions q) : valuation q 1790 = false ∨ valuation q 1822 = false ∨ valuation q 1835 = true := counterClause1641 (baseVal q)

theorem counterClause1642 (q : Nat → Bool) : valuationOf q 1791 = false ∨ valuationOf q 1815 = false ∨ valuationOf q 1829 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1791)) (literal (valuationOf q) (1815)) (literal (valuationOf q) (1829)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 5 1 (meaning1791 q) (meaning1815 q) (meaning1829 q) hs
  change valuationOf q 1791 = false ∨ valuationOf q 1815 = false ∨ valuationOf q 1829 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1642 (q : Snake 81) (h : Conditions q) : valuation q 1791 = false ∨ valuation q 1815 = false ∨ valuation q 1829 = true := counterClause1642 (baseVal q)

theorem counterClause1643 (q : Nat → Bool) : valuationOf q 1791 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1830 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1791)) (literal (valuationOf q) (1816)) (literal (valuationOf q) (1830)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 5 2 (meaning1791 q) (meaning1816 q) (meaning1830 q) hs
  change valuationOf q 1791 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1830 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1643 (q : Snake 81) (h : Conditions q) : valuation q 1791 = false ∨ valuation q 1816 = false ∨ valuation q 1830 = true := counterClause1643 (baseVal q)

theorem counterClause1644 (q : Nat → Bool) : valuationOf q 1791 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1831 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1791)) (literal (valuationOf q) (1817)) (literal (valuationOf q) (1831)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 5 3 (meaning1791 q) (meaning1817 q) (meaning1831 q) hs
  change valuationOf q 1791 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1644 (q : Snake 81) (h : Conditions q) : valuation q 1791 = false ∨ valuation q 1817 = false ∨ valuation q 1831 = true := counterClause1644 (baseVal q)

theorem counterClause1645 (q : Nat → Bool) : valuationOf q 1791 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1832 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1791)) (literal (valuationOf q) (1818)) (literal (valuationOf q) (1832)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 5 4 (meaning1791 q) (meaning1818 q) (meaning1832 q) hs
  change valuationOf q 1791 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1645 (q : Snake 81) (h : Conditions q) : valuation q 1791 = false ∨ valuation q 1818 = false ∨ valuation q 1832 = true := counterClause1645 (baseVal q)

theorem counterClause1646 (q : Nat → Bool) : valuationOf q 1791 = false ∨ valuationOf q 1819 = false ∨ valuationOf q 1833 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1791)) (literal (valuationOf q) (1819)) (literal (valuationOf q) (1833)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 5 5 (meaning1791 q) (meaning1819 q) (meaning1833 q) hs
  change valuationOf q 1791 = false ∨ valuationOf q 1819 = false ∨ valuationOf q 1833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1646 (q : Snake 81) (h : Conditions q) : valuation q 1791 = false ∨ valuation q 1819 = false ∨ valuation q 1833 = true := counterClause1646 (baseVal q)

theorem counterClause1647 (q : Nat → Bool) : valuationOf q 1791 = false ∨ valuationOf q 1820 = false ∨ valuationOf q 1834 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1791)) (literal (valuationOf q) (1820)) (literal (valuationOf q) (1834)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 5 6 (meaning1791 q) (meaning1820 q) (meaning1834 q) hs
  change valuationOf q 1791 = false ∨ valuationOf q 1820 = false ∨ valuationOf q 1834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1647 (q : Snake 81) (h : Conditions q) : valuation q 1791 = false ∨ valuation q 1820 = false ∨ valuation q 1834 = true := counterClause1647 (baseVal q)

theorem counterClause1648 (q : Nat → Bool) : valuationOf q 1791 = false ∨ valuationOf q 1821 = false ∨ valuationOf q 1835 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1791)) (literal (valuationOf q) (1821)) (literal (valuationOf q) (1835)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 5 7 (meaning1791 q) (meaning1821 q) (meaning1835 q) hs
  change valuationOf q 1791 = false ∨ valuationOf q 1821 = false ∨ valuationOf q 1835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1648 (q : Snake 81) (h : Conditions q) : valuation q 1791 = false ∨ valuation q 1821 = false ∨ valuation q 1835 = true := counterClause1648 (baseVal q)

theorem counterClause1649 (q : Nat → Bool) : valuationOf q 1791 = false ∨ valuationOf q 1822 = false ∨ valuationOf q 1836 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1791)) (literal (valuationOf q) (1822)) (literal (valuationOf q) (1836)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 5 8 (meaning1791 q) (meaning1822 q) (meaning1836 q) hs
  change valuationOf q 1791 = false ∨ valuationOf q 1822 = false ∨ valuationOf q 1836 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1649 (q : Snake 81) (h : Conditions q) : valuation q 1791 = false ∨ valuation q 1822 = false ∨ valuation q 1836 = true := counterClause1649 (baseVal q)

theorem counterClause1650 (q : Nat → Bool) : valuationOf q 1792 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1831 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1792)) (literal (valuationOf q) (1816)) (literal (valuationOf q) (1831)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 6 2 (meaning1792 q) (meaning1816 q) (meaning1831 q) hs
  change valuationOf q 1792 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1650 (q : Snake 81) (h : Conditions q) : valuation q 1792 = false ∨ valuation q 1816 = false ∨ valuation q 1831 = true := counterClause1650 (baseVal q)

theorem counterClause1651 (q : Nat → Bool) : valuationOf q 1792 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1832 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1792)) (literal (valuationOf q) (1817)) (literal (valuationOf q) (1832)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 6 3 (meaning1792 q) (meaning1817 q) (meaning1832 q) hs
  change valuationOf q 1792 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1651 (q : Snake 81) (h : Conditions q) : valuation q 1792 = false ∨ valuation q 1817 = false ∨ valuation q 1832 = true := counterClause1651 (baseVal q)

theorem counterClause1652 (q : Nat → Bool) : valuationOf q 1792 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1833 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1792)) (literal (valuationOf q) (1818)) (literal (valuationOf q) (1833)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 6 4 (meaning1792 q) (meaning1818 q) (meaning1833 q) hs
  change valuationOf q 1792 = false ∨ valuationOf q 1818 = false ∨ valuationOf q 1833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1652 (q : Snake 81) (h : Conditions q) : valuation q 1792 = false ∨ valuation q 1818 = false ∨ valuation q 1833 = true := counterClause1652 (baseVal q)

theorem counterClause1653 (q : Nat → Bool) : valuationOf q 1792 = false ∨ valuationOf q 1819 = false ∨ valuationOf q 1834 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1792)) (literal (valuationOf q) (1819)) (literal (valuationOf q) (1834)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 6 5 (meaning1792 q) (meaning1819 q) (meaning1834 q) hs
  change valuationOf q 1792 = false ∨ valuationOf q 1819 = false ∨ valuationOf q 1834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1653 (q : Snake 81) (h : Conditions q) : valuation q 1792 = false ∨ valuation q 1819 = false ∨ valuation q 1834 = true := counterClause1653 (baseVal q)

theorem counterClause1654 (q : Nat → Bool) : valuationOf q 1793 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1832 = true := by
  have hs : count1824 q = (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) + (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -98, -100, -103, -104, -107, -109]) (l₂ := [-112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1793)) (literal (valuationOf q) (1816)) (literal (valuationOf q) (1832)) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109]) (countLit q [-112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1824 q) 7 2 (meaning1793 q) (meaning1816 q) (meaning1832 q) hs
  change valuationOf q 1793 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1654 (q : Snake 81) (h : Conditions q) : valuation q 1793 = false ∨ valuation q 1816 = false ∨ valuation q 1832 = true := counterClause1654 (baseVal q)

theorem counterClause1655 (q : Nat → Bool) : valuationOf q 1755 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1852 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1755)) (literal (valuationOf q) (1833)) (literal (valuationOf q) (1852)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 2 10 (meaning1755 q) (meaning1833 q) (meaning1852 q) hs
  change valuationOf q 1755 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1852 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1655 (q : Snake 81) (h : Conditions q) : valuation q 1755 = false ∨ valuation q 1833 = false ∨ valuation q 1852 = true := counterClause1655 (baseVal q)

theorem counterClause1656 (q : Nat → Bool) : valuationOf q 1755 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1853 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1755)) (literal (valuationOf q) (1834)) (literal (valuationOf q) (1853)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 2 11 (meaning1755 q) (meaning1834 q) (meaning1853 q) hs
  change valuationOf q 1755 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1853 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1656 (q : Snake 81) (h : Conditions q) : valuation q 1755 = false ∨ valuation q 1834 = false ∨ valuation q 1853 = true := counterClause1656 (baseVal q)

theorem counterClause1657 (q : Nat → Bool) : valuationOf q 1755 = false ∨ valuationOf q 1835 = false ∨ valuationOf q 1854 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1755)) (literal (valuationOf q) (1835)) (literal (valuationOf q) (1854)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 2 12 (meaning1755 q) (meaning1835 q) (meaning1854 q) hs
  change valuationOf q 1755 = false ∨ valuationOf q 1835 = false ∨ valuationOf q 1854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1657 (q : Snake 81) (h : Conditions q) : valuation q 1755 = false ∨ valuation q 1835 = false ∨ valuation q 1854 = true := counterClause1657 (baseVal q)

theorem counterClause1658 (q : Nat → Bool) : valuationOf q 1756 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1850 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1756)) (literal (valuationOf q) (1830)) (literal (valuationOf q) (1850)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 3 7 (meaning1756 q) (meaning1830 q) (meaning1850 q) hs
  change valuationOf q 1756 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1850 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1658 (q : Snake 81) (h : Conditions q) : valuation q 1756 = false ∨ valuation q 1830 = false ∨ valuation q 1850 = true := counterClause1658 (baseVal q)

theorem counterClause1659 (q : Nat → Bool) : valuationOf q 1756 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1851 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1756)) (literal (valuationOf q) (1831)) (literal (valuationOf q) (1851)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 3 8 (meaning1756 q) (meaning1831 q) (meaning1851 q) hs
  change valuationOf q 1756 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1851 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1659 (q : Snake 81) (h : Conditions q) : valuation q 1756 = false ∨ valuation q 1831 = false ∨ valuation q 1851 = true := counterClause1659 (baseVal q)

theorem counterClause1660 (q : Nat → Bool) : valuationOf q 1756 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1852 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1756)) (literal (valuationOf q) (1832)) (literal (valuationOf q) (1852)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 3 9 (meaning1756 q) (meaning1832 q) (meaning1852 q) hs
  change valuationOf q 1756 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1852 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1660 (q : Snake 81) (h : Conditions q) : valuation q 1756 = false ∨ valuation q 1832 = false ∨ valuation q 1852 = true := counterClause1660 (baseVal q)

theorem counterClause1661 (q : Nat → Bool) : valuationOf q 1756 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1853 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1756)) (literal (valuationOf q) (1833)) (literal (valuationOf q) (1853)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 3 10 (meaning1756 q) (meaning1833 q) (meaning1853 q) hs
  change valuationOf q 1756 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1853 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1661 (q : Snake 81) (h : Conditions q) : valuation q 1756 = false ∨ valuation q 1833 = false ∨ valuation q 1853 = true := counterClause1661 (baseVal q)

theorem counterClause1662 (q : Nat → Bool) : valuationOf q 1756 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1854 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1756)) (literal (valuationOf q) (1834)) (literal (valuationOf q) (1854)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 3 11 (meaning1756 q) (meaning1834 q) (meaning1854 q) hs
  change valuationOf q 1756 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1662 (q : Snake 81) (h : Conditions q) : valuation q 1756 = false ∨ valuation q 1834 = false ∨ valuation q 1854 = true := counterClause1662 (baseVal q)

theorem counterClause1663 (q : Nat → Bool) : valuationOf q 1756 = false ∨ valuationOf q 1835 = false ∨ valuationOf q 1855 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1756)) (literal (valuationOf q) (1835)) (literal (valuationOf q) (1855)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 3 12 (meaning1756 q) (meaning1835 q) (meaning1855 q) hs
  change valuationOf q 1756 = false ∨ valuationOf q 1835 = false ∨ valuationOf q 1855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1663 (q : Snake 81) (h : Conditions q) : valuation q 1756 = false ∨ valuation q 1835 = false ∨ valuation q 1855 = true := counterClause1663 (baseVal q)

theorem counterClause1664 (q : Nat → Bool) : valuationOf q 1756 = false ∨ valuationOf q 1836 = false ∨ valuationOf q 1856 = true := by
  have hs : count1841 q = (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) + (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (l₂ := [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1756)) (literal (valuationOf q) (1836)) (literal (valuationOf q) (1856)) (countLit q [-61, -62, -65, -68, -70, -72, -73, -74, -77, -79, -81, -82, -84, -86, -89, -92, -93]) (countLit q [-95, -97, -98, -100, -103, -104, -107, -109, -112, -113, -117, -118, -120, -121, -122, -125, -126]) (count1841 q) 3 13 (meaning1756 q) (meaning1836 q) (meaning1856 q) hs
  change valuationOf q 1756 = false ∨ valuationOf q 1836 = false ∨ valuationOf q 1856 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1664 (q : Snake 81) (h : Conditions q) : valuation q 1756 = false ∨ valuation q 1836 = false ∨ valuation q 1856 = true := counterClause1664 (baseVal q)

theorem block51 (q : Snake 81) (h : Conditions q) : B112E034.Block51 (valuation q) :=
  ⟨clause1633 q h, clause1634 q h, clause1635 q h, clause1636 q h, clause1637 q h, clause1638 q h, clause1639 q h, clause1640 q h, clause1641 q h, clause1642 q h, clause1643 q h, clause1644 q h, clause1645 q h, clause1646 q h, clause1647 q h, clause1648 q h, clause1649 q h, clause1650 q h, clause1651 q h, clause1652 q h, clause1653 q h, clause1654 q h, clause1655 q h, clause1656 q h, clause1657 q h, clause1658 q h, clause1659 q h, clause1660 q h, clause1661 q h, clause1662 q h, clause1663 q h, clause1664 q h⟩

end
end Snake9.Regrowth.E112034
