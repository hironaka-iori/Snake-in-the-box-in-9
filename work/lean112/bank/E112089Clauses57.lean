import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec57 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1825 (q : Nat → Bool) : valuationOf q 1746 = false ∨ valuationOf q 1750 = true := by
  have hs : count1749 q = (countLit q [-111, -113, -115, -117]) + (countLit q [-119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -113, -115, -117]) (l₂ := [-119, -120, -122, -123])
  have hm := merge_right (literal (valuationOf q) (1746)) (literal (valuationOf q) (1750)) (countLit q [-111, -113, -115, -117]) (countLit q [-119, -120, -122, -123]) (count1749 q) 2 (meaning1746 q) (meaning1750 q) hs
  change valuationOf q 1746 = false ∨ valuationOf q 1750 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1825 (q : Snake 81) (h : Conditions q) : valuation q 1746 = false ∨ valuation q 1750 = true := counterClause1825 (baseVal q)

theorem counterClause1826 (q : Nat → Bool) : valuationOf q 1747 = false ∨ valuationOf q 1751 = true := by
  have hs : count1749 q = (countLit q [-111, -113, -115, -117]) + (countLit q [-119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -113, -115, -117]) (l₂ := [-119, -120, -122, -123])
  have hm := merge_right (literal (valuationOf q) (1747)) (literal (valuationOf q) (1751)) (countLit q [-111, -113, -115, -117]) (countLit q [-119, -120, -122, -123]) (count1749 q) 3 (meaning1747 q) (meaning1751 q) hs
  change valuationOf q 1747 = false ∨ valuationOf q 1751 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1826 (q : Snake 81) (h : Conditions q) : valuation q 1747 = false ∨ valuation q 1751 = true := counterClause1826 (baseVal q)

theorem counterClause1827 (q : Nat → Bool) : valuationOf q 1737 = false ∨ valuationOf q 1749 = true := by
  have hs : count1749 q = (countLit q [-111, -113, -115, -117]) + (countLit q [-119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -113, -115, -117]) (l₂ := [-119, -120, -122, -123])
  have hm := merge_left (literal (valuationOf q) (1737)) (literal (valuationOf q) (1749)) (countLit q [-111, -113, -115, -117]) (countLit q [-119, -120, -122, -123]) (count1749 q) 1 (meaning1737 q) (meaning1749 q) hs
  change valuationOf q 1737 = false ∨ valuationOf q 1749 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1827 (q : Snake 81) (h : Conditions q) : valuation q 1737 = false ∨ valuation q 1749 = true := counterClause1827 (baseVal q)

theorem counterClause1828 (q : Nat → Bool) : valuationOf q 1737 = false ∨ valuationOf q 1745 = false ∨ valuationOf q 1750 = true := by
  have hs : count1749 q = (countLit q [-111, -113, -115, -117]) + (countLit q [-119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -113, -115, -117]) (l₂ := [-119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1737)) (literal (valuationOf q) (1745)) (literal (valuationOf q) (1750)) (countLit q [-111, -113, -115, -117]) (countLit q [-119, -120, -122, -123]) (count1749 q) 1 1 (meaning1737 q) (meaning1745 q) (meaning1750 q) hs
  change valuationOf q 1737 = false ∨ valuationOf q 1745 = false ∨ valuationOf q 1750 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1828 (q : Snake 81) (h : Conditions q) : valuation q 1737 = false ∨ valuation q 1745 = false ∨ valuation q 1750 = true := counterClause1828 (baseVal q)

theorem counterClause1829 (q : Nat → Bool) : valuationOf q 1737 = false ∨ valuationOf q 1746 = false ∨ valuationOf q 1751 = true := by
  have hs : count1749 q = (countLit q [-111, -113, -115, -117]) + (countLit q [-119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -113, -115, -117]) (l₂ := [-119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1737)) (literal (valuationOf q) (1746)) (literal (valuationOf q) (1751)) (countLit q [-111, -113, -115, -117]) (countLit q [-119, -120, -122, -123]) (count1749 q) 1 2 (meaning1737 q) (meaning1746 q) (meaning1751 q) hs
  change valuationOf q 1737 = false ∨ valuationOf q 1746 = false ∨ valuationOf q 1751 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1829 (q : Snake 81) (h : Conditions q) : valuation q 1737 = false ∨ valuation q 1746 = false ∨ valuation q 1751 = true := counterClause1829 (baseVal q)

theorem counterClause1830 (q : Nat → Bool) : valuationOf q 1737 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1752 = true := by
  have hs : count1749 q = (countLit q [-111, -113, -115, -117]) + (countLit q [-119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -113, -115, -117]) (l₂ := [-119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1737)) (literal (valuationOf q) (1747)) (literal (valuationOf q) (1752)) (countLit q [-111, -113, -115, -117]) (countLit q [-119, -120, -122, -123]) (count1749 q) 1 3 (meaning1737 q) (meaning1747 q) (meaning1752 q) hs
  change valuationOf q 1737 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1830 (q : Snake 81) (h : Conditions q) : valuation q 1737 = false ∨ valuation q 1747 = false ∨ valuation q 1752 = true := counterClause1830 (baseVal q)

theorem counterClause1831 (q : Nat → Bool) : valuationOf q 1738 = false ∨ valuationOf q 1750 = true := by
  have hs : count1749 q = (countLit q [-111, -113, -115, -117]) + (countLit q [-119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -113, -115, -117]) (l₂ := [-119, -120, -122, -123])
  have hm := merge_left (literal (valuationOf q) (1738)) (literal (valuationOf q) (1750)) (countLit q [-111, -113, -115, -117]) (countLit q [-119, -120, -122, -123]) (count1749 q) 2 (meaning1738 q) (meaning1750 q) hs
  change valuationOf q 1738 = false ∨ valuationOf q 1750 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1831 (q : Snake 81) (h : Conditions q) : valuation q 1738 = false ∨ valuation q 1750 = true := counterClause1831 (baseVal q)

theorem counterClause1832 (q : Nat → Bool) : valuationOf q 1738 = false ∨ valuationOf q 1745 = false ∨ valuationOf q 1751 = true := by
  have hs : count1749 q = (countLit q [-111, -113, -115, -117]) + (countLit q [-119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -113, -115, -117]) (l₂ := [-119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1738)) (literal (valuationOf q) (1745)) (literal (valuationOf q) (1751)) (countLit q [-111, -113, -115, -117]) (countLit q [-119, -120, -122, -123]) (count1749 q) 2 1 (meaning1738 q) (meaning1745 q) (meaning1751 q) hs
  change valuationOf q 1738 = false ∨ valuationOf q 1745 = false ∨ valuationOf q 1751 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1832 (q : Snake 81) (h : Conditions q) : valuation q 1738 = false ∨ valuation q 1745 = false ∨ valuation q 1751 = true := counterClause1832 (baseVal q)

theorem counterClause1833 (q : Nat → Bool) : valuationOf q 1738 = false ∨ valuationOf q 1746 = false ∨ valuationOf q 1752 = true := by
  have hs : count1749 q = (countLit q [-111, -113, -115, -117]) + (countLit q [-119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -113, -115, -117]) (l₂ := [-119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1738)) (literal (valuationOf q) (1746)) (literal (valuationOf q) (1752)) (countLit q [-111, -113, -115, -117]) (countLit q [-119, -120, -122, -123]) (count1749 q) 2 2 (meaning1738 q) (meaning1746 q) (meaning1752 q) hs
  change valuationOf q 1738 = false ∨ valuationOf q 1746 = false ∨ valuationOf q 1752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1833 (q : Snake 81) (h : Conditions q) : valuation q 1738 = false ∨ valuation q 1746 = false ∨ valuation q 1752 = true := counterClause1833 (baseVal q)

theorem counterClause1834 (q : Nat → Bool) : valuationOf q 1738 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1753 = true := by
  have hs : count1749 q = (countLit q [-111, -113, -115, -117]) + (countLit q [-119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -113, -115, -117]) (l₂ := [-119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1738)) (literal (valuationOf q) (1747)) (literal (valuationOf q) (1753)) (countLit q [-111, -113, -115, -117]) (countLit q [-119, -120, -122, -123]) (count1749 q) 2 3 (meaning1738 q) (meaning1747 q) (meaning1753 q) hs
  change valuationOf q 1738 = false ∨ valuationOf q 1747 = false ∨ valuationOf q 1753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1834 (q : Snake 81) (h : Conditions q) : valuation q 1738 = false ∨ valuation q 1747 = false ∨ valuation q 1753 = true := counterClause1834 (baseVal q)

theorem counterClause1835 (q : Nat → Bool) : valuationOf q 1739 = false ∨ valuationOf q 1751 = true := by
  have hs : count1749 q = (countLit q [-111, -113, -115, -117]) + (countLit q [-119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -113, -115, -117]) (l₂ := [-119, -120, -122, -123])
  have hm := merge_left (literal (valuationOf q) (1739)) (literal (valuationOf q) (1751)) (countLit q [-111, -113, -115, -117]) (countLit q [-119, -120, -122, -123]) (count1749 q) 3 (meaning1739 q) (meaning1751 q) hs
  change valuationOf q 1739 = false ∨ valuationOf q 1751 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1835 (q : Snake 81) (h : Conditions q) : valuation q 1739 = false ∨ valuation q 1751 = true := counterClause1835 (baseVal q)

theorem counterClause1836 (q : Nat → Bool) : valuationOf q 1739 = false ∨ valuationOf q 1745 = false ∨ valuationOf q 1752 = true := by
  have hs : count1749 q = (countLit q [-111, -113, -115, -117]) + (countLit q [-119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -113, -115, -117]) (l₂ := [-119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1739)) (literal (valuationOf q) (1745)) (literal (valuationOf q) (1752)) (countLit q [-111, -113, -115, -117]) (countLit q [-119, -120, -122, -123]) (count1749 q) 3 1 (meaning1739 q) (meaning1745 q) (meaning1752 q) hs
  change valuationOf q 1739 = false ∨ valuationOf q 1745 = false ∨ valuationOf q 1752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1836 (q : Snake 81) (h : Conditions q) : valuation q 1739 = false ∨ valuation q 1745 = false ∨ valuation q 1752 = true := counterClause1836 (baseVal q)

theorem counterClause1837 (q : Nat → Bool) : valuationOf q 1739 = false ∨ valuationOf q 1746 = false ∨ valuationOf q 1753 = true := by
  have hs : count1749 q = (countLit q [-111, -113, -115, -117]) + (countLit q [-119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -113, -115, -117]) (l₂ := [-119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1739)) (literal (valuationOf q) (1746)) (literal (valuationOf q) (1753)) (countLit q [-111, -113, -115, -117]) (countLit q [-119, -120, -122, -123]) (count1749 q) 3 2 (meaning1739 q) (meaning1746 q) (meaning1753 q) hs
  change valuationOf q 1739 = false ∨ valuationOf q 1746 = false ∨ valuationOf q 1753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1837 (q : Snake 81) (h : Conditions q) : valuation q 1739 = false ∨ valuation q 1746 = false ∨ valuation q 1753 = true := counterClause1837 (baseVal q)

theorem counterClause1838 (q : Nat → Bool) : valuationOf q 1740 = false ∨ valuationOf q 1752 = true := by
  have hs : count1749 q = (countLit q [-111, -113, -115, -117]) + (countLit q [-119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -113, -115, -117]) (l₂ := [-119, -120, -122, -123])
  have hm := merge_left (literal (valuationOf q) (1740)) (literal (valuationOf q) (1752)) (countLit q [-111, -113, -115, -117]) (countLit q [-119, -120, -122, -123]) (count1749 q) 4 (meaning1740 q) (meaning1752 q) hs
  change valuationOf q 1740 = false ∨ valuationOf q 1752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1838 (q : Snake 81) (h : Conditions q) : valuation q 1740 = false ∨ valuation q 1752 = true := counterClause1838 (baseVal q)

theorem counterClause1839 (q : Nat → Bool) : valuationOf q 1740 = false ∨ valuationOf q 1745 = false ∨ valuationOf q 1753 = true := by
  have hs : count1749 q = (countLit q [-111, -113, -115, -117]) + (countLit q [-119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-111, -113, -115, -117]) (l₂ := [-119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1740)) (literal (valuationOf q) (1745)) (literal (valuationOf q) (1753)) (countLit q [-111, -113, -115, -117]) (countLit q [-119, -120, -122, -123]) (count1749 q) 4 1 (meaning1740 q) (meaning1745 q) (meaning1753 q) hs
  change valuationOf q 1740 = false ∨ valuationOf q 1745 = false ∨ valuationOf q 1753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1839 (q : Snake 81) (h : Conditions q) : valuation q 1740 = false ∨ valuation q 1745 = false ∨ valuation q 1753 = true := counterClause1839 (baseVal q)

theorem counterClause1840 (q : Nat → Bool) : valuationOf q 1749 = false ∨ valuationOf q 1757 = true := by
  have hs : count1757 q = (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) + (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99, -102, -103, -104, -107]) (l₂ := [-111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_right (literal (valuationOf q) (1749)) (literal (valuationOf q) (1757)) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) (count1757 q) 1 (meaning1749 q) (meaning1757 q) hs
  change valuationOf q 1749 = false ∨ valuationOf q 1757 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1840 (q : Snake 81) (h : Conditions q) : valuation q 1749 = false ∨ valuation q 1757 = true := counterClause1840 (baseVal q)

theorem counterClause1841 (q : Nat → Bool) : valuationOf q 1750 = false ∨ valuationOf q 1758 = true := by
  have hs : count1757 q = (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) + (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99, -102, -103, -104, -107]) (l₂ := [-111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_right (literal (valuationOf q) (1750)) (literal (valuationOf q) (1758)) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) (count1757 q) 2 (meaning1750 q) (meaning1758 q) hs
  change valuationOf q 1750 = false ∨ valuationOf q 1758 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1841 (q : Snake 81) (h : Conditions q) : valuation q 1750 = false ∨ valuation q 1758 = true := counterClause1841 (baseVal q)

theorem counterClause1842 (q : Nat → Bool) : valuationOf q 1751 = false ∨ valuationOf q 1759 = true := by
  have hs : count1757 q = (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) + (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99, -102, -103, -104, -107]) (l₂ := [-111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_right (literal (valuationOf q) (1751)) (literal (valuationOf q) (1759)) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) (count1757 q) 3 (meaning1751 q) (meaning1759 q) hs
  change valuationOf q 1751 = false ∨ valuationOf q 1759 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1842 (q : Snake 81) (h : Conditions q) : valuation q 1751 = false ∨ valuation q 1759 = true := counterClause1842 (baseVal q)

theorem counterClause1843 (q : Nat → Bool) : valuationOf q 1752 = false ∨ valuationOf q 1760 = true := by
  have hs : count1757 q = (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) + (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99, -102, -103, -104, -107]) (l₂ := [-111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_right (literal (valuationOf q) (1752)) (literal (valuationOf q) (1760)) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) (count1757 q) 4 (meaning1752 q) (meaning1760 q) hs
  change valuationOf q 1752 = false ∨ valuationOf q 1760 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1843 (q : Snake 81) (h : Conditions q) : valuation q 1752 = false ∨ valuation q 1760 = true := counterClause1843 (baseVal q)

theorem counterClause1844 (q : Nat → Bool) : valuationOf q 1753 = false ∨ valuationOf q 1761 = true := by
  have hs : count1757 q = (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) + (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99, -102, -103, -104, -107]) (l₂ := [-111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_right (literal (valuationOf q) (1753)) (literal (valuationOf q) (1761)) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) (count1757 q) 5 (meaning1753 q) (meaning1761 q) hs
  change valuationOf q 1753 = false ∨ valuationOf q 1761 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1844 (q : Snake 81) (h : Conditions q) : valuation q 1753 = false ∨ valuation q 1761 = true := counterClause1844 (baseVal q)

theorem counterClause1845 (q : Nat → Bool) : valuationOf q 1725 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1758 = true := by
  have hs : count1757 q = (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) + (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99, -102, -103, -104, -107]) (l₂ := [-111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1725)) (literal (valuationOf q) (1749)) (literal (valuationOf q) (1758)) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) (count1757 q) 1 1 (meaning1725 q) (meaning1749 q) (meaning1758 q) hs
  change valuationOf q 1725 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1758 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1845 (q : Snake 81) (h : Conditions q) : valuation q 1725 = false ∨ valuation q 1749 = false ∨ valuation q 1758 = true := counterClause1845 (baseVal q)

theorem counterClause1846 (q : Nat → Bool) : valuationOf q 1725 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1759 = true := by
  have hs : count1757 q = (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) + (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99, -102, -103, -104, -107]) (l₂ := [-111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1725)) (literal (valuationOf q) (1750)) (literal (valuationOf q) (1759)) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) (count1757 q) 1 2 (meaning1725 q) (meaning1750 q) (meaning1759 q) hs
  change valuationOf q 1725 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1759 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1846 (q : Snake 81) (h : Conditions q) : valuation q 1725 = false ∨ valuation q 1750 = false ∨ valuation q 1759 = true := counterClause1846 (baseVal q)

theorem counterClause1847 (q : Nat → Bool) : valuationOf q 1725 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1760 = true := by
  have hs : count1757 q = (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) + (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99, -102, -103, -104, -107]) (l₂ := [-111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1725)) (literal (valuationOf q) (1751)) (literal (valuationOf q) (1760)) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) (count1757 q) 1 3 (meaning1725 q) (meaning1751 q) (meaning1760 q) hs
  change valuationOf q 1725 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1760 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1847 (q : Snake 81) (h : Conditions q) : valuation q 1725 = false ∨ valuation q 1751 = false ∨ valuation q 1760 = true := counterClause1847 (baseVal q)

theorem counterClause1848 (q : Nat → Bool) : valuationOf q 1725 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1761 = true := by
  have hs : count1757 q = (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) + (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99, -102, -103, -104, -107]) (l₂ := [-111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1725)) (literal (valuationOf q) (1752)) (literal (valuationOf q) (1761)) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) (count1757 q) 1 4 (meaning1725 q) (meaning1752 q) (meaning1761 q) hs
  change valuationOf q 1725 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1761 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1848 (q : Snake 81) (h : Conditions q) : valuation q 1725 = false ∨ valuation q 1752 = false ∨ valuation q 1761 = true := counterClause1848 (baseVal q)

theorem counterClause1849 (q : Nat → Bool) : valuationOf q 1725 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1762 = true := by
  have hs : count1757 q = (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) + (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99, -102, -103, -104, -107]) (l₂ := [-111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1725)) (literal (valuationOf q) (1753)) (literal (valuationOf q) (1762)) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) (count1757 q) 1 5 (meaning1725 q) (meaning1753 q) (meaning1762 q) hs
  change valuationOf q 1725 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1849 (q : Snake 81) (h : Conditions q) : valuation q 1725 = false ∨ valuation q 1753 = false ∨ valuation q 1762 = true := counterClause1849 (baseVal q)

theorem counterClause1850 (q : Nat → Bool) : valuationOf q 1726 = false ∨ valuationOf q 1758 = true := by
  have hs : count1757 q = (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) + (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99, -102, -103, -104, -107]) (l₂ := [-111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_left (literal (valuationOf q) (1726)) (literal (valuationOf q) (1758)) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) (count1757 q) 2 (meaning1726 q) (meaning1758 q) hs
  change valuationOf q 1726 = false ∨ valuationOf q 1758 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1850 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false ∨ valuation q 1758 = true := counterClause1850 (baseVal q)

theorem counterClause1851 (q : Nat → Bool) : valuationOf q 1726 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1759 = true := by
  have hs : count1757 q = (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) + (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99, -102, -103, -104, -107]) (l₂ := [-111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1726)) (literal (valuationOf q) (1749)) (literal (valuationOf q) (1759)) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) (count1757 q) 2 1 (meaning1726 q) (meaning1749 q) (meaning1759 q) hs
  change valuationOf q 1726 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1759 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1851 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false ∨ valuation q 1749 = false ∨ valuation q 1759 = true := counterClause1851 (baseVal q)

theorem counterClause1852 (q : Nat → Bool) : valuationOf q 1726 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1760 = true := by
  have hs : count1757 q = (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) + (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99, -102, -103, -104, -107]) (l₂ := [-111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1726)) (literal (valuationOf q) (1750)) (literal (valuationOf q) (1760)) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) (count1757 q) 2 2 (meaning1726 q) (meaning1750 q) (meaning1760 q) hs
  change valuationOf q 1726 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1760 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1852 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false ∨ valuation q 1750 = false ∨ valuation q 1760 = true := counterClause1852 (baseVal q)

theorem counterClause1853 (q : Nat → Bool) : valuationOf q 1726 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1761 = true := by
  have hs : count1757 q = (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) + (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99, -102, -103, -104, -107]) (l₂ := [-111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1726)) (literal (valuationOf q) (1751)) (literal (valuationOf q) (1761)) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) (count1757 q) 2 3 (meaning1726 q) (meaning1751 q) (meaning1761 q) hs
  change valuationOf q 1726 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1761 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1853 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false ∨ valuation q 1751 = false ∨ valuation q 1761 = true := counterClause1853 (baseVal q)

theorem counterClause1854 (q : Nat → Bool) : valuationOf q 1726 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1762 = true := by
  have hs : count1757 q = (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) + (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99, -102, -103, -104, -107]) (l₂ := [-111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1726)) (literal (valuationOf q) (1752)) (literal (valuationOf q) (1762)) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) (count1757 q) 2 4 (meaning1726 q) (meaning1752 q) (meaning1762 q) hs
  change valuationOf q 1726 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1854 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false ∨ valuation q 1752 = false ∨ valuation q 1762 = true := counterClause1854 (baseVal q)

theorem counterClause1855 (q : Nat → Bool) : valuationOf q 1726 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1763 = true := by
  have hs : count1757 q = (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) + (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99, -102, -103, -104, -107]) (l₂ := [-111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1726)) (literal (valuationOf q) (1753)) (literal (valuationOf q) (1763)) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) (count1757 q) 2 5 (meaning1726 q) (meaning1753 q) (meaning1763 q) hs
  change valuationOf q 1726 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1763 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1855 (q : Snake 81) (h : Conditions q) : valuation q 1726 = false ∨ valuation q 1753 = false ∨ valuation q 1763 = true := counterClause1855 (baseVal q)

theorem counterClause1856 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1759 = true := by
  have hs : count1757 q = (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) + (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99, -102, -103, -104, -107]) (l₂ := [-111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_left (literal (valuationOf q) (1727)) (literal (valuationOf q) (1759)) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) (count1757 q) 3 (meaning1727 q) (meaning1759 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1759 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1856 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1759 = true := counterClause1856 (baseVal q)

theorem block57 (q : Snake 81) (h : Conditions q) : B112E089.Block57 (valuation q) :=
  ⟨clause1825 q h, clause1826 q h, clause1827 q h, clause1828 q h, clause1829 q h, clause1830 q h, clause1831 q h, clause1832 q h, clause1833 q h, clause1834 q h, clause1835 q h, clause1836 q h, clause1837 q h, clause1838 q h, clause1839 q h, clause1840 q h, clause1841 q h, clause1842 q h, clause1843 q h, clause1844 q h, clause1845 q h, clause1846 q h, clause1847 q h, clause1848 q h, clause1849 q h, clause1850 q h, clause1851 q h, clause1852 q h, clause1853 q h, clause1854 q h, clause1855 q h, clause1856 q h⟩

end
end Snake9.Regrowth.E112089
