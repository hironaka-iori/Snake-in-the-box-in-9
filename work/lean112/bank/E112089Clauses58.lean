import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec58 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1857 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1760 = true := by
  have hs : count1757 q = (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) + (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99, -102, -103, -104, -107]) (l₂ := [-111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1727)) (literal (valuationOf q) (1749)) (literal (valuationOf q) (1760)) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) (count1757 q) 3 1 (meaning1727 q) (meaning1749 q) (meaning1760 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1760 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1857 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1749 = false ∨ valuation q 1760 = true := counterClause1857 (baseVal q)

theorem counterClause1858 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1761 = true := by
  have hs : count1757 q = (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) + (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99, -102, -103, -104, -107]) (l₂ := [-111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1727)) (literal (valuationOf q) (1750)) (literal (valuationOf q) (1761)) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) (count1757 q) 3 2 (meaning1727 q) (meaning1750 q) (meaning1761 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1761 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1858 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1750 = false ∨ valuation q 1761 = true := counterClause1858 (baseVal q)

theorem counterClause1859 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1762 = true := by
  have hs : count1757 q = (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) + (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99, -102, -103, -104, -107]) (l₂ := [-111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1727)) (literal (valuationOf q) (1751)) (literal (valuationOf q) (1762)) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) (count1757 q) 3 3 (meaning1727 q) (meaning1751 q) (meaning1762 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1859 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1751 = false ∨ valuation q 1762 = true := counterClause1859 (baseVal q)

theorem counterClause1860 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1763 = true := by
  have hs : count1757 q = (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) + (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99, -102, -103, -104, -107]) (l₂ := [-111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1727)) (literal (valuationOf q) (1752)) (literal (valuationOf q) (1763)) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) (count1757 q) 3 4 (meaning1727 q) (meaning1752 q) (meaning1763 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1763 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1860 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1752 = false ∨ valuation q 1763 = true := counterClause1860 (baseVal q)

theorem counterClause1861 (q : Nat → Bool) : valuationOf q 1727 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1764 = true := by
  have hs : count1757 q = (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) + (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99, -102, -103, -104, -107]) (l₂ := [-111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1727)) (literal (valuationOf q) (1753)) (literal (valuationOf q) (1764)) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) (count1757 q) 3 5 (meaning1727 q) (meaning1753 q) (meaning1764 q) hs
  change valuationOf q 1727 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1764 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1861 (q : Snake 81) (h : Conditions q) : valuation q 1727 = false ∨ valuation q 1753 = false ∨ valuation q 1764 = true := counterClause1861 (baseVal q)

theorem counterClause1862 (q : Nat → Bool) : valuationOf q 1728 = false ∨ valuationOf q 1760 = true := by
  have hs : count1757 q = (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) + (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99, -102, -103, -104, -107]) (l₂ := [-111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_left (literal (valuationOf q) (1728)) (literal (valuationOf q) (1760)) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) (count1757 q) 4 (meaning1728 q) (meaning1760 q) hs
  change valuationOf q 1728 = false ∨ valuationOf q 1760 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1862 (q : Snake 81) (h : Conditions q) : valuation q 1728 = false ∨ valuation q 1760 = true := counterClause1862 (baseVal q)

theorem counterClause1863 (q : Nat → Bool) : valuationOf q 1728 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1761 = true := by
  have hs : count1757 q = (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) + (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99, -102, -103, -104, -107]) (l₂ := [-111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1728)) (literal (valuationOf q) (1749)) (literal (valuationOf q) (1761)) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) (count1757 q) 4 1 (meaning1728 q) (meaning1749 q) (meaning1761 q) hs
  change valuationOf q 1728 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1761 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1863 (q : Snake 81) (h : Conditions q) : valuation q 1728 = false ∨ valuation q 1749 = false ∨ valuation q 1761 = true := counterClause1863 (baseVal q)

theorem counterClause1864 (q : Nat → Bool) : valuationOf q 1728 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1762 = true := by
  have hs : count1757 q = (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) + (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99, -102, -103, -104, -107]) (l₂ := [-111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1728)) (literal (valuationOf q) (1750)) (literal (valuationOf q) (1762)) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) (count1757 q) 4 2 (meaning1728 q) (meaning1750 q) (meaning1762 q) hs
  change valuationOf q 1728 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1864 (q : Snake 81) (h : Conditions q) : valuation q 1728 = false ∨ valuation q 1750 = false ∨ valuation q 1762 = true := counterClause1864 (baseVal q)

theorem counterClause1865 (q : Nat → Bool) : valuationOf q 1728 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1763 = true := by
  have hs : count1757 q = (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) + (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99, -102, -103, -104, -107]) (l₂ := [-111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1728)) (literal (valuationOf q) (1751)) (literal (valuationOf q) (1763)) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) (count1757 q) 4 3 (meaning1728 q) (meaning1751 q) (meaning1763 q) hs
  change valuationOf q 1728 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1763 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1865 (q : Snake 81) (h : Conditions q) : valuation q 1728 = false ∨ valuation q 1751 = false ∨ valuation q 1763 = true := counterClause1865 (baseVal q)

theorem counterClause1866 (q : Nat → Bool) : valuationOf q 1728 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1764 = true := by
  have hs : count1757 q = (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) + (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99, -102, -103, -104, -107]) (l₂ := [-111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1728)) (literal (valuationOf q) (1752)) (literal (valuationOf q) (1764)) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) (count1757 q) 4 4 (meaning1728 q) (meaning1752 q) (meaning1764 q) hs
  change valuationOf q 1728 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1764 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1866 (q : Snake 81) (h : Conditions q) : valuation q 1728 = false ∨ valuation q 1752 = false ∨ valuation q 1764 = true := counterClause1866 (baseVal q)

theorem counterClause1867 (q : Nat → Bool) : valuationOf q 1729 = false ∨ valuationOf q 1761 = true := by
  have hs : count1757 q = (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) + (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99, -102, -103, -104, -107]) (l₂ := [-111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_left (literal (valuationOf q) (1729)) (literal (valuationOf q) (1761)) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) (count1757 q) 5 (meaning1729 q) (meaning1761 q) hs
  change valuationOf q 1729 = false ∨ valuationOf q 1761 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1867 (q : Snake 81) (h : Conditions q) : valuation q 1729 = false ∨ valuation q 1761 = true := counterClause1867 (baseVal q)

theorem counterClause1868 (q : Nat → Bool) : valuationOf q 1729 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1762 = true := by
  have hs : count1757 q = (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) + (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99, -102, -103, -104, -107]) (l₂ := [-111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1729)) (literal (valuationOf q) (1749)) (literal (valuationOf q) (1762)) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) (count1757 q) 5 1 (meaning1729 q) (meaning1749 q) (meaning1762 q) hs
  change valuationOf q 1729 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1868 (q : Snake 81) (h : Conditions q) : valuation q 1729 = false ∨ valuation q 1749 = false ∨ valuation q 1762 = true := counterClause1868 (baseVal q)

theorem counterClause1869 (q : Nat → Bool) : valuationOf q 1729 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1763 = true := by
  have hs : count1757 q = (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) + (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99, -102, -103, -104, -107]) (l₂ := [-111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1729)) (literal (valuationOf q) (1750)) (literal (valuationOf q) (1763)) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) (count1757 q) 5 2 (meaning1729 q) (meaning1750 q) (meaning1763 q) hs
  change valuationOf q 1729 = false ∨ valuationOf q 1750 = false ∨ valuationOf q 1763 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1869 (q : Snake 81) (h : Conditions q) : valuation q 1729 = false ∨ valuation q 1750 = false ∨ valuation q 1763 = true := counterClause1869 (baseVal q)

theorem counterClause1870 (q : Nat → Bool) : valuationOf q 1729 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1764 = true := by
  have hs : count1757 q = (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) + (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99, -102, -103, -104, -107]) (l₂ := [-111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1729)) (literal (valuationOf q) (1751)) (literal (valuationOf q) (1764)) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) (count1757 q) 5 3 (meaning1729 q) (meaning1751 q) (meaning1764 q) hs
  change valuationOf q 1729 = false ∨ valuationOf q 1751 = false ∨ valuationOf q 1764 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1870 (q : Snake 81) (h : Conditions q) : valuation q 1729 = false ∨ valuation q 1751 = false ∨ valuation q 1764 = true := counterClause1870 (baseVal q)

theorem counterClause1871 (q : Nat → Bool) : valuationOf q 1729 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1765 = true := by
  have hs : count1757 q = (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) + (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99, -102, -103, -104, -107]) (l₂ := [-111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1729)) (literal (valuationOf q) (1752)) (literal (valuationOf q) (1765)) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) (count1757 q) 5 4 (meaning1729 q) (meaning1752 q) (meaning1765 q) hs
  change valuationOf q 1729 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1765 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1871 (q : Snake 81) (h : Conditions q) : valuation q 1729 = false ∨ valuation q 1752 = false ∨ valuation q 1765 = true := counterClause1871 (baseVal q)

theorem counterClause1872 (q : Nat → Bool) : valuationOf q 1730 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1763 = true := by
  have hs : count1757 q = (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) + (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -99, -102, -103, -104, -107]) (l₂ := [-111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1730)) (literal (valuationOf q) (1749)) (literal (valuationOf q) (1763)) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107]) (countLit q [-111, -113, -115, -117, -119, -120, -122, -123]) (count1757 q) 6 1 (meaning1730 q) (meaning1749 q) (meaning1763 q) hs
  change valuationOf q 1730 = false ∨ valuationOf q 1749 = false ∨ valuationOf q 1763 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1872 (q : Snake 81) (h : Conditions q) : valuation q 1730 = false ∨ valuation q 1749 = false ∨ valuation q 1763 = true := counterClause1872 (baseVal q)

theorem counterClause1873 (q : Nat → Bool) : valuationOf q 1695 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1779 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1695)) (literal (valuationOf q) (1761)) (literal (valuationOf q) (1779)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 2 5 (meaning1695 q) (meaning1761 q) (meaning1779 q) hs
  change valuationOf q 1695 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1779 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1873 (q : Snake 81) (h : Conditions q) : valuation q 1695 = false ∨ valuation q 1761 = false ∨ valuation q 1779 = true := counterClause1873 (baseVal q)

theorem counterClause1874 (q : Nat → Bool) : valuationOf q 1695 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1781 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1695)) (literal (valuationOf q) (1763)) (literal (valuationOf q) (1781)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 2 7 (meaning1695 q) (meaning1763 q) (meaning1781 q) hs
  change valuationOf q 1695 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1874 (q : Snake 81) (h : Conditions q) : valuation q 1695 = false ∨ valuation q 1763 = false ∨ valuation q 1781 = true := counterClause1874 (baseVal q)

theorem counterClause1875 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1779 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1696)) (literal (valuationOf q) (1760)) (literal (valuationOf q) (1779)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 3 4 (meaning1696 q) (meaning1760 q) (meaning1779 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1779 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1875 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1760 = false ∨ valuation q 1779 = true := counterClause1875 (baseVal q)

theorem counterClause1876 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1780 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1696)) (literal (valuationOf q) (1761)) (literal (valuationOf q) (1780)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 3 5 (meaning1696 q) (meaning1761 q) (meaning1780 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1876 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1761 = false ∨ valuation q 1780 = true := counterClause1876 (baseVal q)

theorem counterClause1877 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1781 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1696)) (literal (valuationOf q) (1762)) (literal (valuationOf q) (1781)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 3 6 (meaning1696 q) (meaning1762 q) (meaning1781 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1877 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1762 = false ∨ valuation q 1781 = true := counterClause1877 (baseVal q)

theorem counterClause1878 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1782 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1696)) (literal (valuationOf q) (1763)) (literal (valuationOf q) (1782)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 3 7 (meaning1696 q) (meaning1763 q) (meaning1782 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1782 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1878 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1763 = false ∨ valuation q 1782 = true := counterClause1878 (baseVal q)

theorem counterClause1879 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1783 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1696)) (literal (valuationOf q) (1764)) (literal (valuationOf q) (1783)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 3 8 (meaning1696 q) (meaning1764 q) (meaning1783 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1879 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1764 = false ∨ valuation q 1783 = true := counterClause1879 (baseVal q)

theorem counterClause1880 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1765 = false ∨ valuationOf q 1784 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1696)) (literal (valuationOf q) (1765)) (literal (valuationOf q) (1784)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 3 9 (meaning1696 q) (meaning1765 q) (meaning1784 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1765 = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1880 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1765 = false ∨ valuation q 1784 = true := counterClause1880 (baseVal q)

theorem counterClause1881 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1779 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1697)) (literal (valuationOf q) (1759)) (literal (valuationOf q) (1779)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 4 3 (meaning1697 q) (meaning1759 q) (meaning1779 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1779 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1881 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1759 = false ∨ valuation q 1779 = true := counterClause1881 (baseVal q)

theorem counterClause1882 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1780 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1697)) (literal (valuationOf q) (1760)) (literal (valuationOf q) (1780)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 4 4 (meaning1697 q) (meaning1760 q) (meaning1780 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1882 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1760 = false ∨ valuation q 1780 = true := counterClause1882 (baseVal q)

theorem counterClause1883 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1781 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1697)) (literal (valuationOf q) (1761)) (literal (valuationOf q) (1781)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 4 5 (meaning1697 q) (meaning1761 q) (meaning1781 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1883 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1761 = false ∨ valuation q 1781 = true := counterClause1883 (baseVal q)

theorem counterClause1884 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1782 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1697)) (literal (valuationOf q) (1762)) (literal (valuationOf q) (1782)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 4 6 (meaning1697 q) (meaning1762 q) (meaning1782 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1782 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1884 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1762 = false ∨ valuation q 1782 = true := counterClause1884 (baseVal q)

theorem counterClause1885 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1783 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1697)) (literal (valuationOf q) (1763)) (literal (valuationOf q) (1783)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 4 7 (meaning1697 q) (meaning1763 q) (meaning1783 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1885 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1763 = false ∨ valuation q 1783 = true := counterClause1885 (baseVal q)

theorem counterClause1886 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1784 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1697)) (literal (valuationOf q) (1764)) (literal (valuationOf q) (1784)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 4 8 (meaning1697 q) (meaning1764 q) (meaning1784 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1886 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1764 = false ∨ valuation q 1784 = true := counterClause1886 (baseVal q)

theorem counterClause1887 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1765 = false ∨ valuationOf q 1785 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1697)) (literal (valuationOf q) (1765)) (literal (valuationOf q) (1785)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 4 9 (meaning1697 q) (meaning1765 q) (meaning1785 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1765 = false ∨ valuationOf q 1785 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1887 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1765 = false ∨ valuation q 1785 = true := counterClause1887 (baseVal q)

theorem counterClause1888 (q : Nat → Bool) : valuationOf q 1698 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1780 = true := by
  have hs : count1773 q = (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) + (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (l₂ := [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1698)) (literal (valuationOf q) (1759)) (literal (valuationOf q) (1780)) (countLit q [-62, -64, -66, -67, -69, -72, -73, -75, -76, -79, -81, -85, -87, -89, -91]) (countLit q [-94, -96, -98, -99, -102, -103, -104, -107, -111, -113, -115, -117, -119, -120, -122, -123]) (count1773 q) 5 3 (meaning1698 q) (meaning1759 q) (meaning1780 q) hs
  change valuationOf q 1698 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1888 (q : Snake 81) (h : Conditions q) : valuation q 1698 = false ∨ valuation q 1759 = false ∨ valuation q 1780 = true := counterClause1888 (baseVal q)

theorem block58 (q : Snake 81) (h : Conditions q) : B112E089.Block58 (valuation q) :=
  ⟨clause1857 q h, clause1858 q h, clause1859 q h, clause1860 q h, clause1861 q h, clause1862 q h, clause1863 q h, clause1864 q h, clause1865 q h, clause1866 q h, clause1867 q h, clause1868 q h, clause1869 q h, clause1870 q h, clause1871 q h, clause1872 q h, clause1873 q h, clause1874 q h, clause1875 q h, clause1876 q h, clause1877 q h, clause1878 q h, clause1879 q h, clause1880 q h, clause1881 q h, clause1882 q h, clause1883 q h, clause1884 q h, clause1885 q h, clause1886 q h, clause1887 q h, clause1888 q h⟩

end
end Snake9.Regrowth.E112089
