import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec58 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1857 (q : Nat → Bool) : valuationOf q 1748 = false ∨ valuationOf q 1815 = false ∨ valuationOf q 1837 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1748)) (literal (valuationOf q) (1815)) (literal (valuationOf q) (1837)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 6 9 (meaning1748 q) (meaning1815 q) (meaning1837 q) hs
  change valuationOf q 1748 = false ∨ valuationOf q 1815 = false ∨ valuationOf q 1837 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1857 (q : Snake 81) (h : Conditions q) : valuation q 1748 = false ∨ valuation q 1815 = false ∨ valuation q 1837 = true := counterClause1857 (baseVal q)

theorem counterClause1858 (q : Nat → Bool) : valuationOf q 1749 = false ∨ valuationOf q 1810 = false ∨ valuationOf q 1833 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1749)) (literal (valuationOf q) (1810)) (literal (valuationOf q) (1833)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 7 4 (meaning1749 q) (meaning1810 q) (meaning1833 q) hs
  change valuationOf q 1749 = false ∨ valuationOf q 1810 = false ∨ valuationOf q 1833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1858 (q : Snake 81) (h : Conditions q) : valuation q 1749 = false ∨ valuation q 1810 = false ∨ valuation q 1833 = true := counterClause1858 (baseVal q)

theorem counterClause1859 (q : Nat → Bool) : valuationOf q 1749 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1834 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1749)) (literal (valuationOf q) (1811)) (literal (valuationOf q) (1834)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 7 5 (meaning1749 q) (meaning1811 q) (meaning1834 q) hs
  change valuationOf q 1749 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1859 (q : Snake 81) (h : Conditions q) : valuation q 1749 = false ∨ valuation q 1811 = false ∨ valuation q 1834 = true := counterClause1859 (baseVal q)

theorem counterClause1860 (q : Nat → Bool) : valuationOf q 1749 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1835 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1749)) (literal (valuationOf q) (1812)) (literal (valuationOf q) (1835)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 7 6 (meaning1749 q) (meaning1812 q) (meaning1835 q) hs
  change valuationOf q 1749 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1860 (q : Snake 81) (h : Conditions q) : valuation q 1749 = false ∨ valuation q 1812 = false ∨ valuation q 1835 = true := counterClause1860 (baseVal q)

theorem counterClause1861 (q : Nat → Bool) : valuationOf q 1749 = false ∨ valuationOf q 1813 = false ∨ valuationOf q 1836 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1749)) (literal (valuationOf q) (1813)) (literal (valuationOf q) (1836)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 7 7 (meaning1749 q) (meaning1813 q) (meaning1836 q) hs
  change valuationOf q 1749 = false ∨ valuationOf q 1813 = false ∨ valuationOf q 1836 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1861 (q : Snake 81) (h : Conditions q) : valuation q 1749 = false ∨ valuation q 1813 = false ∨ valuation q 1836 = true := counterClause1861 (baseVal q)

theorem counterClause1862 (q : Nat → Bool) : valuationOf q 1749 = false ∨ valuationOf q 1814 = false ∨ valuationOf q 1837 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1749)) (literal (valuationOf q) (1814)) (literal (valuationOf q) (1837)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 7 8 (meaning1749 q) (meaning1814 q) (meaning1837 q) hs
  change valuationOf q 1749 = false ∨ valuationOf q 1814 = false ∨ valuationOf q 1837 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1862 (q : Snake 81) (h : Conditions q) : valuation q 1749 = false ∨ valuation q 1814 = false ∨ valuation q 1837 = true := counterClause1862 (baseVal q)

theorem counterClause1863 (q : Nat → Bool) : valuationOf q 1749 = false ∨ valuationOf q 1815 = false ∨ valuationOf q 1838 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1749)) (literal (valuationOf q) (1815)) (literal (valuationOf q) (1838)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 7 9 (meaning1749 q) (meaning1815 q) (meaning1838 q) hs
  change valuationOf q 1749 = false ∨ valuationOf q 1815 = false ∨ valuationOf q 1838 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1863 (q : Snake 81) (h : Conditions q) : valuation q 1749 = false ∨ valuation q 1815 = false ∨ valuation q 1838 = true := counterClause1863 (baseVal q)

theorem counterClause1864 (q : Nat → Bool) : valuationOf q 1749 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1839 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1749)) (literal (valuationOf q) (1816)) (literal (valuationOf q) (1839)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 7 10 (meaning1749 q) (meaning1816 q) (meaning1839 q) hs
  change valuationOf q 1749 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1839 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1864 (q : Snake 81) (h : Conditions q) : valuation q 1749 = false ∨ valuation q 1816 = false ∨ valuation q 1839 = true := counterClause1864 (baseVal q)

theorem counterClause1865 (q : Nat → Bool) : valuationOf q 1750 = false ∨ valuationOf q 1808 = false ∨ valuationOf q 1832 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1750)) (literal (valuationOf q) (1808)) (literal (valuationOf q) (1832)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 8 2 (meaning1750 q) (meaning1808 q) (meaning1832 q) hs
  change valuationOf q 1750 = false ∨ valuationOf q 1808 = false ∨ valuationOf q 1832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1865 (q : Snake 81) (h : Conditions q) : valuation q 1750 = false ∨ valuation q 1808 = false ∨ valuation q 1832 = true := counterClause1865 (baseVal q)

theorem counterClause1866 (q : Nat → Bool) : valuationOf q 1750 = false ∨ valuationOf q 1809 = false ∨ valuationOf q 1833 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1750)) (literal (valuationOf q) (1809)) (literal (valuationOf q) (1833)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 8 3 (meaning1750 q) (meaning1809 q) (meaning1833 q) hs
  change valuationOf q 1750 = false ∨ valuationOf q 1809 = false ∨ valuationOf q 1833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1866 (q : Snake 81) (h : Conditions q) : valuation q 1750 = false ∨ valuation q 1809 = false ∨ valuation q 1833 = true := counterClause1866 (baseVal q)

theorem counterClause1867 (q : Nat → Bool) : valuationOf q 1750 = false ∨ valuationOf q 1810 = false ∨ valuationOf q 1834 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1750)) (literal (valuationOf q) (1810)) (literal (valuationOf q) (1834)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 8 4 (meaning1750 q) (meaning1810 q) (meaning1834 q) hs
  change valuationOf q 1750 = false ∨ valuationOf q 1810 = false ∨ valuationOf q 1834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1867 (q : Snake 81) (h : Conditions q) : valuation q 1750 = false ∨ valuation q 1810 = false ∨ valuation q 1834 = true := counterClause1867 (baseVal q)

theorem counterClause1868 (q : Nat → Bool) : valuationOf q 1750 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1835 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1750)) (literal (valuationOf q) (1811)) (literal (valuationOf q) (1835)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 8 5 (meaning1750 q) (meaning1811 q) (meaning1835 q) hs
  change valuationOf q 1750 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1868 (q : Snake 81) (h : Conditions q) : valuation q 1750 = false ∨ valuation q 1811 = false ∨ valuation q 1835 = true := counterClause1868 (baseVal q)

theorem counterClause1869 (q : Nat → Bool) : valuationOf q 1750 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1836 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1750)) (literal (valuationOf q) (1812)) (literal (valuationOf q) (1836)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 8 6 (meaning1750 q) (meaning1812 q) (meaning1836 q) hs
  change valuationOf q 1750 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1836 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1869 (q : Snake 81) (h : Conditions q) : valuation q 1750 = false ∨ valuation q 1812 = false ∨ valuation q 1836 = true := counterClause1869 (baseVal q)

theorem counterClause1870 (q : Nat → Bool) : valuationOf q 1750 = false ∨ valuationOf q 1813 = false ∨ valuationOf q 1837 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1750)) (literal (valuationOf q) (1813)) (literal (valuationOf q) (1837)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 8 7 (meaning1750 q) (meaning1813 q) (meaning1837 q) hs
  change valuationOf q 1750 = false ∨ valuationOf q 1813 = false ∨ valuationOf q 1837 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1870 (q : Snake 81) (h : Conditions q) : valuation q 1750 = false ∨ valuation q 1813 = false ∨ valuation q 1837 = true := counterClause1870 (baseVal q)

theorem counterClause1871 (q : Nat → Bool) : valuationOf q 1750 = false ∨ valuationOf q 1814 = false ∨ valuationOf q 1838 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1750)) (literal (valuationOf q) (1814)) (literal (valuationOf q) (1838)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 8 8 (meaning1750 q) (meaning1814 q) (meaning1838 q) hs
  change valuationOf q 1750 = false ∨ valuationOf q 1814 = false ∨ valuationOf q 1838 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1871 (q : Snake 81) (h : Conditions q) : valuation q 1750 = false ∨ valuation q 1814 = false ∨ valuation q 1838 = true := counterClause1871 (baseVal q)

theorem counterClause1872 (q : Nat → Bool) : valuationOf q 1750 = false ∨ valuationOf q 1815 = false ∨ valuationOf q 1839 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1750)) (literal (valuationOf q) (1815)) (literal (valuationOf q) (1839)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 8 9 (meaning1750 q) (meaning1815 q) (meaning1839 q) hs
  change valuationOf q 1750 = false ∨ valuationOf q 1815 = false ∨ valuationOf q 1839 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1872 (q : Snake 81) (h : Conditions q) : valuation q 1750 = false ∨ valuation q 1815 = false ∨ valuation q 1839 = true := counterClause1872 (baseVal q)

theorem counterClause1873 (q : Nat → Bool) : valuationOf q 1751 = false ∨ valuationOf q 1808 = false ∨ valuationOf q 1833 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1751)) (literal (valuationOf q) (1808)) (literal (valuationOf q) (1833)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 9 2 (meaning1751 q) (meaning1808 q) (meaning1833 q) hs
  change valuationOf q 1751 = false ∨ valuationOf q 1808 = false ∨ valuationOf q 1833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1873 (q : Snake 81) (h : Conditions q) : valuation q 1751 = false ∨ valuation q 1808 = false ∨ valuation q 1833 = true := counterClause1873 (baseVal q)

theorem counterClause1874 (q : Nat → Bool) : valuationOf q 1751 = false ∨ valuationOf q 1809 = false ∨ valuationOf q 1834 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1751)) (literal (valuationOf q) (1809)) (literal (valuationOf q) (1834)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 9 3 (meaning1751 q) (meaning1809 q) (meaning1834 q) hs
  change valuationOf q 1751 = false ∨ valuationOf q 1809 = false ∨ valuationOf q 1834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1874 (q : Snake 81) (h : Conditions q) : valuation q 1751 = false ∨ valuation q 1809 = false ∨ valuation q 1834 = true := counterClause1874 (baseVal q)

theorem counterClause1875 (q : Nat → Bool) : valuationOf q 1751 = false ∨ valuationOf q 1810 = false ∨ valuationOf q 1835 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1751)) (literal (valuationOf q) (1810)) (literal (valuationOf q) (1835)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 9 4 (meaning1751 q) (meaning1810 q) (meaning1835 q) hs
  change valuationOf q 1751 = false ∨ valuationOf q 1810 = false ∨ valuationOf q 1835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1875 (q : Snake 81) (h : Conditions q) : valuation q 1751 = false ∨ valuation q 1810 = false ∨ valuation q 1835 = true := counterClause1875 (baseVal q)

theorem counterClause1876 (q : Nat → Bool) : valuationOf q 1751 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1836 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1751)) (literal (valuationOf q) (1811)) (literal (valuationOf q) (1836)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 9 5 (meaning1751 q) (meaning1811 q) (meaning1836 q) hs
  change valuationOf q 1751 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1836 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1876 (q : Snake 81) (h : Conditions q) : valuation q 1751 = false ∨ valuation q 1811 = false ∨ valuation q 1836 = true := counterClause1876 (baseVal q)

theorem counterClause1877 (q : Nat → Bool) : valuationOf q 1751 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1837 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1751)) (literal (valuationOf q) (1812)) (literal (valuationOf q) (1837)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 9 6 (meaning1751 q) (meaning1812 q) (meaning1837 q) hs
  change valuationOf q 1751 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1837 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1877 (q : Snake 81) (h : Conditions q) : valuation q 1751 = false ∨ valuation q 1812 = false ∨ valuation q 1837 = true := counterClause1877 (baseVal q)

theorem counterClause1878 (q : Nat → Bool) : valuationOf q 1751 = false ∨ valuationOf q 1813 = false ∨ valuationOf q 1838 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1751)) (literal (valuationOf q) (1813)) (literal (valuationOf q) (1838)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 9 7 (meaning1751 q) (meaning1813 q) (meaning1838 q) hs
  change valuationOf q 1751 = false ∨ valuationOf q 1813 = false ∨ valuationOf q 1838 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1878 (q : Snake 81) (h : Conditions q) : valuation q 1751 = false ∨ valuation q 1813 = false ∨ valuation q 1838 = true := counterClause1878 (baseVal q)

theorem counterClause1879 (q : Nat → Bool) : valuationOf q 1751 = false ∨ valuationOf q 1814 = false ∨ valuationOf q 1839 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1751)) (literal (valuationOf q) (1814)) (literal (valuationOf q) (1839)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 9 8 (meaning1751 q) (meaning1814 q) (meaning1839 q) hs
  change valuationOf q 1751 = false ∨ valuationOf q 1814 = false ∨ valuationOf q 1839 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1879 (q : Snake 81) (h : Conditions q) : valuation q 1751 = false ∨ valuation q 1814 = false ∨ valuation q 1839 = true := counterClause1879 (baseVal q)

theorem counterClause1880 (q : Nat → Bool) : valuationOf q 1751 = false ∨ valuationOf q 1815 = false ∨ valuationOf q 1840 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1751)) (literal (valuationOf q) (1815)) (literal (valuationOf q) (1840)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 9 9 (meaning1751 q) (meaning1815 q) (meaning1840 q) hs
  change valuationOf q 1751 = false ∨ valuationOf q 1815 = false ∨ valuationOf q 1840 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1880 (q : Snake 81) (h : Conditions q) : valuation q 1751 = false ∨ valuation q 1815 = false ∨ valuation q 1840 = true := counterClause1880 (baseVal q)

theorem counterClause1881 (q : Nat → Bool) : valuationOf q 1752 = false ∨ valuationOf q 1832 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_left (literal (valuationOf q) (1752)) (literal (valuationOf q) (1832)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 10 (meaning1752 q) (meaning1832 q) hs
  change valuationOf q 1752 = false ∨ valuationOf q 1832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1881 (q : Snake 81) (h : Conditions q) : valuation q 1752 = false ∨ valuation q 1832 = true := counterClause1881 (baseVal q)

theorem counterClause1882 (q : Nat → Bool) : valuationOf q 1752 = false ∨ valuationOf q 1808 = false ∨ valuationOf q 1834 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1752)) (literal (valuationOf q) (1808)) (literal (valuationOf q) (1834)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 10 2 (meaning1752 q) (meaning1808 q) (meaning1834 q) hs
  change valuationOf q 1752 = false ∨ valuationOf q 1808 = false ∨ valuationOf q 1834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1882 (q : Snake 81) (h : Conditions q) : valuation q 1752 = false ∨ valuation q 1808 = false ∨ valuation q 1834 = true := counterClause1882 (baseVal q)

theorem counterClause1883 (q : Nat → Bool) : valuationOf q 1752 = false ∨ valuationOf q 1809 = false ∨ valuationOf q 1835 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1752)) (literal (valuationOf q) (1809)) (literal (valuationOf q) (1835)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 10 3 (meaning1752 q) (meaning1809 q) (meaning1835 q) hs
  change valuationOf q 1752 = false ∨ valuationOf q 1809 = false ∨ valuationOf q 1835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1883 (q : Snake 81) (h : Conditions q) : valuation q 1752 = false ∨ valuation q 1809 = false ∨ valuation q 1835 = true := counterClause1883 (baseVal q)

theorem counterClause1884 (q : Nat → Bool) : valuationOf q 1752 = false ∨ valuationOf q 1810 = false ∨ valuationOf q 1836 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1752)) (literal (valuationOf q) (1810)) (literal (valuationOf q) (1836)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 10 4 (meaning1752 q) (meaning1810 q) (meaning1836 q) hs
  change valuationOf q 1752 = false ∨ valuationOf q 1810 = false ∨ valuationOf q 1836 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1884 (q : Snake 81) (h : Conditions q) : valuation q 1752 = false ∨ valuation q 1810 = false ∨ valuation q 1836 = true := counterClause1884 (baseVal q)

theorem counterClause1885 (q : Nat → Bool) : valuationOf q 1752 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1837 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1752)) (literal (valuationOf q) (1811)) (literal (valuationOf q) (1837)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 10 5 (meaning1752 q) (meaning1811 q) (meaning1837 q) hs
  change valuationOf q 1752 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1837 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1885 (q : Snake 81) (h : Conditions q) : valuation q 1752 = false ∨ valuation q 1811 = false ∨ valuation q 1837 = true := counterClause1885 (baseVal q)

theorem counterClause1886 (q : Nat → Bool) : valuationOf q 1752 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1838 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1752)) (literal (valuationOf q) (1812)) (literal (valuationOf q) (1838)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 10 6 (meaning1752 q) (meaning1812 q) (meaning1838 q) hs
  change valuationOf q 1752 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1838 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1886 (q : Snake 81) (h : Conditions q) : valuation q 1752 = false ∨ valuation q 1812 = false ∨ valuation q 1838 = true := counterClause1886 (baseVal q)

theorem counterClause1887 (q : Nat → Bool) : valuationOf q 1752 = false ∨ valuationOf q 1813 = false ∨ valuationOf q 1839 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1752)) (literal (valuationOf q) (1813)) (literal (valuationOf q) (1839)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 10 7 (meaning1752 q) (meaning1813 q) (meaning1839 q) hs
  change valuationOf q 1752 = false ∨ valuationOf q 1813 = false ∨ valuationOf q 1839 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1887 (q : Snake 81) (h : Conditions q) : valuation q 1752 = false ∨ valuation q 1813 = false ∨ valuation q 1839 = true := counterClause1887 (baseVal q)

theorem counterClause1888 (q : Nat → Bool) : valuationOf q 1752 = false ∨ valuationOf q 1814 = false ∨ valuationOf q 1840 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1752)) (literal (valuationOf q) (1814)) (literal (valuationOf q) (1840)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 10 8 (meaning1752 q) (meaning1814 q) (meaning1840 q) hs
  change valuationOf q 1752 = false ∨ valuationOf q 1814 = false ∨ valuationOf q 1840 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1888 (q : Snake 81) (h : Conditions q) : valuation q 1752 = false ∨ valuation q 1814 = false ∨ valuation q 1840 = true := counterClause1888 (baseVal q)

theorem block58 (q : Snake 81) (h : Conditions q) : B112E052.Block58 (valuation q) :=
  ⟨clause1857 q h, clause1858 q h, clause1859 q h, clause1860 q h, clause1861 q h, clause1862 q h, clause1863 q h, clause1864 q h, clause1865 q h, clause1866 q h, clause1867 q h, clause1868 q h, clause1869 q h, clause1870 q h, clause1871 q h, clause1872 q h, clause1873 q h, clause1874 q h, clause1875 q h, clause1876 q h, clause1877 q h, clause1878 q h, clause1879 q h, clause1880 q h, clause1881 q h, clause1882 q h, clause1883 q h, clause1884 q h, clause1885 q h, clause1886 q h, clause1887 q h, clause1888 q h⟩

end
end Snake9.Regrowth.E112052
