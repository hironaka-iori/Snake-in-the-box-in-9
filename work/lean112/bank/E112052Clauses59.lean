import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec59 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1889 (q : Nat → Bool) : valuationOf q 1753 = false ∨ valuationOf q 1807 = false ∨ valuationOf q 1834 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1753)) (literal (valuationOf q) (1807)) (literal (valuationOf q) (1834)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 11 1 (meaning1753 q) (meaning1807 q) (meaning1834 q) hs
  change valuationOf q 1753 = false ∨ valuationOf q 1807 = false ∨ valuationOf q 1834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1889 (q : Snake 81) (h : Conditions q) : valuation q 1753 = false ∨ valuation q 1807 = false ∨ valuation q 1834 = true := counterClause1889 (baseVal q)

theorem counterClause1890 (q : Nat → Bool) : valuationOf q 1753 = false ∨ valuationOf q 1808 = false ∨ valuationOf q 1835 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1753)) (literal (valuationOf q) (1808)) (literal (valuationOf q) (1835)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 11 2 (meaning1753 q) (meaning1808 q) (meaning1835 q) hs
  change valuationOf q 1753 = false ∨ valuationOf q 1808 = false ∨ valuationOf q 1835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1890 (q : Snake 81) (h : Conditions q) : valuation q 1753 = false ∨ valuation q 1808 = false ∨ valuation q 1835 = true := counterClause1890 (baseVal q)

theorem counterClause1891 (q : Nat → Bool) : valuationOf q 1753 = false ∨ valuationOf q 1809 = false ∨ valuationOf q 1836 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1753)) (literal (valuationOf q) (1809)) (literal (valuationOf q) (1836)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 11 3 (meaning1753 q) (meaning1809 q) (meaning1836 q) hs
  change valuationOf q 1753 = false ∨ valuationOf q 1809 = false ∨ valuationOf q 1836 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1891 (q : Snake 81) (h : Conditions q) : valuation q 1753 = false ∨ valuation q 1809 = false ∨ valuation q 1836 = true := counterClause1891 (baseVal q)

theorem counterClause1892 (q : Nat → Bool) : valuationOf q 1753 = false ∨ valuationOf q 1810 = false ∨ valuationOf q 1837 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1753)) (literal (valuationOf q) (1810)) (literal (valuationOf q) (1837)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 11 4 (meaning1753 q) (meaning1810 q) (meaning1837 q) hs
  change valuationOf q 1753 = false ∨ valuationOf q 1810 = false ∨ valuationOf q 1837 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1892 (q : Snake 81) (h : Conditions q) : valuation q 1753 = false ∨ valuation q 1810 = false ∨ valuation q 1837 = true := counterClause1892 (baseVal q)

theorem counterClause1893 (q : Nat → Bool) : valuationOf q 1753 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1838 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1753)) (literal (valuationOf q) (1811)) (literal (valuationOf q) (1838)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 11 5 (meaning1753 q) (meaning1811 q) (meaning1838 q) hs
  change valuationOf q 1753 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1838 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1893 (q : Snake 81) (h : Conditions q) : valuation q 1753 = false ∨ valuation q 1811 = false ∨ valuation q 1838 = true := counterClause1893 (baseVal q)

theorem counterClause1894 (q : Nat → Bool) : valuationOf q 1753 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1839 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1753)) (literal (valuationOf q) (1812)) (literal (valuationOf q) (1839)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 11 6 (meaning1753 q) (meaning1812 q) (meaning1839 q) hs
  change valuationOf q 1753 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1839 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1894 (q : Snake 81) (h : Conditions q) : valuation q 1753 = false ∨ valuation q 1812 = false ∨ valuation q 1839 = true := counterClause1894 (baseVal q)

theorem counterClause1895 (q : Nat → Bool) : valuationOf q 1753 = false ∨ valuationOf q 1813 = false ∨ valuationOf q 1840 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1753)) (literal (valuationOf q) (1813)) (literal (valuationOf q) (1840)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 11 7 (meaning1753 q) (meaning1813 q) (meaning1840 q) hs
  change valuationOf q 1753 = false ∨ valuationOf q 1813 = false ∨ valuationOf q 1840 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1895 (q : Snake 81) (h : Conditions q) : valuation q 1753 = false ∨ valuation q 1813 = false ∨ valuation q 1840 = true := counterClause1895 (baseVal q)

theorem counterClause1896 (q : Nat → Bool) : valuationOf q 1754 = false ∨ valuationOf q 1834 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_left (literal (valuationOf q) (1754)) (literal (valuationOf q) (1834)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 12 (meaning1754 q) (meaning1834 q) hs
  change valuationOf q 1754 = false ∨ valuationOf q 1834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1896 (q : Snake 81) (h : Conditions q) : valuation q 1754 = false ∨ valuation q 1834 = true := counterClause1896 (baseVal q)

theorem counterClause1897 (q : Nat → Bool) : valuationOf q 1754 = false ∨ valuationOf q 1808 = false ∨ valuationOf q 1836 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1754)) (literal (valuationOf q) (1808)) (literal (valuationOf q) (1836)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 12 2 (meaning1754 q) (meaning1808 q) (meaning1836 q) hs
  change valuationOf q 1754 = false ∨ valuationOf q 1808 = false ∨ valuationOf q 1836 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1897 (q : Snake 81) (h : Conditions q) : valuation q 1754 = false ∨ valuation q 1808 = false ∨ valuation q 1836 = true := counterClause1897 (baseVal q)

theorem counterClause1898 (q : Nat → Bool) : valuationOf q 1754 = false ∨ valuationOf q 1809 = false ∨ valuationOf q 1837 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1754)) (literal (valuationOf q) (1809)) (literal (valuationOf q) (1837)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 12 3 (meaning1754 q) (meaning1809 q) (meaning1837 q) hs
  change valuationOf q 1754 = false ∨ valuationOf q 1809 = false ∨ valuationOf q 1837 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1898 (q : Snake 81) (h : Conditions q) : valuation q 1754 = false ∨ valuation q 1809 = false ∨ valuation q 1837 = true := counterClause1898 (baseVal q)

theorem counterClause1899 (q : Nat → Bool) : valuationOf q 1754 = false ∨ valuationOf q 1810 = false ∨ valuationOf q 1838 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1754)) (literal (valuationOf q) (1810)) (literal (valuationOf q) (1838)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 12 4 (meaning1754 q) (meaning1810 q) (meaning1838 q) hs
  change valuationOf q 1754 = false ∨ valuationOf q 1810 = false ∨ valuationOf q 1838 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1899 (q : Snake 81) (h : Conditions q) : valuation q 1754 = false ∨ valuation q 1810 = false ∨ valuation q 1838 = true := counterClause1899 (baseVal q)

theorem counterClause1900 (q : Nat → Bool) : valuationOf q 1754 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1839 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1754)) (literal (valuationOf q) (1811)) (literal (valuationOf q) (1839)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 12 5 (meaning1754 q) (meaning1811 q) (meaning1839 q) hs
  change valuationOf q 1754 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1839 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1900 (q : Snake 81) (h : Conditions q) : valuation q 1754 = false ∨ valuation q 1811 = false ∨ valuation q 1839 = true := counterClause1900 (baseVal q)

theorem counterClause1901 (q : Nat → Bool) : valuationOf q 1754 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1840 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1754)) (literal (valuationOf q) (1812)) (literal (valuationOf q) (1840)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 12 6 (meaning1754 q) (meaning1812 q) (meaning1840 q) hs
  change valuationOf q 1754 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1840 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1901 (q : Snake 81) (h : Conditions q) : valuation q 1754 = false ∨ valuation q 1812 = false ∨ valuation q 1840 = true := counterClause1901 (baseVal q)

theorem counterClause1902 (q : Nat → Bool) : valuationOf q 1754 = false ∨ valuationOf q 1813 = false ∨ valuationOf q 1841 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1754)) (literal (valuationOf q) (1813)) (literal (valuationOf q) (1841)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 12 7 (meaning1754 q) (meaning1813 q) (meaning1841 q) hs
  change valuationOf q 1754 = false ∨ valuationOf q 1813 = false ∨ valuationOf q 1841 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1902 (q : Snake 81) (h : Conditions q) : valuation q 1754 = false ∨ valuation q 1813 = false ∨ valuation q 1841 = true := counterClause1902 (baseVal q)

theorem counterClause1903 (q : Nat → Bool) : valuationOf q 1755 = false ∨ valuationOf q 1807 = false ∨ valuationOf q 1836 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1755)) (literal (valuationOf q) (1807)) (literal (valuationOf q) (1836)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 13 1 (meaning1755 q) (meaning1807 q) (meaning1836 q) hs
  change valuationOf q 1755 = false ∨ valuationOf q 1807 = false ∨ valuationOf q 1836 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1903 (q : Snake 81) (h : Conditions q) : valuation q 1755 = false ∨ valuation q 1807 = false ∨ valuation q 1836 = true := counterClause1903 (baseVal q)

theorem counterClause1904 (q : Nat → Bool) : valuationOf q 1755 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1840 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1755)) (literal (valuationOf q) (1811)) (literal (valuationOf q) (1840)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 13 5 (meaning1755 q) (meaning1811 q) (meaning1840 q) hs
  change valuationOf q 1755 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1840 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1904 (q : Snake 81) (h : Conditions q) : valuation q 1755 = false ∨ valuation q 1811 = false ∨ valuation q 1840 = true := counterClause1904 (baseVal q)

theorem counterClause1905 (q : Nat → Bool) : valuationOf q 1755 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1841 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1755)) (literal (valuationOf q) (1812)) (literal (valuationOf q) (1841)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 13 6 (meaning1755 q) (meaning1812 q) (meaning1841 q) hs
  change valuationOf q 1755 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1841 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1905 (q : Snake 81) (h : Conditions q) : valuation q 1755 = false ∨ valuation q 1812 = false ∨ valuation q 1841 = true := counterClause1905 (baseVal q)

theorem counterClause1906 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1841 = false ∨ valuationOf q 1870 = true := by
  have hs : count1847 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) + (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (l₂ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1675)) (literal (valuationOf q) (1841)) (literal (valuationOf q) (1870)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1847 q) 5 19 (meaning1675 q) (meaning1841 q) (meaning1870 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1841 = false ∨ valuationOf q 1870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1906 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1841 = false ∨ valuation q 1870 = true := counterClause1906 (baseVal q)

theorem counterClause1907 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1840 = false ∨ valuationOf q 1870 = true := by
  have hs : count1847 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) + (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (l₂ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1676)) (literal (valuationOf q) (1840)) (literal (valuationOf q) (1870)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1847 q) 6 18 (meaning1676 q) (meaning1840 q) (meaning1870 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1840 = false ∨ valuationOf q 1870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1907 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1840 = false ∨ valuation q 1870 = true := counterClause1907 (baseVal q)

theorem counterClause1908 (q : Nat → Bool) : valuationOf q 1677 = false ∨ valuationOf q 1839 = false ∨ valuationOf q 1870 = true := by
  have hs : count1847 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) + (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (l₂ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1677)) (literal (valuationOf q) (1839)) (literal (valuationOf q) (1870)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1847 q) 7 17 (meaning1677 q) (meaning1839 q) (meaning1870 q) hs
  change valuationOf q 1677 = false ∨ valuationOf q 1839 = false ∨ valuationOf q 1870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1908 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1839 = false ∨ valuation q 1870 = true := counterClause1908 (baseVal q)

theorem counterClause1909 (q : Nat → Bool) : valuationOf q 1678 = false ∨ valuationOf q 1838 = false ∨ valuationOf q 1870 = true := by
  have hs : count1847 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) + (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (l₂ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1678)) (literal (valuationOf q) (1838)) (literal (valuationOf q) (1870)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1847 q) 8 16 (meaning1678 q) (meaning1838 q) (meaning1870 q) hs
  change valuationOf q 1678 = false ∨ valuationOf q 1838 = false ∨ valuationOf q 1870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1909 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1838 = false ∨ valuation q 1870 = true := counterClause1909 (baseVal q)

theorem counterClause1910 (q : Nat → Bool) : valuationOf q 1679 = false ∨ valuationOf q 1837 = false ∨ valuationOf q 1870 = true := by
  have hs : count1847 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) + (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (l₂ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1679)) (literal (valuationOf q) (1837)) (literal (valuationOf q) (1870)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1847 q) 9 15 (meaning1679 q) (meaning1837 q) (meaning1870 q) hs
  change valuationOf q 1679 = false ∨ valuationOf q 1837 = false ∨ valuationOf q 1870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1910 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1837 = false ∨ valuation q 1870 = true := counterClause1910 (baseVal q)

theorem counterClause1911 (q : Nat → Bool) : valuationOf q 1680 = false ∨ valuationOf q 1836 = false ∨ valuationOf q 1870 = true := by
  have hs : count1847 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) + (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (l₂ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1680)) (literal (valuationOf q) (1836)) (literal (valuationOf q) (1870)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1847 q) 10 14 (meaning1680 q) (meaning1836 q) (meaning1870 q) hs
  change valuationOf q 1680 = false ∨ valuationOf q 1836 = false ∨ valuationOf q 1870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1911 (q : Snake 81) (h : Conditions q) : valuation q 1680 = false ∨ valuation q 1836 = false ∨ valuation q 1870 = true := counterClause1911 (baseVal q)

theorem counterClause1912 (q : Nat → Bool) : valuationOf q 1681 = false ∨ valuationOf q 1835 = false ∨ valuationOf q 1870 = true := by
  have hs : count1847 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) + (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (l₂ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1681)) (literal (valuationOf q) (1835)) (literal (valuationOf q) (1870)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1847 q) 11 13 (meaning1681 q) (meaning1835 q) (meaning1870 q) hs
  change valuationOf q 1681 = false ∨ valuationOf q 1835 = false ∨ valuationOf q 1870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1912 (q : Snake 81) (h : Conditions q) : valuation q 1681 = false ∨ valuation q 1835 = false ∨ valuation q 1870 = true := counterClause1912 (baseVal q)

theorem counterClause1913 (q : Nat → Bool) : valuationOf q 1682 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1870 = true := by
  have hs : count1847 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) + (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (l₂ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1682)) (literal (valuationOf q) (1834)) (literal (valuationOf q) (1870)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1847 q) 12 12 (meaning1682 q) (meaning1834 q) (meaning1870 q) hs
  change valuationOf q 1682 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1913 (q : Snake 81) (h : Conditions q) : valuation q 1682 = false ∨ valuation q 1834 = false ∨ valuation q 1870 = true := counterClause1913 (baseVal q)

theorem counterClause1914 (q : Nat → Bool) : valuationOf q 1683 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1870 = true := by
  have hs : count1847 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) + (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (l₂ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1683)) (literal (valuationOf q) (1833)) (literal (valuationOf q) (1870)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1847 q) 13 11 (meaning1683 q) (meaning1833 q) (meaning1870 q) hs
  change valuationOf q 1683 = false ∨ valuationOf q 1833 = false ∨ valuationOf q 1870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1914 (q : Snake 81) (h : Conditions q) : valuation q 1683 = false ∨ valuation q 1833 = false ∨ valuation q 1870 = true := counterClause1914 (baseVal q)

theorem counterClause1915 (q : Nat → Bool) : valuationOf q 1684 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1870 = true := by
  have hs : count1847 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) + (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (l₂ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1684)) (literal (valuationOf q) (1832)) (literal (valuationOf q) (1870)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1847 q) 14 10 (meaning1684 q) (meaning1832 q) (meaning1870 q) hs
  change valuationOf q 1684 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1915 (q : Snake 81) (h : Conditions q) : valuation q 1684 = false ∨ valuation q 1832 = false ∨ valuation q 1870 = true := counterClause1915 (baseVal q)

theorem counterClause1916 (q : Nat → Bool) : valuationOf q 1685 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1870 = true := by
  have hs : count1847 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) + (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (l₂ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1685)) (literal (valuationOf q) (1831)) (literal (valuationOf q) (1870)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1847 q) 15 9 (meaning1685 q) (meaning1831 q) (meaning1870 q) hs
  change valuationOf q 1685 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1916 (q : Snake 81) (h : Conditions q) : valuation q 1685 = false ∨ valuation q 1831 = false ∨ valuation q 1870 = true := counterClause1916 (baseVal q)

theorem counterClause1917 (q : Nat → Bool) : valuationOf q 1686 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1870 = true := by
  have hs : count1847 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) + (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (l₂ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1686)) (literal (valuationOf q) (1830)) (literal (valuationOf q) (1870)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1847 q) 16 8 (meaning1686 q) (meaning1830 q) (meaning1870 q) hs
  change valuationOf q 1686 = false ∨ valuationOf q 1830 = false ∨ valuationOf q 1870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1917 (q : Snake 81) (h : Conditions q) : valuation q 1686 = false ∨ valuation q 1830 = false ∨ valuation q 1870 = true := counterClause1917 (baseVal q)

theorem counterClause1918 (q : Nat → Bool) : valuationOf q 1687 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1870 = true := by
  have hs : count1847 q = (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) + (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (l₂ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1687)) (literal (valuationOf q) (1829)) (literal (valuationOf q) (1870)) (countLit q [-1, -3, -5, -7, -8, -10, -11, -12, -15, -17, -18, -20, -24, -25, -27, -28, -30, -33, -35, -36, -39, -42, -43, -45, -46, -51, -53, -54, -56, -60, -62, -63]) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95, -96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1847 q) 17 7 (meaning1687 q) (meaning1829 q) (meaning1870 q) hs
  change valuationOf q 1687 = false ∨ valuationOf q 1829 = false ∨ valuationOf q 1870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1918 (q : Snake 81) (h : Conditions q) : valuation q 1687 = false ∨ valuation q 1829 = false ∨ valuation q 1870 = true := counterClause1918 (baseVal q)

theorem clause1919 (q : Snake 81) (h : Conditions q) : valuation q 1870 = false := by
  rw [value1870]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1847 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1920 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 25 = false ∨ valuation q 26 = false := by
  rw [value14, value15, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (130 : Vertex) (131 : Vertex) (146 : Vertex) (147 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block59 (q : Snake 81) (h : Conditions q) : B112E052.Block59 (valuation q) :=
  ⟨clause1889 q h, clause1890 q h, clause1891 q h, clause1892 q h, clause1893 q h, clause1894 q h, clause1895 q h, clause1896 q h, clause1897 q h, clause1898 q h, clause1899 q h, clause1900 q h, clause1901 q h, clause1902 q h, clause1903 q h, clause1904 q h, clause1905 q h, clause1906 q h, clause1907 q h, clause1908 q h, clause1909 q h, clause1910 q h, clause1911 q h, clause1912 q h, clause1913 q h, clause1914 q h, clause1915 q h, clause1916 q h, clause1917 q h, clause1918 q h, clause1919 q h, clause1920 q h⟩

end
end Snake9.Regrowth.E112052
