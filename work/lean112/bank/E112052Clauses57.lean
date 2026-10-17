import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec57 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1825 (q : Nat → Bool) : valuationOf q 1780 = false ∨ valuationOf q 1800 = false ∨ valuationOf q 1814 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1780)) (literal (valuationOf q) (1800)) (literal (valuationOf q) (1814)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 6 2 (meaning1780 q) (meaning1800 q) (meaning1814 q) hs
  change valuationOf q 1780 = false ∨ valuationOf q 1800 = false ∨ valuationOf q 1814 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1825 (q : Snake 81) (h : Conditions q) : valuation q 1780 = false ∨ valuation q 1800 = false ∨ valuation q 1814 = true := counterClause1825 (baseVal q)

theorem counterClause1826 (q : Nat → Bool) : valuationOf q 1780 = false ∨ valuationOf q 1801 = false ∨ valuationOf q 1815 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1780)) (literal (valuationOf q) (1801)) (literal (valuationOf q) (1815)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 6 3 (meaning1780 q) (meaning1801 q) (meaning1815 q) hs
  change valuationOf q 1780 = false ∨ valuationOf q 1801 = false ∨ valuationOf q 1815 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1826 (q : Snake 81) (h : Conditions q) : valuation q 1780 = false ∨ valuation q 1801 = false ∨ valuation q 1815 = true := counterClause1826 (baseVal q)

theorem counterClause1827 (q : Nat → Bool) : valuationOf q 1780 = false ∨ valuationOf q 1802 = false ∨ valuationOf q 1816 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1780)) (literal (valuationOf q) (1802)) (literal (valuationOf q) (1816)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 6 4 (meaning1780 q) (meaning1802 q) (meaning1816 q) hs
  change valuationOf q 1780 = false ∨ valuationOf q 1802 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1827 (q : Snake 81) (h : Conditions q) : valuation q 1780 = false ∨ valuation q 1802 = false ∨ valuation q 1816 = true := counterClause1827 (baseVal q)

theorem counterClause1828 (q : Nat → Bool) : valuationOf q 1780 = false ∨ valuationOf q 1803 = false ∨ valuationOf q 1817 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1780)) (literal (valuationOf q) (1803)) (literal (valuationOf q) (1817)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 6 5 (meaning1780 q) (meaning1803 q) (meaning1817 q) hs
  change valuationOf q 1780 = false ∨ valuationOf q 1803 = false ∨ valuationOf q 1817 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1828 (q : Snake 81) (h : Conditions q) : valuation q 1780 = false ∨ valuation q 1803 = false ∨ valuation q 1817 = true := counterClause1828 (baseVal q)

theorem counterClause1829 (q : Nat → Bool) : valuationOf q 1781 = false ∨ valuationOf q 1813 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_left (literal (valuationOf q) (1781)) (literal (valuationOf q) (1813)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 7 (meaning1781 q) (meaning1813 q) hs
  change valuationOf q 1781 = false ∨ valuationOf q 1813 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1829 (q : Snake 81) (h : Conditions q) : valuation q 1781 = false ∨ valuation q 1813 = true := counterClause1829 (baseVal q)

theorem counterClause1830 (q : Nat → Bool) : valuationOf q 1781 = false ∨ valuationOf q 1799 = false ∨ valuationOf q 1814 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1781)) (literal (valuationOf q) (1799)) (literal (valuationOf q) (1814)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 7 1 (meaning1781 q) (meaning1799 q) (meaning1814 q) hs
  change valuationOf q 1781 = false ∨ valuationOf q 1799 = false ∨ valuationOf q 1814 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1830 (q : Snake 81) (h : Conditions q) : valuation q 1781 = false ∨ valuation q 1799 = false ∨ valuation q 1814 = true := counterClause1830 (baseVal q)

theorem counterClause1831 (q : Nat → Bool) : valuationOf q 1781 = false ∨ valuationOf q 1800 = false ∨ valuationOf q 1815 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1781)) (literal (valuationOf q) (1800)) (literal (valuationOf q) (1815)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 7 2 (meaning1781 q) (meaning1800 q) (meaning1815 q) hs
  change valuationOf q 1781 = false ∨ valuationOf q 1800 = false ∨ valuationOf q 1815 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1831 (q : Snake 81) (h : Conditions q) : valuation q 1781 = false ∨ valuation q 1800 = false ∨ valuation q 1815 = true := counterClause1831 (baseVal q)

theorem counterClause1832 (q : Nat → Bool) : valuationOf q 1781 = false ∨ valuationOf q 1801 = false ∨ valuationOf q 1816 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1781)) (literal (valuationOf q) (1801)) (literal (valuationOf q) (1816)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 7 3 (meaning1781 q) (meaning1801 q) (meaning1816 q) hs
  change valuationOf q 1781 = false ∨ valuationOf q 1801 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1832 (q : Snake 81) (h : Conditions q) : valuation q 1781 = false ∨ valuation q 1801 = false ∨ valuation q 1816 = true := counterClause1832 (baseVal q)

theorem counterClause1833 (q : Nat → Bool) : valuationOf q 1781 = false ∨ valuationOf q 1802 = false ∨ valuationOf q 1817 = true := by
  have hs : count1807 q = (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) + (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-96, -99, -100, -102, -103, -107, -108, -110]) (l₂ := [-112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1781)) (literal (valuationOf q) (1802)) (literal (valuationOf q) (1817)) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110]) (countLit q [-112, -114, -118, -120, -122, -123, -126, -127]) (count1807 q) 7 4 (meaning1781 q) (meaning1802 q) (meaning1817 q) hs
  change valuationOf q 1781 = false ∨ valuationOf q 1802 = false ∨ valuationOf q 1817 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1833 (q : Snake 81) (h : Conditions q) : valuation q 1781 = false ∨ valuation q 1802 = false ∨ valuation q 1817 = true := counterClause1833 (baseVal q)

theorem counterClause1834 (q : Nat → Bool) : valuationOf q 1745 = false ∨ valuationOf q 1813 = false ∨ valuationOf q 1832 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1745)) (literal (valuationOf q) (1813)) (literal (valuationOf q) (1832)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 3 7 (meaning1745 q) (meaning1813 q) (meaning1832 q) hs
  change valuationOf q 1745 = false ∨ valuationOf q 1813 = false ∨ valuationOf q 1832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1834 (q : Snake 81) (h : Conditions q) : valuation q 1745 = false ∨ valuation q 1813 = false ∨ valuation q 1832 = true := counterClause1834 (baseVal q)

theorem counterClause1835 (q : Nat → Bool) : valuationOf q 1745 = false ∨ valuationOf q 1815 = false ∨ valuationOf q 1834 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1745)) (literal (valuationOf q) (1815)) (literal (valuationOf q) (1834)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 3 9 (meaning1745 q) (meaning1815 q) (meaning1834 q) hs
  change valuationOf q 1745 = false ∨ valuationOf q 1815 = false ∨ valuationOf q 1834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1835 (q : Snake 81) (h : Conditions q) : valuation q 1745 = false ∨ valuation q 1815 = false ∨ valuation q 1834 = true := counterClause1835 (baseVal q)

theorem counterClause1836 (q : Nat → Bool) : valuationOf q 1745 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1835 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1745)) (literal (valuationOf q) (1816)) (literal (valuationOf q) (1835)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 3 10 (meaning1745 q) (meaning1816 q) (meaning1835 q) hs
  change valuationOf q 1745 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1836 (q : Snake 81) (h : Conditions q) : valuation q 1745 = false ∨ valuation q 1816 = false ∨ valuation q 1835 = true := counterClause1836 (baseVal q)

theorem counterClause1837 (q : Nat → Bool) : valuationOf q 1746 = false ∨ valuationOf q 1809 = false ∨ valuationOf q 1829 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1746)) (literal (valuationOf q) (1809)) (literal (valuationOf q) (1829)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 4 3 (meaning1746 q) (meaning1809 q) (meaning1829 q) hs
  change valuationOf q 1746 = false ∨ valuationOf q 1809 = false ∨ valuationOf q 1829 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1837 (q : Snake 81) (h : Conditions q) : valuation q 1746 = false ∨ valuation q 1809 = false ∨ valuation q 1829 = true := counterClause1837 (baseVal q)

theorem counterClause1838 (q : Nat → Bool) : valuationOf q 1746 = false ∨ valuationOf q 1810 = false ∨ valuationOf q 1830 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1746)) (literal (valuationOf q) (1810)) (literal (valuationOf q) (1830)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 4 4 (meaning1746 q) (meaning1810 q) (meaning1830 q) hs
  change valuationOf q 1746 = false ∨ valuationOf q 1810 = false ∨ valuationOf q 1830 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1838 (q : Snake 81) (h : Conditions q) : valuation q 1746 = false ∨ valuation q 1810 = false ∨ valuation q 1830 = true := counterClause1838 (baseVal q)

theorem counterClause1839 (q : Nat → Bool) : valuationOf q 1746 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1831 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1746)) (literal (valuationOf q) (1811)) (literal (valuationOf q) (1831)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 4 5 (meaning1746 q) (meaning1811 q) (meaning1831 q) hs
  change valuationOf q 1746 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1839 (q : Snake 81) (h : Conditions q) : valuation q 1746 = false ∨ valuation q 1811 = false ∨ valuation q 1831 = true := counterClause1839 (baseVal q)

theorem counterClause1840 (q : Nat → Bool) : valuationOf q 1746 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1832 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1746)) (literal (valuationOf q) (1812)) (literal (valuationOf q) (1832)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 4 6 (meaning1746 q) (meaning1812 q) (meaning1832 q) hs
  change valuationOf q 1746 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1840 (q : Snake 81) (h : Conditions q) : valuation q 1746 = false ∨ valuation q 1812 = false ∨ valuation q 1832 = true := counterClause1840 (baseVal q)

theorem counterClause1841 (q : Nat → Bool) : valuationOf q 1746 = false ∨ valuationOf q 1813 = false ∨ valuationOf q 1833 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1746)) (literal (valuationOf q) (1813)) (literal (valuationOf q) (1833)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 4 7 (meaning1746 q) (meaning1813 q) (meaning1833 q) hs
  change valuationOf q 1746 = false ∨ valuationOf q 1813 = false ∨ valuationOf q 1833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1841 (q : Snake 81) (h : Conditions q) : valuation q 1746 = false ∨ valuation q 1813 = false ∨ valuation q 1833 = true := counterClause1841 (baseVal q)

theorem counterClause1842 (q : Nat → Bool) : valuationOf q 1746 = false ∨ valuationOf q 1814 = false ∨ valuationOf q 1834 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1746)) (literal (valuationOf q) (1814)) (literal (valuationOf q) (1834)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 4 8 (meaning1746 q) (meaning1814 q) (meaning1834 q) hs
  change valuationOf q 1746 = false ∨ valuationOf q 1814 = false ∨ valuationOf q 1834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1842 (q : Snake 81) (h : Conditions q) : valuation q 1746 = false ∨ valuation q 1814 = false ∨ valuation q 1834 = true := counterClause1842 (baseVal q)

theorem counterClause1843 (q : Nat → Bool) : valuationOf q 1746 = false ∨ valuationOf q 1815 = false ∨ valuationOf q 1835 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1746)) (literal (valuationOf q) (1815)) (literal (valuationOf q) (1835)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 4 9 (meaning1746 q) (meaning1815 q) (meaning1835 q) hs
  change valuationOf q 1746 = false ∨ valuationOf q 1815 = false ∨ valuationOf q 1835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1843 (q : Snake 81) (h : Conditions q) : valuation q 1746 = false ∨ valuation q 1815 = false ∨ valuation q 1835 = true := counterClause1843 (baseVal q)

theorem counterClause1844 (q : Nat → Bool) : valuationOf q 1746 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1836 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1746)) (literal (valuationOf q) (1816)) (literal (valuationOf q) (1836)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 4 10 (meaning1746 q) (meaning1816 q) (meaning1836 q) hs
  change valuationOf q 1746 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1836 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1844 (q : Snake 81) (h : Conditions q) : valuation q 1746 = false ∨ valuation q 1816 = false ∨ valuation q 1836 = true := counterClause1844 (baseVal q)

theorem counterClause1845 (q : Nat → Bool) : valuationOf q 1746 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1837 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1746)) (literal (valuationOf q) (1817)) (literal (valuationOf q) (1837)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 4 11 (meaning1746 q) (meaning1817 q) (meaning1837 q) hs
  change valuationOf q 1746 = false ∨ valuationOf q 1817 = false ∨ valuationOf q 1837 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1845 (q : Snake 81) (h : Conditions q) : valuation q 1746 = false ∨ valuation q 1817 = false ∨ valuation q 1837 = true := counterClause1845 (baseVal q)

theorem counterClause1846 (q : Nat → Bool) : valuationOf q 1747 = false ∨ valuationOf q 1810 = false ∨ valuationOf q 1831 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1747)) (literal (valuationOf q) (1810)) (literal (valuationOf q) (1831)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 5 4 (meaning1747 q) (meaning1810 q) (meaning1831 q) hs
  change valuationOf q 1747 = false ∨ valuationOf q 1810 = false ∨ valuationOf q 1831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1846 (q : Snake 81) (h : Conditions q) : valuation q 1747 = false ∨ valuation q 1810 = false ∨ valuation q 1831 = true := counterClause1846 (baseVal q)

theorem counterClause1847 (q : Nat → Bool) : valuationOf q 1747 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1832 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1747)) (literal (valuationOf q) (1811)) (literal (valuationOf q) (1832)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 5 5 (meaning1747 q) (meaning1811 q) (meaning1832 q) hs
  change valuationOf q 1747 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1847 (q : Snake 81) (h : Conditions q) : valuation q 1747 = false ∨ valuation q 1811 = false ∨ valuation q 1832 = true := counterClause1847 (baseVal q)

theorem counterClause1848 (q : Nat → Bool) : valuationOf q 1747 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1833 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1747)) (literal (valuationOf q) (1812)) (literal (valuationOf q) (1833)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 5 6 (meaning1747 q) (meaning1812 q) (meaning1833 q) hs
  change valuationOf q 1747 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1848 (q : Snake 81) (h : Conditions q) : valuation q 1747 = false ∨ valuation q 1812 = false ∨ valuation q 1833 = true := counterClause1848 (baseVal q)

theorem counterClause1849 (q : Nat → Bool) : valuationOf q 1747 = false ∨ valuationOf q 1813 = false ∨ valuationOf q 1834 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1747)) (literal (valuationOf q) (1813)) (literal (valuationOf q) (1834)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 5 7 (meaning1747 q) (meaning1813 q) (meaning1834 q) hs
  change valuationOf q 1747 = false ∨ valuationOf q 1813 = false ∨ valuationOf q 1834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1849 (q : Snake 81) (h : Conditions q) : valuation q 1747 = false ∨ valuation q 1813 = false ∨ valuation q 1834 = true := counterClause1849 (baseVal q)

theorem counterClause1850 (q : Nat → Bool) : valuationOf q 1747 = false ∨ valuationOf q 1814 = false ∨ valuationOf q 1835 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1747)) (literal (valuationOf q) (1814)) (literal (valuationOf q) (1835)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 5 8 (meaning1747 q) (meaning1814 q) (meaning1835 q) hs
  change valuationOf q 1747 = false ∨ valuationOf q 1814 = false ∨ valuationOf q 1835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1850 (q : Snake 81) (h : Conditions q) : valuation q 1747 = false ∨ valuation q 1814 = false ∨ valuation q 1835 = true := counterClause1850 (baseVal q)

theorem counterClause1851 (q : Nat → Bool) : valuationOf q 1747 = false ∨ valuationOf q 1815 = false ∨ valuationOf q 1836 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1747)) (literal (valuationOf q) (1815)) (literal (valuationOf q) (1836)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 5 9 (meaning1747 q) (meaning1815 q) (meaning1836 q) hs
  change valuationOf q 1747 = false ∨ valuationOf q 1815 = false ∨ valuationOf q 1836 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1851 (q : Snake 81) (h : Conditions q) : valuation q 1747 = false ∨ valuation q 1815 = false ∨ valuation q 1836 = true := counterClause1851 (baseVal q)

theorem counterClause1852 (q : Nat → Bool) : valuationOf q 1747 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1837 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1747)) (literal (valuationOf q) (1816)) (literal (valuationOf q) (1837)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 5 10 (meaning1747 q) (meaning1816 q) (meaning1837 q) hs
  change valuationOf q 1747 = false ∨ valuationOf q 1816 = false ∨ valuationOf q 1837 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1852 (q : Snake 81) (h : Conditions q) : valuation q 1747 = false ∨ valuation q 1816 = false ∨ valuation q 1837 = true := counterClause1852 (baseVal q)

theorem counterClause1853 (q : Nat → Bool) : valuationOf q 1748 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1833 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1748)) (literal (valuationOf q) (1811)) (literal (valuationOf q) (1833)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 6 5 (meaning1748 q) (meaning1811 q) (meaning1833 q) hs
  change valuationOf q 1748 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1853 (q : Snake 81) (h : Conditions q) : valuation q 1748 = false ∨ valuation q 1811 = false ∨ valuation q 1833 = true := counterClause1853 (baseVal q)

theorem counterClause1854 (q : Nat → Bool) : valuationOf q 1748 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1834 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1748)) (literal (valuationOf q) (1812)) (literal (valuationOf q) (1834)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 6 6 (meaning1748 q) (meaning1812 q) (meaning1834 q) hs
  change valuationOf q 1748 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1854 (q : Snake 81) (h : Conditions q) : valuation q 1748 = false ∨ valuation q 1812 = false ∨ valuation q 1834 = true := counterClause1854 (baseVal q)

theorem counterClause1855 (q : Nat → Bool) : valuationOf q 1748 = false ∨ valuationOf q 1813 = false ∨ valuationOf q 1835 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1748)) (literal (valuationOf q) (1813)) (literal (valuationOf q) (1835)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 6 7 (meaning1748 q) (meaning1813 q) (meaning1835 q) hs
  change valuationOf q 1748 = false ∨ valuationOf q 1813 = false ∨ valuationOf q 1835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1855 (q : Snake 81) (h : Conditions q) : valuation q 1748 = false ∨ valuation q 1813 = false ∨ valuation q 1835 = true := counterClause1855 (baseVal q)

theorem counterClause1856 (q : Nat → Bool) : valuationOf q 1748 = false ∨ valuationOf q 1814 = false ∨ valuationOf q 1836 = true := by
  have hs : count1823 q = (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) + (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (l₂ := [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127])
  have hm := merge_two (literal (valuationOf q) (1748)) (literal (valuationOf q) (1814)) (literal (valuationOf q) (1836)) (countLit q [-65, -67, -68, -71, -72, -77, -78, -81, -82, -84, -86, -87, -90, -91, -94, -95]) (countLit q [-96, -99, -100, -102, -103, -107, -108, -110, -112, -114, -118, -120, -122, -123, -126, -127]) (count1823 q) 6 8 (meaning1748 q) (meaning1814 q) (meaning1836 q) hs
  change valuationOf q 1748 = false ∨ valuationOf q 1814 = false ∨ valuationOf q 1836 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1856 (q : Snake 81) (h : Conditions q) : valuation q 1748 = false ∨ valuation q 1814 = false ∨ valuation q 1836 = true := counterClause1856 (baseVal q)

theorem block57 (q : Snake 81) (h : Conditions q) : B112E052.Block57 (valuation q) :=
  ⟨clause1825 q h, clause1826 q h, clause1827 q h, clause1828 q h, clause1829 q h, clause1830 q h, clause1831 q h, clause1832 q h, clause1833 q h, clause1834 q h, clause1835 q h, clause1836 q h, clause1837 q h, clause1838 q h, clause1839 q h, clause1840 q h, clause1841 q h, clause1842 q h, clause1843 q h, clause1844 q h, clause1845 q h, clause1846 q h, clause1847 q h, clause1848 q h, clause1849 q h, clause1850 q h, clause1851 q h, clause1852 q h, clause1853 q h, clause1854 q h, clause1855 q h, clause1856 q h⟩

end
end Snake9.Regrowth.E112052
