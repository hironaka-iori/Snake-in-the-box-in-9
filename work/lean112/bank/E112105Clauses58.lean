import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec58 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1857 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1785 = false ∨ valuationOf q 1816 = true := by
  have hs : count1796 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31, -33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) + (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93, -95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31, -33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (l₂ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93, -95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1785)) (literal (valuationOf q) (1816)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31, -33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93, -95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1796 q) 10 11 (meaning1640 q) (meaning1785 q) (meaning1816 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1785 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1857 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1785 = false ∨ valuation q 1816 = true := counterClause1857 (baseVal q)

theorem counterClause1858 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1784 = false ∨ valuationOf q 1816 = true := by
  have hs : count1796 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31, -33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) + (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93, -95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31, -33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (l₂ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93, -95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1641)) (literal (valuationOf q) (1784)) (literal (valuationOf q) (1816)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31, -33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93, -95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1796 q) 11 10 (meaning1641 q) (meaning1784 q) (meaning1816 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1784 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1858 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1784 = false ∨ valuation q 1816 = true := counterClause1858 (baseVal q)

theorem counterClause1859 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1783 = false ∨ valuationOf q 1816 = true := by
  have hs : count1796 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31, -33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) + (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93, -95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31, -33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (l₂ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93, -95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1642)) (literal (valuationOf q) (1783)) (literal (valuationOf q) (1816)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31, -33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93, -95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1796 q) 12 9 (meaning1642 q) (meaning1783 q) (meaning1816 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1783 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1859 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1783 = false ∨ valuation q 1816 = true := counterClause1859 (baseVal q)

theorem counterClause1860 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1782 = false ∨ valuationOf q 1816 = true := by
  have hs : count1796 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31, -33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) + (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93, -95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31, -33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (l₂ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93, -95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1643)) (literal (valuationOf q) (1782)) (literal (valuationOf q) (1816)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31, -33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93, -95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1796 q) 13 8 (meaning1643 q) (meaning1782 q) (meaning1816 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1782 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1860 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1782 = false ∨ valuation q 1816 = true := counterClause1860 (baseVal q)

theorem counterClause1861 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1781 = false ∨ valuationOf q 1816 = true := by
  have hs : count1796 q = (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31, -33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) + (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93, -95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31, -33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (l₂ := [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93, -95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1644)) (literal (valuationOf q) (1781)) (literal (valuationOf q) (1816)) (countLit q [-2, -4, -6, -7, -10, -13, -16, -17, -20, -22, -23, -25, -27, -28, -31, -33, -35, -37, -40, -41, -44, -45, -48, -49, -52, -54, -56, -59, -60, -61]) (countLit q [-64, -66, -68, -71, -72, -74, -76, -78, -81, -83, -85, -88, -89, -91, -93, -95, -98, -99, -101, -102, -105, -106, -107, -108, -110, -113, -115, -116, -117, -122, -123]) (count1796 q) 14 7 (meaning1644 q) (meaning1781 q) (meaning1816 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1781 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1861 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1781 = false ∨ valuation q 1816 = true := counterClause1861 (baseVal q)

theorem clause1862 (q : Snake 81) (h : Conditions q) : valuation q 1816 = false := by
  rw [value1816]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1796 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1863 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 14 = false ∨ valuation q 32 = false ∨ valuation q 49 = false := by
  rw [value2, value14, value32, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (4 : Vertex) (68 : Vertex) (132 : Vertex) (196 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1864 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 17 = false ∨ valuation q 49 = false ∨ valuation q 55 = false := by
  rw [value14, value17, value49, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (68 : Vertex) (76 : Vertex) (196 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1865 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 20 = false ∨ valuation q 71 = false ∨ valuation q 75 = false := by
  rw [value15, value20, value71, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (71 : Vertex) (79 : Vertex) (327 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1866 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 19 = false ∨ valuation q 20 = false := by
  rw [value17, value18, value19, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (76 : Vertex) (77 : Vertex) (78 : Vertex) (79 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1867 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 20 = false ∨ valuation q 27 = false ∨ valuation q 29 = false := by
  rw [value18, value20, value27, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (77 : Vertex) (79 : Vertex) (93 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1868 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 20 = false ∨ valuation q 56 = false ∨ valuation q 57 = false := by
  rw [value19, value20, value56, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (78 : Vertex) (79 : Vertex) (206 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1869 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 20 = false ∨ valuation q 74 = false ∨ valuation q 75 = false := by
  rw [value19, value20, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (78 : Vertex) (79 : Vertex) (334 : Vertex) (335 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1870 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 56 = false ∨ valuation q 74 = false ∨ valuation q 112 = false := by
  rw [value19, value56, value74, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (78 : Vertex) (206 : Vertex) (334 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1871 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 24 = false := by
  rw [value21, value22, value23, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (80 : Vertex) (81 : Vertex) (82 : Vertex) (83 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1872 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 31 = false ∨ valuation q 35 = false ∨ valuation q 36 = false := by
  rw [value30, value31, value35, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (129 : Vertex) (131 : Vertex) (137 : Vertex) (139 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1873 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 37 = false ∨ valuation q 38 = false := by
  rw [value32, value33, value37, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (132 : Vertex) (133 : Vertex) (140 : Vertex) (141 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1874 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 37 = false ∨ valuation q 49 = false ∨ valuation q 55 = false := by
  rw [value32, value37, value49, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (132 : Vertex) (140 : Vertex) (196 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1875 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 42 = false ∨ valuation q 43 = false ∨ valuation q 45 = false := by
  rw [value41, value42, value43, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (146 : Vertex) (150 : Vertex) (154 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1876 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 51 = false := by
  rw [value47, value48, value49, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (192 : Vertex) (194 : Vertex) (196 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1877 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 48 = false ∨ valuation q 52 = false ∨ valuation q 53 = false := by
  rw [value47, value48, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (192 : Vertex) (194 : Vertex) (200 : Vertex) (202 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1878 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 48 = false ∨ valuation q 102 = false ∨ valuation q 104 = false := by
  rw [value47, value48, value102, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (192 : Vertex) (194 : Vertex) (448 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1879 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 49 = false ∨ valuation q 52 = false ∨ valuation q 55 = false := by
  rw [value47, value49, value52, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (192 : Vertex) (196 : Vertex) (200 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1880 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 51 = false ∨ valuation q 53 = false ∨ valuation q 56 = false := by
  rw [value48, value51, value53, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (194 : Vertex) (198 : Vertex) (202 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1881 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 51 = false ∨ valuation q 104 = false ∨ valuation q 107 = false := by
  rw [value48, value51, value104, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (194 : Vertex) (198 : Vertex) (450 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1882 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 51 = false ∨ valuation q 55 = false ∨ valuation q 56 = false := by
  rw [value49, value51, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (196 : Vertex) (198 : Vertex) (204 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1883 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 60 = false ∨ valuation q 106 = false ∨ valuation q 118 = false := by
  rw [value50, value60, value106, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (197 : Vertex) (213 : Vertex) (453 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1884 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 56 = false ∨ valuation q 107 = false ∨ valuation q 112 = false := by
  rw [value51, value56, value107, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (198 : Vertex) (206 : Vertex) (454 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1885 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 55 = false ∨ valuation q 56 = false := by
  rw [value52, value53, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (200 : Vertex) (202 : Vertex) (204 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1886 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 55 = false ∨ valuation q 63 = false ∨ valuation q 66 = false := by
  rw [value52, value55, value63, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (200 : Vertex) (204 : Vertex) (216 : Vertex) (220 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1887 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 56 = false ∨ valuation q 110 = false ∨ valuation q 112 = false := by
  rw [value55, value56, value110, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (204 : Vertex) (206 : Vertex) (460 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1888 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 66 = false ∨ valuation q 110 = false ∨ valuation q 121 = false := by
  rw [value55, value66, value110, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (204 : Vertex) (220 : Vertex) (460 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block58 (q : Snake 81) (h : Conditions q) : B112E105.Block58 (valuation q) :=
  ⟨clause1857 q h, clause1858 q h, clause1859 q h, clause1860 q h, clause1861 q h, clause1862 q h, clause1863 q h, clause1864 q h, clause1865 q h, clause1866 q h, clause1867 q h, clause1868 q h, clause1869 q h, clause1870 q h, clause1871 q h, clause1872 q h, clause1873 q h, clause1874 q h, clause1875 q h, clause1876 q h, clause1877 q h, clause1878 q h, clause1879 q h, clause1880 q h, clause1881 q h, clause1882 q h, clause1883 q h, clause1884 q h, clause1885 q h, clause1886 q h, clause1887 q h, clause1888 q h⟩

end
end Snake9.Regrowth.E112105
