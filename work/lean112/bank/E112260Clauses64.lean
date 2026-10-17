import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec64 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause2049 (q : Nat → Bool) : valuationOf q 1773 = false ∨ valuationOf q 1799 = false ∨ valuationOf q 1813 = true := by
  have hs : count1806 q = (countLit q [-95, -97, -99, -101, -102, -104, -106, -107]) + (countLit q [-109, -112, -114, -116, -118, -120, -121, -123, -125]) := List.countP_append (p := literal q) (l₁ := [-95, -97, -99, -101, -102, -104, -106, -107]) (l₂ := [-109, -112, -114, -116, -118, -120, -121, -123, -125])
  have hm := merge_two (literal (valuationOf q) (1773)) (literal (valuationOf q) (1799)) (literal (valuationOf q) (1813)) (countLit q [-95, -97, -99, -101, -102, -104, -106, -107]) (countLit q [-109, -112, -114, -116, -118, -120, -121, -123, -125]) (count1806 q) 5 3 (meaning1773 q) (meaning1799 q) (meaning1813 q) hs
  change valuationOf q 1773 = false ∨ valuationOf q 1799 = false ∨ valuationOf q 1813 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2049 (q : Snake 81) (h : Conditions q) : valuation q 1773 = false ∨ valuation q 1799 = false ∨ valuation q 1813 = true := counterClause2049 (baseVal q)

theorem counterClause2050 (q : Nat → Bool) : valuationOf q 1741 = false ∨ valuationOf q 1809 = false ∨ valuationOf q 1831 = true := by
  have hs : count1823 q = (countLit q [-63, -66, -70, -71, -75, -77, -78, -80, -83, -84, -87, -88, -91, -92, -93, -94]) + (countLit q [-95, -97, -99, -101, -102, -104, -106, -107, -109, -112, -114, -116, -118, -120, -121, -123, -125]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -70, -71, -75, -77, -78, -80, -83, -84, -87, -88, -91, -92, -93, -94]) (l₂ := [-95, -97, -99, -101, -102, -104, -106, -107, -109, -112, -114, -116, -118, -120, -121, -123, -125])
  have hm := merge_two (literal (valuationOf q) (1741)) (literal (valuationOf q) (1809)) (literal (valuationOf q) (1831)) (countLit q [-63, -66, -70, -71, -75, -77, -78, -80, -83, -84, -87, -88, -91, -92, -93, -94]) (countLit q [-95, -97, -99, -101, -102, -104, -106, -107, -109, -112, -114, -116, -118, -120, -121, -123, -125]) (count1823 q) 5 4 (meaning1741 q) (meaning1809 q) (meaning1831 q) hs
  change valuationOf q 1741 = false ∨ valuationOf q 1809 = false ∨ valuationOf q 1831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2050 (q : Snake 81) (h : Conditions q) : valuation q 1741 = false ∨ valuation q 1809 = false ∨ valuation q 1831 = true := counterClause2050 (baseVal q)

theorem counterClause2051 (q : Nat → Bool) : valuationOf q 1742 = false ∨ valuationOf q 1809 = false ∨ valuationOf q 1832 = true := by
  have hs : count1823 q = (countLit q [-63, -66, -70, -71, -75, -77, -78, -80, -83, -84, -87, -88, -91, -92, -93, -94]) + (countLit q [-95, -97, -99, -101, -102, -104, -106, -107, -109, -112, -114, -116, -118, -120, -121, -123, -125]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -70, -71, -75, -77, -78, -80, -83, -84, -87, -88, -91, -92, -93, -94]) (l₂ := [-95, -97, -99, -101, -102, -104, -106, -107, -109, -112, -114, -116, -118, -120, -121, -123, -125])
  have hm := merge_two (literal (valuationOf q) (1742)) (literal (valuationOf q) (1809)) (literal (valuationOf q) (1832)) (countLit q [-63, -66, -70, -71, -75, -77, -78, -80, -83, -84, -87, -88, -91, -92, -93, -94]) (countLit q [-95, -97, -99, -101, -102, -104, -106, -107, -109, -112, -114, -116, -118, -120, -121, -123, -125]) (count1823 q) 6 4 (meaning1742 q) (meaning1809 q) (meaning1832 q) hs
  change valuationOf q 1742 = false ∨ valuationOf q 1809 = false ∨ valuationOf q 1832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2051 (q : Snake 81) (h : Conditions q) : valuation q 1742 = false ∨ valuation q 1809 = false ∨ valuation q 1832 = true := counterClause2051 (baseVal q)

theorem counterClause2052 (q : Nat → Bool) : valuationOf q 1742 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1834 = true := by
  have hs : count1823 q = (countLit q [-63, -66, -70, -71, -75, -77, -78, -80, -83, -84, -87, -88, -91, -92, -93, -94]) + (countLit q [-95, -97, -99, -101, -102, -104, -106, -107, -109, -112, -114, -116, -118, -120, -121, -123, -125]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -70, -71, -75, -77, -78, -80, -83, -84, -87, -88, -91, -92, -93, -94]) (l₂ := [-95, -97, -99, -101, -102, -104, -106, -107, -109, -112, -114, -116, -118, -120, -121, -123, -125])
  have hm := merge_two (literal (valuationOf q) (1742)) (literal (valuationOf q) (1811)) (literal (valuationOf q) (1834)) (countLit q [-63, -66, -70, -71, -75, -77, -78, -80, -83, -84, -87, -88, -91, -92, -93, -94]) (countLit q [-95, -97, -99, -101, -102, -104, -106, -107, -109, -112, -114, -116, -118, -120, -121, -123, -125]) (count1823 q) 6 6 (meaning1742 q) (meaning1811 q) (meaning1834 q) hs
  change valuationOf q 1742 = false ∨ valuationOf q 1811 = false ∨ valuationOf q 1834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2052 (q : Snake 81) (h : Conditions q) : valuation q 1742 = false ∨ valuation q 1811 = false ∨ valuation q 1834 = true := counterClause2052 (baseVal q)

theorem counterClause2053 (q : Nat → Bool) : valuationOf q 1744 = false ∨ valuationOf q 1813 = false ∨ valuationOf q 1838 = true := by
  have hs : count1823 q = (countLit q [-63, -66, -70, -71, -75, -77, -78, -80, -83, -84, -87, -88, -91, -92, -93, -94]) + (countLit q [-95, -97, -99, -101, -102, -104, -106, -107, -109, -112, -114, -116, -118, -120, -121, -123, -125]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -70, -71, -75, -77, -78, -80, -83, -84, -87, -88, -91, -92, -93, -94]) (l₂ := [-95, -97, -99, -101, -102, -104, -106, -107, -109, -112, -114, -116, -118, -120, -121, -123, -125])
  have hm := merge_two (literal (valuationOf q) (1744)) (literal (valuationOf q) (1813)) (literal (valuationOf q) (1838)) (countLit q [-63, -66, -70, -71, -75, -77, -78, -80, -83, -84, -87, -88, -91, -92, -93, -94]) (countLit q [-95, -97, -99, -101, -102, -104, -106, -107, -109, -112, -114, -116, -118, -120, -121, -123, -125]) (count1823 q) 8 8 (meaning1744 q) (meaning1813 q) (meaning1838 q) hs
  change valuationOf q 1744 = false ∨ valuationOf q 1813 = false ∨ valuationOf q 1838 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2053 (q : Snake 81) (h : Conditions q) : valuation q 1744 = false ∨ valuation q 1813 = false ∨ valuation q 1838 = true := counterClause2053 (baseVal q)

theorem counterClause2054 (q : Nat → Bool) : valuationOf q 1745 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1838 = true := by
  have hs : count1823 q = (countLit q [-63, -66, -70, -71, -75, -77, -78, -80, -83, -84, -87, -88, -91, -92, -93, -94]) + (countLit q [-95, -97, -99, -101, -102, -104, -106, -107, -109, -112, -114, -116, -118, -120, -121, -123, -125]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -70, -71, -75, -77, -78, -80, -83, -84, -87, -88, -91, -92, -93, -94]) (l₂ := [-95, -97, -99, -101, -102, -104, -106, -107, -109, -112, -114, -116, -118, -120, -121, -123, -125])
  have hm := merge_two (literal (valuationOf q) (1745)) (literal (valuationOf q) (1812)) (literal (valuationOf q) (1838)) (countLit q [-63, -66, -70, -71, -75, -77, -78, -80, -83, -84, -87, -88, -91, -92, -93, -94]) (countLit q [-95, -97, -99, -101, -102, -104, -106, -107, -109, -112, -114, -116, -118, -120, -121, -123, -125]) (count1823 q) 9 7 (meaning1745 q) (meaning1812 q) (meaning1838 q) hs
  change valuationOf q 1745 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1838 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2054 (q : Snake 81) (h : Conditions q) : valuation q 1745 = false ∨ valuation q 1812 = false ∨ valuation q 1838 = true := counterClause2054 (baseVal q)

theorem counterClause2055 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1838 = false ∨ valuationOf q 1874 = true := by
  have hs : count1849 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31, -33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) + (countLit q [-63, -66, -70, -71, -75, -77, -78, -80, -83, -84, -87, -88, -91, -92, -93, -94, -95, -97, -99, -101, -102, -104, -106, -107, -109, -112, -114, -116, -118, -120, -121, -123, -125]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31, -33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) (l₂ := [-63, -66, -70, -71, -75, -77, -78, -80, -83, -84, -87, -88, -91, -92, -93, -94, -95, -97, -99, -101, -102, -104, -106, -107, -109, -112, -114, -116, -118, -120, -121, -123, -125])
  have hm := merge_two (literal (valuationOf q) (1672)) (literal (valuationOf q) (1838)) (literal (valuationOf q) (1874)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31, -33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) (countLit q [-63, -66, -70, -71, -75, -77, -78, -80, -83, -84, -87, -88, -91, -92, -93, -94, -95, -97, -99, -101, -102, -104, -106, -107, -109, -112, -114, -116, -118, -120, -121, -123, -125]) (count1849 q) 10 16 (meaning1672 q) (meaning1838 q) (meaning1874 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1838 = false ∨ valuationOf q 1874 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2055 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1838 = false ∨ valuation q 1874 = true := counterClause2055 (baseVal q)

theorem counterClause2056 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1874 = true := by
  have hs : count1849 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31, -33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) + (countLit q [-63, -66, -70, -71, -75, -77, -78, -80, -83, -84, -87, -88, -91, -92, -93, -94, -95, -97, -99, -101, -102, -104, -106, -107, -109, -112, -114, -116, -118, -120, -121, -123, -125]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31, -33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) (l₂ := [-63, -66, -70, -71, -75, -77, -78, -80, -83, -84, -87, -88, -91, -92, -93, -94, -95, -97, -99, -101, -102, -104, -106, -107, -109, -112, -114, -116, -118, -120, -121, -123, -125])
  have hm := merge_two (literal (valuationOf q) (1676)) (literal (valuationOf q) (1834)) (literal (valuationOf q) (1874)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31, -33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) (countLit q [-63, -66, -70, -71, -75, -77, -78, -80, -83, -84, -87, -88, -91, -92, -93, -94, -95, -97, -99, -101, -102, -104, -106, -107, -109, -112, -114, -116, -118, -120, -121, -123, -125]) (count1849 q) 14 12 (meaning1676 q) (meaning1834 q) (meaning1874 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1834 = false ∨ valuationOf q 1874 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2056 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1834 = false ∨ valuation q 1874 = true := counterClause2056 (baseVal q)

theorem counterClause2057 (q : Nat → Bool) : valuationOf q 1678 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1874 = true := by
  have hs : count1849 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31, -33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) + (countLit q [-63, -66, -70, -71, -75, -77, -78, -80, -83, -84, -87, -88, -91, -92, -93, -94, -95, -97, -99, -101, -102, -104, -106, -107, -109, -112, -114, -116, -118, -120, -121, -123, -125]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31, -33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) (l₂ := [-63, -66, -70, -71, -75, -77, -78, -80, -83, -84, -87, -88, -91, -92, -93, -94, -95, -97, -99, -101, -102, -104, -106, -107, -109, -112, -114, -116, -118, -120, -121, -123, -125])
  have hm := merge_two (literal (valuationOf q) (1678)) (literal (valuationOf q) (1832)) (literal (valuationOf q) (1874)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31, -33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) (countLit q [-63, -66, -70, -71, -75, -77, -78, -80, -83, -84, -87, -88, -91, -92, -93, -94, -95, -97, -99, -101, -102, -104, -106, -107, -109, -112, -114, -116, -118, -120, -121, -123, -125]) (count1849 q) 16 10 (meaning1678 q) (meaning1832 q) (meaning1874 q) hs
  change valuationOf q 1678 = false ∨ valuationOf q 1832 = false ∨ valuationOf q 1874 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2057 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1832 = false ∨ valuation q 1874 = true := counterClause2057 (baseVal q)

theorem counterClause2058 (q : Nat → Bool) : valuationOf q 1679 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1874 = true := by
  have hs : count1849 q = (countLit q [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31, -33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) + (countLit q [-63, -66, -70, -71, -75, -77, -78, -80, -83, -84, -87, -88, -91, -92, -93, -94, -95, -97, -99, -101, -102, -104, -106, -107, -109, -112, -114, -116, -118, -120, -121, -123, -125]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31, -33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) (l₂ := [-63, -66, -70, -71, -75, -77, -78, -80, -83, -84, -87, -88, -91, -92, -93, -94, -95, -97, -99, -101, -102, -104, -106, -107, -109, -112, -114, -116, -118, -120, -121, -123, -125])
  have hm := merge_two (literal (valuationOf q) (1679)) (literal (valuationOf q) (1831)) (literal (valuationOf q) (1874)) (countLit q [-3, -4, -8, -9, -11, -13, -14, -17, -18, -19, -22, -23, -25, -27, -29, -31, -33, -35, -37, -38, -39, -41, -43, -45, -47, -52, -53, -54, -55, -57, -58, -59, -61]) (countLit q [-63, -66, -70, -71, -75, -77, -78, -80, -83, -84, -87, -88, -91, -92, -93, -94, -95, -97, -99, -101, -102, -104, -106, -107, -109, -112, -114, -116, -118, -120, -121, -123, -125]) (count1849 q) 17 9 (meaning1679 q) (meaning1831 q) (meaning1874 q) hs
  change valuationOf q 1679 = false ∨ valuationOf q 1831 = false ∨ valuationOf q 1874 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause2058 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1831 = false ∨ valuation q 1874 = true := counterClause2058 (baseVal q)

theorem clause2059 (q : Snake 81) (h : Conditions q) : valuation q 1874 = false := by
  rw [value1874]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1849 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause2060 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 3 = false ∨ valuation q 78 = false ∨ valuation q 81 = false := by
  rw [value1, value3, value78, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (65 : Vertex) (69 : Vertex) (321 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2061 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 11 = false ∨ valuation q 37 = false ∨ valuation q 48 = false := by
  rw [value1, value11, value37, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (65 : Vertex) (81 : Vertex) (193 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2062 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 11 = false ∨ valuation q 78 = false ∨ valuation q 89 = false := by
  rw [value1, value11, value78, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (65 : Vertex) (81 : Vertex) (321 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2063 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 37 = false ∨ valuation q 78 = false ∨ valuation q 103 = false := by
  rw [value1, value37, value78, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (65 : Vertex) (193 : Vertex) (321 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2064 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 4 = false ∨ valuation q 19 = false ∨ valuation q 21 = false := by
  rw [value2, value4, value19, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (66 : Vertex) (70 : Vertex) (98 : Vertex) (102 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2065 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 19 = false ∨ valuation q 38 = false ∨ valuation q 56 = false := by
  rw [value2, value19, value38, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (66 : Vertex) (98 : Vertex) (194 : Vertex) (226 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2066 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 9 = false ∨ valuation q 41 = false ∨ valuation q 46 = false := by
  rw [value5, value9, value41, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (71 : Vertex) (79 : Vertex) (199 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2067 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 14 = false ∨ valuation q 41 = false ∨ valuation q 51 = false := by
  rw [value5, value14, value41, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (71 : Vertex) (87 : Vertex) (199 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2068 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 9 = false ∨ valuation q 43 = false ∨ valuation q 46 = false := by
  rw [value7, value9, value43, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (75 : Vertex) (79 : Vertex) (203 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2069 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 25 = false ∨ valuation q 43 = false ∨ valuation q 62 = false := by
  rw [value7, value25, value43, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (75 : Vertex) (107 : Vertex) (203 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2070 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 26 = false ∨ valuation q 44 = false ∨ valuation q 63 = false := by
  rw [value8, value26, value44, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (76 : Vertex) (108 : Vertex) (204 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2071 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 13 = false ∨ valuation q 47 = false ∨ valuation q 50 = false := by
  rw [value10, value13, value47, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (80 : Vertex) (84 : Vertex) (208 : Vertex) (212 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2072 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 28 = false ∨ valuation q 29 = false := by
  rw [value11, value12, value28, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (81 : Vertex) (83 : Vertex) (113 : Vertex) (115 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2073 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 15 = false ∨ valuation q 48 = false ∨ valuation q 52 = false := by
  rw [value11, value15, value48, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (81 : Vertex) (89 : Vertex) (209 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2074 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 58 = false ∨ valuation q 94 = false ∨ valuation q 119 = false := by
  rw [value20, value58, value94, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (101 : Vertex) (229 : Vertex) (357 : Vertex) (485 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2075 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 27 = false ∨ valuation q 59 = false ∨ valuation q 65 = false := by
  rw [value21, value27, value59, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (102 : Vertex) (110 : Vertex) (230 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2076 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 31 = false ∨ valuation q 59 = false ∨ valuation q 69 = false := by
  rw [value21, value31, value59, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (102 : Vertex) (118 : Vertex) (230 : Vertex) (246 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2077 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 60 = false ∨ valuation q 61 = false := by
  rw [value23, value24, value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (104 : Vertex) (105 : Vertex) (232 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2078 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 32 = false ∨ valuation q 60 = false ∨ valuation q 70 = false := by
  rw [value23, value32, value60, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (104 : Vertex) (120 : Vertex) (232 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2079 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 25 = false ∨ valuation q 61 = false ∨ valuation q 62 = false := by
  rw [value24, value25, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (105 : Vertex) (107 : Vertex) (233 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2080 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 27 = false ∨ valuation q 63 = false ∨ valuation q 65 = false := by
  rw [value26, value27, value63, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (108 : Vertex) (110 : Vertex) (236 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block64 (q : Snake 81) (h : Conditions q) : B112E260.Block64 (valuation q) :=
  ⟨clause2049 q h, clause2050 q h, clause2051 q h, clause2052 q h, clause2053 q h, clause2054 q h, clause2055 q h, clause2056 q h, clause2057 q h, clause2058 q h, clause2059 q h, clause2060 q h, clause2061 q h, clause2062 q h, clause2063 q h, clause2064 q h, clause2065 q h, clause2066 q h, clause2067 q h, clause2068 q h, clause2069 q h, clause2070 q h, clause2071 q h, clause2072 q h, clause2073 q h, clause2074 q h, clause2075 q h, clause2076 q h, clause2077 q h, clause2078 q h, clause2079 q h, clause2080 q h⟩

end
end Snake9.Regrowth.E112260
