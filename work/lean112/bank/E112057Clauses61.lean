import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec61 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1953 (q : Nat → Bool) : valuationOf q 1778 = false ∨ valuationOf q 1802 = false ∨ valuationOf q 1812 = true := by
  have hs : count1809 q = (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) + (countLit q [-115, -116, -117, -119, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-99, -100, -102, -104, -106, -108, -110, -111]) (l₂ := [-115, -116, -117, -119, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1778)) (literal (valuationOf q) (1802)) (literal (valuationOf q) (1812)) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111]) (countLit q [-115, -116, -117, -119, -120, -122, -124, -126]) (count1809 q) 2 2 (meaning1778 q) (meaning1802 q) (meaning1812 q) hs
  change valuationOf q 1778 = false ∨ valuationOf q 1802 = false ∨ valuationOf q 1812 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1953 (q : Snake 81) (h : Conditions q) : valuation q 1778 = false ∨ valuation q 1802 = false ∨ valuation q 1812 = true := counterClause1953 (baseVal q)

theorem counterClause1954 (q : Nat → Bool) : valuationOf q 1752 = false ∨ valuationOf q 1814 = false ∨ valuationOf q 1838 = true := by
  have hs : count1825 q = (countLit q [-63, -66, -68, -70, -71, -74, -76, -78, -80, -81, -84, -85, -88, -92, -93, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -117, -119, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -70, -71, -74, -76, -78, -80, -81, -84, -85, -88, -92, -93, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -117, -119, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1752)) (literal (valuationOf q) (1814)) (literal (valuationOf q) (1838)) (countLit q [-63, -66, -68, -70, -71, -74, -76, -78, -80, -81, -84, -85, -88, -92, -93, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -117, -119, -120, -122, -124, -126]) (count1825 q) 8 6 (meaning1752 q) (meaning1814 q) (meaning1838 q) hs
  change valuationOf q 1752 = false ∨ valuationOf q 1814 = false ∨ valuationOf q 1838 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1954 (q : Snake 81) (h : Conditions q) : valuation q 1752 = false ∨ valuation q 1814 = false ∨ valuation q 1838 = true := counterClause1954 (baseVal q)

theorem counterClause1955 (q : Nat → Bool) : valuationOf q 1753 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1837 = true := by
  have hs : count1825 q = (countLit q [-63, -66, -68, -70, -71, -74, -76, -78, -80, -81, -84, -85, -88, -92, -93, -98]) + (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -117, -119, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -70, -71, -74, -76, -78, -80, -81, -84, -85, -88, -92, -93, -98]) (l₂ := [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -117, -119, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1753)) (literal (valuationOf q) (1812)) (literal (valuationOf q) (1837)) (countLit q [-63, -66, -68, -70, -71, -74, -76, -78, -80, -81, -84, -85, -88, -92, -93, -98]) (countLit q [-99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -117, -119, -120, -122, -124, -126]) (count1825 q) 9 4 (meaning1753 q) (meaning1812 q) (meaning1837 q) hs
  change valuationOf q 1753 = false ∨ valuationOf q 1812 = false ∨ valuationOf q 1837 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1955 (q : Snake 81) (h : Conditions q) : valuation q 1753 = false ∨ valuation q 1812 = false ∨ valuation q 1837 = true := counterClause1955 (baseVal q)

theorem counterClause1956 (q : Nat → Bool) : valuationOf q 1682 = false ∨ valuationOf q 1838 = false ∨ valuationOf q 1870 = true := by
  have hs : count1848 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29, -31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) + (countLit q [-63, -66, -68, -70, -71, -74, -76, -78, -80, -81, -84, -85, -88, -92, -93, -98, -99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -117, -119, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29, -31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (l₂ := [-63, -66, -68, -70, -71, -74, -76, -78, -80, -81, -84, -85, -88, -92, -93, -98, -99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -117, -119, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1682)) (literal (valuationOf q) (1838)) (literal (valuationOf q) (1870)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29, -31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (countLit q [-63, -66, -68, -70, -71, -74, -76, -78, -80, -81, -84, -85, -88, -92, -93, -98, -99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -117, -119, -120, -122, -124, -126]) (count1848 q) 9 14 (meaning1682 q) (meaning1838 q) (meaning1870 q) hs
  change valuationOf q 1682 = false ∨ valuationOf q 1838 = false ∨ valuationOf q 1870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1956 (q : Snake 81) (h : Conditions q) : valuation q 1682 = false ∨ valuation q 1838 = false ∨ valuation q 1870 = true := counterClause1956 (baseVal q)

theorem counterClause1957 (q : Nat → Bool) : valuationOf q 1683 = false ∨ valuationOf q 1837 = false ∨ valuationOf q 1870 = true := by
  have hs : count1848 q = (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29, -31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) + (countLit q [-63, -66, -68, -70, -71, -74, -76, -78, -80, -81, -84, -85, -88, -92, -93, -98, -99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -117, -119, -120, -122, -124, -126]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29, -31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (l₂ := [-63, -66, -68, -70, -71, -74, -76, -78, -80, -81, -84, -85, -88, -92, -93, -98, -99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -117, -119, -120, -122, -124, -126])
  have hm := merge_two (literal (valuationOf q) (1683)) (literal (valuationOf q) (1837)) (literal (valuationOf q) (1870)) (countLit q [-2, -3, -5, -8, -12, -13, -14, -16, -18, -20, -21, -23, -24, -27, -29, -31, -32, -34, -37, -38, -40, -41, -44, -45, -49, -52, -53, -55, -57, -58, -62]) (countLit q [-63, -66, -68, -70, -71, -74, -76, -78, -80, -81, -84, -85, -88, -92, -93, -98, -99, -100, -102, -104, -106, -108, -110, -111, -115, -116, -117, -119, -120, -122, -124, -126]) (count1848 q) 10 13 (meaning1683 q) (meaning1837 q) (meaning1870 q) hs
  change valuationOf q 1683 = false ∨ valuationOf q 1837 = false ∨ valuationOf q 1870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1957 (q : Snake 81) (h : Conditions q) : valuation q 1683 = false ∨ valuation q 1837 = false ∨ valuation q 1870 = true := counterClause1957 (baseVal q)

theorem clause1958 (q : Snake 81) (h : Conditions q) : valuation q 1870 = false := by
  rw [value1870]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1848 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1959 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 3 = false ∨ valuation q 5 = false ∨ valuation q 6 = false := by
  rw [value1, value3, value5, value6]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (0 : Vertex) (2 : Vertex) (8 : Vertex) (10 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1960 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 4 = false ∨ valuation q 10 = false ∨ valuation q 13 = false := by
  rw [value2, value4, value10, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (1 : Vertex) (5 : Vertex) (17 : Vertex) (21 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1961 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 13 = false ∨ valuation q 23 = false ∨ valuation q 33 = false := by
  rw [value4, value13, value23, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (5 : Vertex) (21 : Vertex) (69 : Vertex) (85 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1962 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 13 = false ∨ valuation q 70 = false ∨ valuation q 82 = false := by
  rw [value4, value13, value70, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (5 : Vertex) (21 : Vertex) (261 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1963 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 23 = false ∨ valuation q 70 = false ∨ valuation q 95 = false := by
  rw [value4, value23, value70, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (5 : Vertex) (69 : Vertex) (261 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1964 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 6 = false ∨ valuation q 7 = false ∨ valuation q 8 = false := by
  rw [value5, value6, value7, value8]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (8 : Vertex) (10 : Vertex) (12 : Vertex) (14 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1965 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 18 = false ∨ valuation q 76 = false ∨ valuation q 89 = false := by
  rw [value7, value18, value76, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (12 : Vertex) (28 : Vertex) (268 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1966 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 15 = false := by
  rw [value10, value12, value13, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (17 : Vertex) (19 : Vertex) (21 : Vertex) (23 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1967 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 12 = false ∨ valuation q 16 = false ∨ valuation q 17 = false := by
  rw [value10, value12, value16, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (17 : Vertex) (19 : Vertex) (25 : Vertex) (27 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1968 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 13 = false ∨ valuation q 16 = false ∨ valuation q 19 = false := by
  rw [value10, value13, value16, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (17 : Vertex) (21 : Vertex) (25 : Vertex) (29 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1969 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 15 = false ∨ valuation q 17 = false ∨ valuation q 20 = false := by
  rw [value12, value15, value17, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (19 : Vertex) (23 : Vertex) (27 : Vertex) (31 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1970 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 15 = false ∨ valuation q 50 = false ∨ valuation q 52 = false := by
  rw [value13, value15, value50, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (21 : Vertex) (23 : Vertex) (149 : Vertex) (151 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1971 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 15 = false ∨ valuation q 82 = false ∨ valuation q 84 = false := by
  rw [value13, value15, value82, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (21 : Vertex) (23 : Vertex) (277 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1972 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 83 = false ∨ valuation q 84 = false := by
  rw [value14, value15, value83, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (22 : Vertex) (23 : Vertex) (278 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1973 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 19 = false ∨ valuation q 20 = false := by
  rw [value16, value17, value19, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (25 : Vertex) (27 : Vertex) (29 : Vertex) (31 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1974 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 86 = false ∨ valuation q 88 = false := by
  rw [value16, value17, value86, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (25 : Vertex) (27 : Vertex) (281 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1975 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 36 = false ∨ valuation q 89 = false ∨ valuation q 106 = false := by
  rw [value18, value36, value89, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (28 : Vertex) (92 : Vertex) (284 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1976 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 25 = false ∨ valuation q 28 = false ∨ valuation q 29 = false := by
  rw [value21, value25, value28, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (67 : Vertex) (71 : Vertex) (75 : Vertex) (79 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1977 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 25 = false := by
  rw [value22, value23, value24, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (68 : Vertex) (69 : Vertex) (70 : Vertex) (71 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1978 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 32 = false ∨ valuation q 33 = false := by
  rw [value22, value23, value32, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (68 : Vertex) (69 : Vertex) (84 : Vertex) (85 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1979 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 31 = false ∨ valuation q 34 = false ∨ valuation q 35 = false := by
  rw [value30, value31, value34, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (80 : Vertex) (82 : Vertex) (88 : Vertex) (90 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1980 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 32 = false ∨ valuation q 34 = false ∨ valuation q 36 = false := by
  rw [value30, value32, value34, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (80 : Vertex) (84 : Vertex) (88 : Vertex) (92 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1981 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 37 = false := by
  rw [value34, value35, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (88 : Vertex) (90 : Vertex) (92 : Vertex) (94 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1982 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 42 = false := by
  rw [value39, value40, value41, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (132 : Vertex) (133 : Vertex) (134 : Vertex) (135 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1983 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 49 = false ∨ valuation q 50 = false := by
  rw [value39, value40, value49, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (132 : Vertex) (133 : Vertex) (148 : Vertex) (149 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1984 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 41 = false ∨ valuation q 49 = false ∨ valuation q 51 = false := by
  rw [value39, value41, value49, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (132 : Vertex) (134 : Vertex) (148 : Vertex) (150 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block61 (q : Snake 81) (h : Conditions q) : B112E057.Block61 (valuation q) :=
  ⟨clause1953 q h, clause1954 q h, clause1955 q h, clause1956 q h, clause1957 q h, clause1958 q h, clause1959 q h, clause1960 q h, clause1961 q h, clause1962 q h, clause1963 q h, clause1964 q h, clause1965 q h, clause1966 q h, clause1967 q h, clause1968 q h, clause1969 q h, clause1970 q h, clause1971 q h, clause1972 q h, clause1973 q h, clause1974 q h, clause1975 q h, clause1976 q h, clause1977 q h, clause1978 q h, clause1979 q h, clause1980 q h, clause1981 q h, clause1982 q h, clause1983 q h, clause1984 q h⟩

end
end Snake9.Regrowth.E112057
