import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec61 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1953 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 3 = false ∨ valuation q 4 = false ∨ valuation q 5 = false := by
  rw [value2, value3, value4, value5]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (1 : Vertex) (3 : Vertex) (5 : Vertex) (7 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1954 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 3 = false ∨ valuation q 6 = false ∨ valuation q 8 = false := by
  rw [value2, value3, value6, value8]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (1 : Vertex) (3 : Vertex) (9 : Vertex) (11 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1955 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 6 = false ∨ valuation q 19 = false ∨ valuation q 24 = false := by
  rw [value2, value6, value19, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (1 : Vertex) (9 : Vertex) (65 : Vertex) (73 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1956 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 8 = false ∨ valuation q 42 = false ∨ valuation q 43 = false := by
  rw [value7, value8, value42, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (10 : Vertex) (11 : Vertex) (138 : Vertex) (139 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1957 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 42 = false ∨ valuation q 81 = false ∨ valuation q 95 = false := by
  rw [value7, value42, value81, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (10 : Vertex) (138 : Vertex) (266 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1958 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 19 = false ∨ valuation q 23 = false ∨ valuation q 24 = false := by
  rw [value18, value19, value23, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (64 : Vertex) (65 : Vertex) (72 : Vertex) (73 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1959 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 20 = false ∨ valuation q 21 = false ∨ valuation q 22 = false := by
  rw [value18, value20, value21, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (64 : Vertex) (66 : Vertex) (68 : Vertex) (70 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1960 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 57 = false ∨ valuation q 60 = false := by
  rw [value20, value22, value57, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (66 : Vertex) (70 : Vertex) (194 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1961 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 62 = false ∨ valuation q 63 = false := by
  rw [value23, value24, value62, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (72 : Vertex) (73 : Vertex) (200 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1962 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 32 = false ∨ valuation q 62 = false ∨ valuation q 74 = false := by
  rw [value23, value32, value62, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (72 : Vertex) (88 : Vertex) (200 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1963 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 27 = false ∨ valuation q 67 = false ∨ valuation q 68 = false := by
  rw [value26, value27, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (78 : Vertex) (79 : Vertex) (206 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1964 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 31 = false ∨ valuation q 34 = false ∨ valuation q 35 = false := by
  rw [value28, value31, value34, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (83 : Vertex) (87 : Vertex) (91 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1965 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 74 = false ∨ valuation q 75 = false := by
  rw [value32, value33, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (88 : Vertex) (90 : Vertex) (216 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1966 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 41 = false ∨ valuation q 56 = false ∨ valuation q 63 = false := by
  rw [value36, value41, value56, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (129 : Vertex) (137 : Vertex) (193 : Vertex) (201 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1967 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 46 = false ∨ valuation q 56 = false ∨ valuation q 70 = false := by
  rw [value36, value46, value56, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (129 : Vertex) (145 : Vertex) (193 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1968 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 39 = false ∨ valuation q 57 = false ∨ valuation q 60 = false := by
  rw [value37, value39, value57, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (130 : Vertex) (134 : Vertex) (194 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1969 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 39 = false ∨ valuation q 47 = false ∨ valuation q 49 = false := by
  rw [value38, value39, value47, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (132 : Vertex) (134 : Vertex) (148 : Vertex) (150 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1970 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 49 = false ∨ valuation q 60 = false ∨ valuation q 73 = false := by
  rw [value39, value49, value60, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (134 : Vertex) (150 : Vertex) (198 : Vertex) (214 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1971 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 51 = false ∨ valuation q 52 = false := by
  rw [value40, value41, value51, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (136 : Vertex) (137 : Vertex) (152 : Vertex) (153 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1972 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 42 = false ∨ valuation q 51 = false ∨ valuation q 53 = false := by
  rw [value40, value42, value51, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (136 : Vertex) (138 : Vertex) (152 : Vertex) (154 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1973 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 51 = false ∨ valuation q 62 = false ∨ valuation q 74 = false := by
  rw [value40, value51, value62, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (136 : Vertex) (152 : Vertex) (200 : Vertex) (216 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1974 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 43 = false ∨ valuation q 52 = false ∨ valuation q 54 = false := by
  rw [value41, value43, value52, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (137 : Vertex) (139 : Vertex) (153 : Vertex) (155 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1975 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 43 = false ∨ valuation q 63 = false ∨ valuation q 64 = false := by
  rw [value41, value43, value63, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (137 : Vertex) (139 : Vertex) (201 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1976 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 43 = false ∨ valuation q 95 = false ∨ valuation q 96 = false := by
  rw [value42, value43, value95, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (138 : Vertex) (139 : Vertex) (394 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1977 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 45 = false ∨ valuation q 54 = false ∨ valuation q 55 = false := by
  rw [value43, value45, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (139 : Vertex) (143 : Vertex) (155 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1978 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 45 = false ∨ valuation q 64 = false ∨ valuation q 68 = false := by
  rw [value43, value45, value64, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (139 : Vertex) (143 : Vertex) (203 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1979 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 48 = false ∨ valuation q 49 = false ∨ valuation q 50 = false := by
  rw [value47, value48, value49, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (148 : Vertex) (149 : Vertex) (150 : Vertex) (151 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1980 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 54 = false := by
  rw [value51, value52, value53, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (152 : Vertex) (153 : Vertex) (154 : Vertex) (155 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1981 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 53 = false ∨ valuation q 74 = false ∨ valuation q 75 = false := by
  rw [value51, value53, value74, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (152 : Vertex) (154 : Vertex) (216 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1982 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 58 = false ∨ valuation q 59 = false ∨ valuation q 61 = false := by
  rw [value56, value58, value59, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (193 : Vertex) (195 : Vertex) (197 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1983 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 58 = false ∨ valuation q 63 = false ∨ valuation q 64 = false := by
  rw [value56, value58, value63, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (193 : Vertex) (195 : Vertex) (201 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1984 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 63 = false ∨ valuation q 108 = false ∨ valuation q 113 = false := by
  rw [value56, value63, value108, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (193 : Vertex) (201 : Vertex) (449 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block61 (q : Snake 81) (h : Conditions q) : B112E089.Block61 (valuation q) :=
  ⟨clause1953 q h, clause1954 q h, clause1955 q h, clause1956 q h, clause1957 q h, clause1958 q h, clause1959 q h, clause1960 q h, clause1961 q h, clause1962 q h, clause1963 q h, clause1964 q h, clause1965 q h, clause1966 q h, clause1967 q h, clause1968 q h, clause1969 q h, clause1970 q h, clause1971 q h, clause1972 q h, clause1973 q h, clause1974 q h, clause1975 q h, clause1976 q h, clause1977 q h, clause1978 q h, clause1979 q h, clause1980 q h, clause1981 q h, clause1982 q h, clause1983 q h, clause1984 q h⟩

end
end Snake9.Regrowth.E112089
