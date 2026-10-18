import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec61 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1953 (q : Snake 81) (h : Conditions q) : valuation q 70 = false ∨ valuation q 71 = false ∨ valuation q 78 = false ∨ valuation q 79 = false := by
  rw [value70, value71, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (326 : Vertex) (327 : Vertex) (342 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1954 (q : Snake 81) (h : Conditions q) : valuation q 71 = false ∨ valuation q 79 = false ∨ valuation q 113 = false ∨ valuation q 122 = false := by
  rw [value71, value79, value113, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (327 : Vertex) (343 : Vertex) (455 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1955 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 73 = false ∨ valuation q 80 = false ∨ valuation q 82 = false := by
  rw [value72, value73, value80, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (328 : Vertex) (330 : Vertex) (344 : Vertex) (346 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1956 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 77 = false ∨ valuation q 78 = false ∨ valuation q 79 = false := by
  rw [value76, value77, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (340 : Vertex) (341 : Vertex) (342 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1957 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 81 = false ∨ valuation q 82 = false ∨ valuation q 83 = false := by
  rw [value80, value81, value82, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (344 : Vertex) (345 : Vertex) (346 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1958 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 86 = false ∨ valuation q 91 = false ∨ valuation q 93 = false := by
  rw [value85, value86, value91, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (384 : Vertex) (386 : Vertex) (392 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1959 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 89 = false ∨ valuation q 90 = false := by
  rw [value87, value88, value89, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (388 : Vertex) (389 : Vertex) (390 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1960 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 98 = false ∨ valuation q 99 = false := by
  rw [value87, value88, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (388 : Vertex) (389 : Vertex) (404 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1961 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 89 = false ∨ valuation q 98 = false ∨ valuation q 100 = false := by
  rw [value87, value89, value98, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (388 : Vertex) (390 : Vertex) (404 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1962 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 90 = false ∨ valuation q 99 = false ∨ valuation q 101 = false := by
  rw [value88, value90, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (389 : Vertex) (391 : Vertex) (405 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1963 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 90 = false ∨ valuation q 112 = false ∨ valuation q 113 = false := by
  rw [value88, value90, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (389 : Vertex) (391 : Vertex) (453 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1964 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 90 = false ∨ valuation q 100 = false ∨ valuation q 101 = false := by
  rw [value89, value90, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (390 : Vertex) (391 : Vertex) (406 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1965 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 96 = false ∨ valuation q 100 = false ∨ valuation q 106 = false := by
  rw [value89, value96, value100, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (390 : Vertex) (398 : Vertex) (406 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1966 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 101 = false ∨ valuation q 113 = false ∨ valuation q 122 = false := by
  rw [value90, value101, value113, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (391 : Vertex) (407 : Vertex) (455 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1967 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 93 = false ∨ valuation q 94 = false := by
  rw [value91, value92, value93, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (392 : Vertex) (393 : Vertex) (394 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1968 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 94 = false ∨ valuation q 102 = false ∨ valuation q 104 = false := by
  rw [value92, value94, value102, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (393 : Vertex) (395 : Vertex) (409 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1969 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 94 = false ∨ valuation q 114 = false ∨ valuation q 115 = false := by
  rw [value92, value94, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (393 : Vertex) (395 : Vertex) (457 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1970 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 95 = false ∨ valuation q 114 = false ∨ valuation q 116 = false := by
  rw [value92, value95, value114, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (393 : Vertex) (397 : Vertex) (457 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1971 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 94 = false ∨ valuation q 103 = false ∨ valuation q 104 = false := by
  rw [value93, value94, value103, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (394 : Vertex) (395 : Vertex) (410 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1972 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 106 = false ∨ valuation q 117 = false ∨ valuation q 127 = false := by
  rw [value96, value106, value117, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (398 : Vertex) (414 : Vertex) (462 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1973 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 99 = false ∨ valuation q 102 = false ∨ valuation q 105 = false := by
  rw [value97, value99, value102, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (401 : Vertex) (405 : Vertex) (409 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1974 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 99 = false ∨ valuation q 100 = false ∨ valuation q 101 = false := by
  rw [value98, value99, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (404 : Vertex) (405 : Vertex) (406 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1975 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 101 = false ∨ valuation q 105 = false ∨ valuation q 107 = false := by
  rw [value99, value101, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (405 : Vertex) (407 : Vertex) (413 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1976 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 101 = false ∨ valuation q 106 = false ∨ valuation q 107 = false := by
  rw [value100, value101, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (406 : Vertex) (407 : Vertex) (414 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1977 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 104 = false ∨ valuation q 105 = false ∨ valuation q 107 = false := by
  rw [value102, value104, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (409 : Vertex) (411 : Vertex) (413 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1978 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 104 = false ∨ valuation q 106 = false ∨ valuation q 107 = false := by
  rw [value103, value104, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (410 : Vertex) (411 : Vertex) (414 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1979 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 106 = false ∨ valuation q 124 = false ∨ valuation q 127 = false := by
  rw [value103, value106, value124, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (410 : Vertex) (414 : Vertex) (474 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1980 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 109 = false ∨ valuation q 111 = false ∨ valuation q 112 = false := by
  rw [value108, value109, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (448 : Vertex) (449 : Vertex) (452 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1981 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 110 = false ∨ valuation q 112 = false ∨ valuation q 113 = false := by
  rw [value109, value110, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (449 : Vertex) (451 : Vertex) (453 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1982 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 110 = false ∨ valuation q 114 = false ∨ valuation q 115 = false := by
  rw [value109, value110, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (449 : Vertex) (451 : Vertex) (457 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1983 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 112 = false ∨ valuation q 114 = false ∨ valuation q 116 = false := by
  rw [value109, value112, value114, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (449 : Vertex) (453 : Vertex) (457 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1984 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 113 = false ∨ valuation q 115 = false ∨ valuation q 118 = false := by
  rw [value110, value113, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (451 : Vertex) (455 : Vertex) (459 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block61 (q : Snake 81) (h : Conditions q) : B112E052.Block61 (valuation q) :=
  ⟨clause1953 q h, clause1954 q h, clause1955 q h, clause1956 q h, clause1957 q h, clause1958 q h, clause1959 q h, clause1960 q h, clause1961 q h, clause1962 q h, clause1963 q h, clause1964 q h, clause1965 q h, clause1966 q h, clause1967 q h, clause1968 q h, clause1969 q h, clause1970 q h, clause1971 q h, clause1972 q h, clause1973 q h, clause1974 q h, clause1975 q h, clause1976 q h, clause1977 q h, clause1978 q h, clause1979 q h, clause1980 q h, clause1981 q h, clause1982 q h, clause1983 q h, clause1984 q h⟩

end
end Snake9.Regrowth.E112052
