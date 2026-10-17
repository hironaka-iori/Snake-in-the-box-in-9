import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec60 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1921 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 20 = false ∨ valuation q 21 = false := by
  rw [value16, value17, value20, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (132 : Vertex) (133 : Vertex) (140 : Vertex) (141 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1922 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 87 = false ∨ valuation q 88 = false := by
  rw [value16, value17, value87, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (132 : Vertex) (133 : Vertex) (388 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1923 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 21 = false ∨ valuation q 88 = false ∨ valuation q 95 = false := by
  rw [value17, value21, value88, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (133 : Vertex) (141 : Vertex) (389 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1924 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 19 = false ∨ valuation q 92 = false ∨ valuation q 94 = false := by
  rw [value18, value19, value92, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (137 : Vertex) (139 : Vertex) (393 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1925 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 29 = false ∨ valuation q 30 = false := by
  rw [value20, value22, value29, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (140 : Vertex) (142 : Vertex) (156 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1926 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 25 = false ∨ valuation q 26 = false := by
  rw [value23, value24, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (144 : Vertex) (145 : Vertex) (146 : Vertex) (147 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1927 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 31 = false ∨ valuation q 101 = false ∨ valuation q 107 = false := by
  rw [value27, value31, value101, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (151 : Vertex) (159 : Vertex) (407 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1928 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 44 = false ∨ valuation q 101 = false ∨ valuation q 122 = false := by
  rw [value27, value44, value101, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (151 : Vertex) (215 : Vertex) (407 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1929 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 31 = false ∨ valuation q 106 = false ∨ valuation q 107 = false := by
  rw [value30, value31, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (158 : Vertex) (159 : Vertex) (414 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1930 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 36 = false ∨ valuation q 37 = false := by
  rw [value32, value33, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (192 : Vertex) (194 : Vertex) (200 : Vertex) (202 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1931 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 44 = false ∨ valuation q 113 = false ∨ valuation q 122 = false := by
  rw [value35, value44, value113, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (199 : Vertex) (215 : Vertex) (455 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1932 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 37 = false ∨ valuation q 38 = false ∨ valuation q 39 = false := by
  rw [value36, value37, value38, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (200 : Vertex) (202 : Vertex) (204 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1933 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 42 = false ∨ valuation q 45 = false ∨ valuation q 48 = false := by
  rw [value40, value42, value45, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (209 : Vertex) (213 : Vertex) (217 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1934 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 42 = false ∨ valuation q 43 = false ∨ valuation q 44 = false := by
  rw [value41, value42, value43, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (212 : Vertex) (213 : Vertex) (214 : Vertex) (215 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1935 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 51 = false ∨ valuation q 54 = false ∨ valuation q 55 = false := by
  rw [value49, value51, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (257 : Vertex) (259 : Vertex) (265 : Vertex) (267 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1936 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 53 = false ∨ valuation q 54 = false ∨ valuation q 57 = false := by
  rw [value49, value53, value54, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (257 : Vertex) (261 : Vertex) (265 : Vertex) (269 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1937 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 60 = false ∨ valuation q 61 = false := by
  rw [value50, value51, value60, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (258 : Vertex) (259 : Vertex) (274 : Vertex) (275 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1938 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 87 = false ∨ valuation q 88 = false := by
  rw [value52, value53, value87, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (260 : Vertex) (261 : Vertex) (388 : Vertex) (389 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1939 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 57 = false ∨ valuation q 88 = false ∨ valuation q 95 = false := by
  rw [value53, value57, value88, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (261 : Vertex) (269 : Vertex) (389 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1940 (q : Snake 81) (h : Conditions q) : valuation q 53 = false ∨ valuation q 69 = false ∨ valuation q 88 = false ∨ valuation q 112 = false := by
  rw [value53, value69, value88, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (261 : Vertex) (325 : Vertex) (389 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1941 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 92 = false ∨ valuation q 94 = false := by
  rw [value54, value55, value92, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (265 : Vertex) (267 : Vertex) (393 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1942 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 57 = false ∨ valuation q 92 = false ∨ valuation q 95 = false := by
  rw [value54, value57, value92, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (265 : Vertex) (269 : Vertex) (393 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1943 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 58 = false ∨ valuation q 64 = false ∨ valuation q 65 = false := by
  rw [value56, value58, value64, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (268 : Vertex) (270 : Vertex) (284 : Vertex) (286 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1944 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 66 = false ∨ valuation q 79 = false ∨ valuation q 84 = false := by
  rw [value62, value66, value79, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (279 : Vertex) (287 : Vertex) (343 : Vertex) (351 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1945 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 66 = false ∨ valuation q 101 = false ∨ valuation q 107 = false := by
  rw [value62, value66, value101, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (279 : Vertex) (287 : Vertex) (407 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1946 (q : Snake 81) (h : Conditions q) : valuation q 62 = false ∨ valuation q 79 = false ∨ valuation q 101 = false ∨ valuation q 122 = false := by
  rw [value62, value79, value101, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (279 : Vertex) (343 : Vertex) (407 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1947 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 106 = false ∨ valuation q 107 = false := by
  rw [value65, value66, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (286 : Vertex) (287 : Vertex) (414 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1948 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 69 = false ∨ valuation q 70 = false ∨ valuation q 71 = false := by
  rw [value68, value69, value70, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (324 : Vertex) (325 : Vertex) (326 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1949 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 69 = false ∨ valuation q 76 = false ∨ valuation q 77 = false := by
  rw [value68, value69, value76, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (324 : Vertex) (325 : Vertex) (340 : Vertex) (341 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1950 (q : Snake 81) (h : Conditions q) : valuation q 68 = false ∨ valuation q 70 = false ∨ valuation q 76 = false ∨ valuation q 78 = false := by
  rw [value68, value70, value76, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (324 : Vertex) (326 : Vertex) (340 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1951 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 71 = false ∨ valuation q 77 = false ∨ valuation q 79 = false := by
  rw [value69, value71, value77, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (325 : Vertex) (327 : Vertex) (341 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1952 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 71 = false ∨ valuation q 112 = false ∨ valuation q 113 = false := by
  rw [value69, value71, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (325 : Vertex) (327 : Vertex) (453 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block60 (q : Snake 81) (h : Conditions q) : B112E052.Block60 (valuation q) :=
  ⟨clause1921 q h, clause1922 q h, clause1923 q h, clause1924 q h, clause1925 q h, clause1926 q h, clause1927 q h, clause1928 q h, clause1929 q h, clause1930 q h, clause1931 q h, clause1932 q h, clause1933 q h, clause1934 q h, clause1935 q h, clause1936 q h, clause1937 q h, clause1938 q h, clause1939 q h, clause1940 q h, clause1941 q h, clause1942 q h, clause1943 q h, clause1944 q h, clause1945 q h, clause1946 q h, clause1947 q h, clause1948 q h, clause1949 q h, clause1950 q h, clause1951 q h, clause1952 q h⟩

end
end Snake9.Regrowth.E112052
