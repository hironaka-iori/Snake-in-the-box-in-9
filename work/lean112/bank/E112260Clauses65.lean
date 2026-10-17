import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec65 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause2081 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 37 = false ∨ valuation q 47 = false ∨ valuation q 48 = false := by
  rw [value36, value37, value47, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (192 : Vertex) (193 : Vertex) (208 : Vertex) (209 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2082 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 42 = false ∨ valuation q 49 = false ∨ valuation q 53 = false := by
  rw [value38, value42, value49, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (194 : Vertex) (202 : Vertex) (210 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2083 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 41 = false ∨ valuation q 45 = false ∨ valuation q 46 = false := by
  rw [value40, value41, value45, value46]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (197 : Vertex) (199 : Vertex) (205 : Vertex) (207 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2084 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 54 = false ∨ valuation q 63 = false ∨ valuation q 72 = false := by
  rw [value44, value54, value63, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (204 : Vertex) (220 : Vertex) (236 : Vertex) (252 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2085 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 59 = false ∨ valuation q 66 = false ∨ valuation q 69 = false := by
  rw [value56, value59, value66, value69]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (226 : Vertex) (230 : Vertex) (242 : Vertex) (246 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2086 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 62 = false ∨ valuation q 67 = false ∨ valuation q 71 = false := by
  rw [value57, value62, value67, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (227 : Vertex) (235 : Vertex) (243 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2087 (q : Snake 81) (h : Conditions q) : valuation q 58 = false ∨ valuation q 64 = false ∨ valuation q 119 = false ∨ valuation q 125 = false := by
  rw [value58, value64, value119, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (229 : Vertex) (237 : Vertex) (485 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2088 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 75 = false ∨ valuation q 78 = false ∨ valuation q 81 = false := by
  rw [value74, value75, value78, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (257 : Vertex) (261 : Vertex) (321 : Vertex) (325 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2089 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 76 = false ∨ valuation q 81 = false ∨ valuation q 94 = false := by
  rw [value75, value76, value81, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (261 : Vertex) (293 : Vertex) (325 : Vertex) (357 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2090 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 77 = false ∨ valuation q 94 = false ∨ valuation q 96 = false := by
  rw [value76, value77, value94, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (293 : Vertex) (295 : Vertex) (357 : Vertex) (359 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2091 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 79 = false ∨ valuation q 81 = false ∨ valuation q 83 = false := by
  rw [value78, value79, value81, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (321 : Vertex) (323 : Vertex) (325 : Vertex) (327 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2092 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 79 = false ∨ valuation q 103 = false ∨ valuation q 104 = false := by
  rw [value78, value79, value103, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (321 : Vertex) (323 : Vertex) (449 : Vertex) (451 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2093 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 81 = false ∨ valuation q 89 = false ∨ valuation q 91 = false := by
  rw [value78, value81, value89, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (321 : Vertex) (325 : Vertex) (337 : Vertex) (341 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2094 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 93 = false ∨ valuation q 104 = false ∨ valuation q 117 = false := by
  rw [value79, value93, value104, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (323 : Vertex) (355 : Vertex) (451 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2095 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 98 = false ∨ valuation q 111 = false ∨ valuation q 125 = false := by
  rw [value87, value98, value111, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (333 : Vertex) (365 : Vertex) (461 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2096 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 96 = false ∨ valuation q 100 = false ∨ valuation q 101 = false := by
  rw [value94, value96, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (357 : Vertex) (359 : Vertex) (373 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2097 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 96 = false ∨ valuation q 119 = false ∨ valuation q 120 = false := by
  rw [value94, value96, value119, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (357 : Vertex) (359 : Vertex) (485 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2098 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 99 = false ∨ valuation q 120 = false ∨ valuation q 126 = false := by
  rw [value96, value99, value120, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (359 : Vertex) (367 : Vertex) (487 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2099 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 101 = false ∨ valuation q 120 = false ∨ valuation q 127 = false := by
  rw [value96, value101, value120, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (359 : Vertex) (375 : Vertex) (487 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2100 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 99 = false ∨ valuation q 125 = false ∨ valuation q 126 = false := by
  rw [value98, value99, value125, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (365 : Vertex) (367 : Vertex) (493 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2101 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 106 = false ∨ valuation q 114 = false ∨ valuation q 115 = false := by
  rw [value105, value106, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (452 : Vertex) (453 : Vertex) (468 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2102 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 117 = false ∨ valuation q 122 = false ∨ valuation q 123 = false := by
  rw [value116, value117, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (482 : Vertex) (483 : Vertex) (490 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block65 (q : Snake 81) (h : Conditions q) : B112E260.Block65 (valuation q) :=
  ⟨clause2081 q h, clause2082 q h, clause2083 q h, clause2084 q h, clause2085 q h, clause2086 q h, clause2087 q h, clause2088 q h, clause2089 q h, clause2090 q h, clause2091 q h, clause2092 q h, clause2093 q h, clause2094 q h, clause2095 q h, clause2096 q h, clause2097 q h, clause2098 q h, clause2099 q h, clause2100 q h, clause2101 q h, clause2102 q h⟩

end
end Snake9.Regrowth.E112260
