import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec57 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1825 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 42 = false ∨ valuation q 45 = false ∨ valuation q 51 = false := by
  rw [value38, value42, value45, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (194 : Vertex) (202 : Vertex) (210 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1826 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 47 = false ∨ valuation q 57 = false ∨ valuation q 66 = false := by
  rw [value39, value47, value57, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (196 : Vertex) (212 : Vertex) (228 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1827 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 65 = false ∨ valuation q 108 = false ∨ valuation q 119 = false := by
  rw [value46, value65, value108, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (211 : Vertex) (243 : Vertex) (467 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1828 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 48 = false ∨ valuation q 52 = false ∨ valuation q 53 = false := by
  rw [value47, value48, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (212 : Vertex) (213 : Vertex) (220 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1829 (q : Snake 81) (h : Conditions q) : valuation q 55 = false ∨ valuation q 57 = false ∨ valuation q 63 = false ∨ valuation q 66 = false := by
  rw [value55, value57, value63, value66]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (224 : Vertex) (228 : Vertex) (240 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1830 (q : Snake 81) (h : Conditions q) : valuation q 56 = false ∨ valuation q 60 = false ∨ valuation q 65 = false ∨ valuation q 71 = false := by
  rw [value56, value60, value65, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (227 : Vertex) (235 : Vertex) (243 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1831 (q : Snake 81) (h : Conditions q) : valuation q 59 = false ∨ valuation q 62 = false ∨ valuation q 70 = false ∨ valuation q 73 = false := by
  rw [value59, value62, value70, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (234 : Vertex) (238 : Vertex) (250 : Vertex) (254 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1832 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 72 = false ∨ valuation q 121 = false ∨ valuation q 126 = false := by
  rw [value67, value72, value121, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (245 : Vertex) (253 : Vertex) (501 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1833 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 75 = false ∨ valuation q 87 = false ∨ valuation q 90 = false := by
  rw [value74, value75, value87, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (281 : Vertex) (285 : Vertex) (345 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1834 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 76 = false ∨ valuation q 90 = false ∨ valuation q 99 = false := by
  rw [value75, value76, value90, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (285 : Vertex) (317 : Vertex) (349 : Vertex) (381 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1835 (q : Snake 81) (h : Conditions q) : valuation q 76 = false ∨ valuation q 77 = false ∨ valuation q 99 = false ∨ valuation q 101 = false := by
  rw [value76, value77, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (317 : Vertex) (319 : Vertex) (381 : Vertex) (383 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1836 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 80 = false ∨ valuation q 87 = false ∨ valuation q 90 = false := by
  rw [value78, value80, value87, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (329 : Vertex) (333 : Vertex) (345 : Vertex) (349 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1837 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 96 = false ∨ valuation q 109 = false ∨ valuation q 121 = false := by
  rw [value85, value96, value109, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (341 : Vertex) (373 : Vertex) (469 : Vertex) (501 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1838 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 111 = false ∨ valuation q 112 = false := by
  rw [value87, value88, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (345 : Vertex) (347 : Vertex) (473 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1839 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 92 = false ∨ valuation q 98 = false ∨ valuation q 101 = false := by
  rw [value88, value92, value98, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (347 : Vertex) (351 : Vertex) (379 : Vertex) (383 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1840 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 98 = false ∨ valuation q 112 = false ∨ valuation q 124 = false := by
  rw [value88, value98, value112, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (347 : Vertex) (379 : Vertex) (475 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1841 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 101 = false ∨ valuation q 116 = false ∨ valuation q 127 = false := by
  rw [value94, value101, value116, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (367 : Vertex) (383 : Vertex) (495 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1842 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 97 = false ∨ valuation q 121 = false ∨ valuation q 122 = false := by
  rw [value96, value97, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (373 : Vertex) (375 : Vertex) (501 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1843 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 108 = false ∨ valuation q 111 = false ∨ valuation q 112 = false := by
  rw [value107, value108, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (465 : Vertex) (467 : Vertex) (473 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block57 (q : Snake 81) (h : Conditions q) : B112E256.Block57 (valuation q) :=
  ⟨clause1825 q h, clause1826 q h, clause1827 q h, clause1828 q h, clause1829 q h, clause1830 q h, clause1831 q h, clause1832 q h, clause1833 q h, clause1834 q h, clause1835 q h, clause1836 q h, clause1837 q h, clause1838 q h, clause1839 q h, clause1840 q h, clause1841 q h, clause1842 q h, clause1843 q h⟩

end
end Snake9.Regrowth.E112256
