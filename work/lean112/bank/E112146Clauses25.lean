import E112146Semantics
import B112E146Inputs
namespace Snake9.Regrowth.E112146
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 10 = false ∨ valuation q 12 = false ∨ valuation q 16 = false := by
  rw [value8, value10, value12, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (65 : Vertex) (69 : Vertex) (73 : Vertex) (77 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 14 = false ∨ valuation q 68 = false ∨ valuation q 72 = false := by
  rw [value9, value14, value68, value72]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (67 : Vertex) (75 : Vertex) (323 : Vertex) (331 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 50 = false ∨ valuation q 51 = false := by
  rw [value13, value14, value50, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (74 : Vertex) (75 : Vertex) (202 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 52 = false ∨ valuation q 53 = false := by
  rw [value15, value16, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (76 : Vertex) (77 : Vertex) (204 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 73 = false ∨ valuation q 74 = false := by
  rw [value15, value16, value73, value74]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (76 : Vertex) (77 : Vertex) (332 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 25 = false := by
  rw [value19, value22, value23, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (80 : Vertex) (84 : Vertex) (88 : Vertex) (92 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 58 = false ∨ valuation q 60 = false := by
  rw [value23, value24, value58, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (88 : Vertex) (90 : Vertex) (216 : Vertex) (218 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 30 = false ∨ valuation q 31 = false ∨ valuation q 32 = false := by
  rw [value28, value30, value31, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (129 : Vertex) (131 : Vertex) (133 : Vertex) (135 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 30 = false ∨ valuation q 33 = false ∨ valuation q 34 = false := by
  rw [value28, value30, value33, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (129 : Vertex) (131 : Vertex) (137 : Vertex) (139 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 31 = false ∨ valuation q 33 = false ∨ valuation q 36 = false := by
  rw [value28, value31, value33, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (129 : Vertex) (133 : Vertex) (137 : Vertex) (141 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 32 = false ∨ valuation q 36 = false ∨ valuation q 37 = false := by
  rw [value31, value32, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (133 : Vertex) (135 : Vertex) (141 : Vertex) (143 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 34 = false ∨ valuation q 36 = false ∨ valuation q 37 = false := by
  rw [value33, value34, value36, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (137 : Vertex) (139 : Vertex) (141 : Vertex) (143 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 52 = false ∨ valuation q 53 = false := by
  rw [value35, value36, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (140 : Vertex) (141 : Vertex) (204 : Vertex) (205 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 48 = false ∨ valuation q 49 = false := by
  rw [value45, value46, value48, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (192 : Vertex) (194 : Vertex) (196 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 46 = false ∨ valuation q 47 = false ∨ valuation q 50 = false ∨ valuation q 51 = false := by
  rw [value46, value47, value50, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (194 : Vertex) (195 : Vertex) (202 : Vertex) (203 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 55 = false ∨ valuation q 59 = false ∨ valuation q 61 = false := by
  rw [value54, value55, value59, value61]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (209 : Vertex) (213 : Vertex) (217 : Vertex) (221 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E146.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h⟩

end
end Snake9.Regrowth.E112146
