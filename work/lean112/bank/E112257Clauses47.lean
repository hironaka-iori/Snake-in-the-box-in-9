import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec47 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1505 (q : Snake 81) (h : Conditions q) : valuation q 47 = false ∨ valuation q 49 = false ∨ valuation q 52 = false ∨ valuation q 55 = false := by
  rw [value47, value49, value52, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (145 : Vertex) (149 : Vertex) (153 : Vertex) (157 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1506 (q : Snake 81) (h : Conditions q) : valuation q 48 = false ∨ valuation q 53 = false ∨ valuation q 69 = false ∨ valuation q 75 = false := by
  rw [value48, value53, value69, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (147 : Vertex) (155 : Vertex) (179 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1507 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 54 = false ∨ valuation q 55 = false := by
  rw [value51, value52, value54, value55]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (152 : Vertex) (153 : Vertex) (156 : Vertex) (157 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1508 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 52 = false ∨ valuation q 72 = false ∨ valuation q 73 = false := by
  rw [value51, value52, value72, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (152 : Vertex) (153 : Vertex) (184 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1509 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 54 = false ∨ valuation q 72 = false ∨ valuation q 76 = false := by
  rw [value51, value54, value72, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (152 : Vertex) (156 : Vertex) (184 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1510 (q : Snake 81) (h : Conditions q) : valuation q 52 = false ∨ valuation q 53 = false ∨ valuation q 73 = false ∨ valuation q 75 = false := by
  rw [value52, value53, value73, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (153 : Vertex) (155 : Vertex) (185 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1511 (q : Snake 81) (h : Conditions q) : valuation q 57 = false ∨ valuation q 59 = false ∨ valuation q 62 = false ∨ valuation q 65 = false := by
  rw [value57, value59, value62, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (161 : Vertex) (165 : Vertex) (169 : Vertex) (173 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1512 (q : Snake 81) (h : Conditions q) : valuation q 61 = false ∨ valuation q 62 = false ∨ valuation q 72 = false ∨ valuation q 73 = false := by
  rw [value61, value62, value72, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (168 : Vertex) (169 : Vertex) (184 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1513 (q : Snake 81) (h : Conditions q) : valuation q 67 = false ∨ valuation q 70 = false ∨ valuation q 72 = false ∨ valuation q 76 = false := by
  rw [value67, value70, value72, value76]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (176 : Vertex) (180 : Vertex) (184 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1514 (q : Snake 81) (h : Conditions q) : valuation q 73 = false ∨ valuation q 75 = false ∨ valuation q 114 = false ∨ valuation q 115 = false := by
  rw [value73, value75, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (185 : Vertex) (187 : Vertex) (441 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1515 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 94 = false ∨ valuation q 110 = false ∨ valuation q 111 = false := by
  rw [value93, value94, value110, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (305 : Vertex) (307 : Vertex) (433 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1516 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 107 = false ∨ valuation q 111 = false ∨ valuation q 115 = false := by
  rw [value104, value107, value111, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (419 : Vertex) (427 : Vertex) (435 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1517 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 111 = false ∨ valuation q 114 = false ∨ valuation q 115 = false := by
  rw [value110, value111, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (433 : Vertex) (435 : Vertex) (441 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block47 (q : Snake 81) (h : Conditions q) : B112E257.Block47 (valuation q) :=
  ⟨clause1505 q h, clause1506 q h, clause1507 q h, clause1508 q h, clause1509 q h, clause1510 q h, clause1511 q h, clause1512 q h, clause1513 q h, clause1514 q h, clause1515 q h, clause1516 q h, clause1517 q h⟩

end
end Snake9.Regrowth.E112257
