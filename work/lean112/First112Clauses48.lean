import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec48 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1537 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 92 = false ∨ valuation q 110 = false ∨ valuation q 112 = false := by
  rw [value89, value92, value110, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (427 : Vertex) (431 : Vertex) (491 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1538 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 94 = false ∨ valuation q 96 = false ∨ valuation q 97 = false := by
  rw [value93, value94, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (433 : Vertex) (435 : Vertex) (437 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1539 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 94 = false ∨ valuation q 114 = false ∨ valuation q 116 = false := by
  rw [value93, value94, value114, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (433 : Vertex) (435 : Vertex) (497 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1540 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 97 = false ∨ valuation q 101 = false ∨ valuation q 102 = false := by
  rw [value94, value97, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (435 : Vertex) (439 : Vertex) (443 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1541 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 99 = false ∨ valuation q 100 = false ∨ valuation q 101 = false := by
  rw [value98, value99, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (440 : Vertex) (441 : Vertex) (442 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1542 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 109 = false ∨ valuation q 113 = false ∨ valuation q 118 = false := by
  rw [value103, value109, value113, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (480 : Vertex) (488 : Vertex) (496 : Vertex) (504 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1543 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 106 = false ∨ valuation q 114 = false ∨ valuation q 116 = false := by
  rw [value104, value106, value114, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (481 : Vertex) (483 : Vertex) (497 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1544 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 108 = false ∨ valuation q 115 = false ∨ valuation q 117 = false := by
  rw [value105, value108, value115, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (482 : Vertex) (486 : Vertex) (498 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1545 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 112 = false ∨ valuation q 120 = false ∨ valuation q 122 = false := by
  rw [value111, value112, value120, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (493 : Vertex) (495 : Vertex) (509 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1546 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 114 = false ∨ valuation q 115 = false ∨ valuation q 116 = false := by
  rw [value113, value114, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (496 : Vertex) (497 : Vertex) (498 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1547 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 120 = false ∨ valuation q 121 = false ∨ valuation q 122 = false := by
  rw [value119, value120, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (508 : Vertex) (509 : Vertex) (510 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block48 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block48 (valuation q) :=
  ⟨clause1537 q h, clause1538 q h, clause1539 q h, clause1540 q h, clause1541 q h, clause1542 q h, clause1543 q h, clause1544 q h, clause1545 q h, clause1546 q h, clause1547 q h⟩

end
end Snake9.Regrowth.First112
