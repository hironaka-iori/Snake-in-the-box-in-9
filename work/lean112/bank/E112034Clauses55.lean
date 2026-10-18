import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec55 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1761 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 97 = false ∨ valuation q 98 = false ∨ valuation q 99 = false := by
  rw [value96, value97, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (432 : Vertex) (433 : Vertex) (434 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1762 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 99 = false ∨ valuation q 119 = false ∨ valuation q 120 = false := by
  rw [value97, value99, value119, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (433 : Vertex) (435 : Vertex) (497 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1763 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 103 = false ∨ valuation q 104 = false ∨ valuation q 105 = false := by
  rw [value102, value103, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (444 : Vertex) (445 : Vertex) (446 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1764 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 107 = false ∨ valuation q 113 = false ∨ valuation q 115 = false := by
  rw [value106, value107, value113, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (480 : Vertex) (482 : Vertex) (488 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1765 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 109 = false ∨ valuation q 113 = false ∨ valuation q 116 = false := by
  rw [value106, value109, value113, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (480 : Vertex) (484 : Vertex) (488 : Vertex) (492 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1766 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 111 = false ∨ valuation q 115 = false ∨ valuation q 118 = false := by
  rw [value107, value111, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (482 : Vertex) (486 : Vertex) (490 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1767 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 111 = false ∨ valuation q 116 = false ∨ valuation q 118 = false := by
  rw [value109, value111, value116, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (484 : Vertex) (486 : Vertex) (492 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1768 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 112 = false ∨ valuation q 121 = false ∨ valuation q 123 = false := by
  rw [value110, value112, value121, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (485 : Vertex) (487 : Vertex) (501 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1769 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 117 = false ∨ valuation q 121 = false ∨ valuation q 128 = false := by
  rw [value110, value117, value121, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (485 : Vertex) (493 : Vertex) (501 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1770 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 114 = false ∨ valuation q 116 = false ∨ valuation q 117 = false := by
  rw [value113, value114, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (488 : Vertex) (489 : Vertex) (492 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1771 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 114 = false ∨ valuation q 124 = false ∨ valuation q 125 = false := by
  rw [value113, value114, value124, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (488 : Vertex) (489 : Vertex) (504 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1772 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 115 = false ∨ valuation q 116 = false ∨ valuation q 118 = false := by
  rw [value113, value115, value116, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (488 : Vertex) (490 : Vertex) (492 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1773 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 115 = false ∨ valuation q 124 = false ∨ valuation q 126 = false := by
  rw [value113, value115, value124, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (488 : Vertex) (490 : Vertex) (504 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1774 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 117 = false ∨ valuation q 125 = false ∨ valuation q 128 = false := by
  rw [value114, value117, value125, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (489 : Vertex) (493 : Vertex) (505 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1775 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 120 = false ∨ valuation q 121 = false ∨ valuation q 123 = false := by
  rw [value119, value120, value121, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (497 : Vertex) (499 : Vertex) (501 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1776 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 120 = false ∨ valuation q 125 = false ∨ valuation q 127 = false := by
  rw [value119, value120, value125, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (497 : Vertex) (499 : Vertex) (505 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1777 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 121 = false ∨ valuation q 125 = false ∨ valuation q 128 = false := by
  rw [value119, value121, value125, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (497 : Vertex) (501 : Vertex) (505 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1778 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 125 = false ∨ valuation q 126 = false ∨ valuation q 127 = false := by
  rw [value124, value125, value126, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (504 : Vertex) (505 : Vertex) (506 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block55 (q : Snake 81) (h : Conditions q) : B112E034.Block55 (valuation q) :=
  ⟨clause1761 q h, clause1762 q h, clause1763 q h, clause1764 q h, clause1765 q h, clause1766 q h, clause1767 q h, clause1768 q h, clause1769 q h, clause1770 q h, clause1771 q h, clause1772 q h, clause1773 q h, clause1774 q h, clause1775 q h, clause1776 q h, clause1777 q h, clause1778 q h⟩

end
end Snake9.Regrowth.E112034
