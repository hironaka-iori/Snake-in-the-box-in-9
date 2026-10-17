import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec50 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1601 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 105 = false ∨ valuation q 115 = false ∨ valuation q 116 = false := by
  rw [value104, value105, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (482 : Vertex) (483 : Vertex) (498 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1602 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 108 = false ∨ valuation q 110 = false ∨ valuation q 111 = false := by
  rw [value107, value108, value110, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (488 : Vertex) (489 : Vertex) (492 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1603 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 110 = false ∨ valuation q 119 = false ∨ valuation q 121 = false := by
  rw [value107, value110, value119, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (488 : Vertex) (492 : Vertex) (504 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1604 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 109 = false ∨ valuation q 111 = false ∨ valuation q 112 = false := by
  rw [value108, value109, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (489 : Vertex) (491 : Vertex) (493 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1605 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 111 = false ∨ valuation q 121 = false ∨ valuation q 122 = false := by
  rw [value110, value111, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (492 : Vertex) (493 : Vertex) (508 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1606 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 112 = false ∨ valuation q 122 = false ∨ valuation q 124 = false := by
  rw [value111, value112, value122, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (493 : Vertex) (495 : Vertex) (509 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1607 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 114 = false ∨ valuation q 115 = false ∨ valuation q 116 = false := by
  rw [value113, value114, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (496 : Vertex) (497 : Vertex) (498 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1608 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 115 = false ∨ valuation q 117 = false ∨ valuation q 118 = false := by
  rw [value113, value115, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (496 : Vertex) (498 : Vertex) (500 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1609 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 117 = false ∨ valuation q 119 = false ∨ valuation q 121 = false := by
  rw [value113, value117, value119, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (496 : Vertex) (500 : Vertex) (504 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1610 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 118 = false ∨ valuation q 121 = false ∨ valuation q 123 = false := by
  rw [value117, value118, value121, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (500 : Vertex) (502 : Vertex) (508 : Vertex) (510 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1611 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 122 = false ∨ valuation q 123 = false ∨ valuation q 124 = false := by
  rw [value121, value122, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (508 : Vertex) (509 : Vertex) (510 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block50 (q : Snake 81) (h : Conditions q) : B112E020.Block50 (valuation q) :=
  ⟨clause1601 q h, clause1602 q h, clause1603 q h, clause1604 q h, clause1605 q h, clause1606 q h, clause1607 q h, clause1608 q h, clause1609 q h, clause1610 q h, clause1611 q h⟩

end
end Snake9.Regrowth.E112020
