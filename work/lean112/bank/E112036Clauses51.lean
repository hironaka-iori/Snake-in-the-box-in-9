import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec51 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1633 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 96 = false ∨ valuation q 106 = false ∨ valuation q 108 = false := by
  rw [value95, value96, value106, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (424 : Vertex) (426 : Vertex) (440 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1634 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 97 = false ∨ valuation q 99 = false ∨ valuation q 100 = false := by
  rw [value96, value97, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (426 : Vertex) (427 : Vertex) (430 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1635 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 97 = false ∨ valuation q 108 = false ∨ valuation q 109 = false := by
  rw [value96, value97, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (426 : Vertex) (427 : Vertex) (442 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1636 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 100 = false ∨ valuation q 109 = false ∨ valuation q 110 = false := by
  rw [value97, value100, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (427 : Vertex) (431 : Vertex) (443 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1637 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 100 = false ∨ valuation q 117 = false ∨ valuation q 119 = false := by
  rw [value97, value100, value117, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (427 : Vertex) (431 : Vertex) (491 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1638 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 102 = false ∨ valuation q 104 = false ∨ valuation q 105 = false := by
  rw [value101, value102, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (433 : Vertex) (435 : Vertex) (437 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1639 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 102 = false ∨ valuation q 120 = false ∨ valuation q 122 = false := by
  rw [value101, value102, value120, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (433 : Vertex) (435 : Vertex) (497 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1640 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 105 = false ∨ valuation q 109 = false ∨ valuation q 110 = false := by
  rw [value102, value105, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (435 : Vertex) (439 : Vertex) (443 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1641 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 107 = false ∨ valuation q 108 = false ∨ valuation q 109 = false := by
  rw [value106, value107, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (440 : Vertex) (441 : Vertex) (442 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1642 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 112 = false ∨ valuation q 115 = false ∨ valuation q 116 = false := by
  rw [value111, value112, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (480 : Vertex) (481 : Vertex) (488 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1643 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 117 = false ∨ valuation q 118 = false ∨ valuation q 119 = false := by
  rw [value116, value117, value118, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (489 : Vertex) (491 : Vertex) (493 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1644 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 124 = false ∨ valuation q 126 = false ∨ valuation q 128 = false := by
  rw [value123, value124, value126, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (500 : Vertex) (502 : Vertex) (508 : Vertex) (510 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block51 (q : Snake 81) (h : Conditions q) : B112E036.Block51 (valuation q) :=
  ⟨clause1633 q h, clause1634 q h, clause1635 q h, clause1636 q h, clause1637 q h, clause1638 q h, clause1639 q h, clause1640 q h, clause1641 q h, clause1642 q h, clause1643 q h, clause1644 q h⟩

end
end Snake9.Regrowth.E112036
