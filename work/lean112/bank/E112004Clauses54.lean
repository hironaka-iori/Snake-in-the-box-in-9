import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec54 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1729 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 93 = false ∨ valuation q 100 = false ∨ valuation q 103 = false := by
  rw [value91, value93, value100, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (426 : Vertex) (430 : Vertex) (442 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1730 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 101 = false ∨ valuation q 117 = false ∨ valuation q 118 = false := by
  rw [value100, value101, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (442 : Vertex) (443 : Vertex) (506 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1731 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 105 = false ∨ valuation q 106 = false ∨ valuation q 107 = false := by
  rw [value104, value105, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (480 : Vertex) (481 : Vertex) (482 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1732 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 111 = false ∨ valuation q 119 = false ∨ valuation q 120 = false := by
  rw [value110, value111, value119, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (492 : Vertex) (493 : Vertex) (508 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1733 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 114 = false ∨ valuation q 117 = false ∨ valuation q 118 = false := by
  rw [value113, value114, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (498 : Vertex) (499 : Vertex) (506 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block54 (q : Snake 81) (h : Conditions q) : B112E004.Block54 (valuation q) :=
  ⟨clause1729 q h, clause1730 q h, clause1731 q h, clause1732 q h, clause1733 q h⟩

end
end Snake9.Regrowth.E112004
