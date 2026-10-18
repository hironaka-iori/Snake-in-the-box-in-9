import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec50 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1601 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 96 = false ∨ valuation q 115 = false ∨ valuation q 116 = false := by
  rw [value94, value96, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (428 : Vertex) (430 : Vertex) (492 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1602 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 97 = false ∨ valuation q 107 = false ∨ valuation q 108 = false := by
  rw [value96, value97, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (430 : Vertex) (431 : Vertex) (446 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1603 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 99 = false ∨ valuation q 100 = false ∨ valuation q 101 = false := by
  rw [value98, value99, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (432 : Vertex) (433 : Vertex) (434 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1604 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 102 = false ∨ valuation q 103 = false ∨ valuation q 106 = false := by
  rw [value98, value102, value103, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (432 : Vertex) (436 : Vertex) (440 : Vertex) (444 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1605 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 105 = false ∨ valuation q 107 = false ∨ valuation q 108 = false := by
  rw [value104, value105, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (442 : Vertex) (443 : Vertex) (446 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1606 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 110 = false ∨ valuation q 113 = false ∨ valuation q 114 = false := by
  rw [value109, value110, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (480 : Vertex) (481 : Vertex) (488 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block50 (q : Snake 81) (h : Conditions q) : B112E008.Block50 (valuation q) :=
  ⟨clause1601 q h, clause1602 q h, clause1603 q h, clause1604 q h, clause1605 q h, clause1606 q h⟩

end
end Snake9.Regrowth.E112008
