import E112104Semantics
import B112E104Inputs
namespace Snake9.Regrowth.E112104
noncomputable section
local instance blockDec36 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1153 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 104 = false ∨ valuation q 106 = false ∨ valuation q 108 = false := by
  rw [value102, value104, value106, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (488 : Vertex) (490 : Vertex) (492 : Vertex) (494 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1154 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 107 = false ∨ valuation q 115 = false ∨ valuation q 117 = false := by
  rw [value103, value107, value115, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (489 : Vertex) (493 : Vertex) (505 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1155 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 113 = false ∨ valuation q 117 = false ∨ valuation q 118 = false := by
  rw [value111, value113, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (501 : Vertex) (503 : Vertex) (509 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block36 (q : Snake 81) (h : Conditions q) : B112E104.Block36 (valuation q) :=
  ⟨clause1153 q h, clause1154 q h, clause1155 q h⟩

end
end Snake9.Regrowth.E112104
