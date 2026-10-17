import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec62 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1985 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 113 = false ∨ valuation q 121 = false ∨ valuation q 122 = false := by
  rw [value110, value113, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (451 : Vertex) (455 : Vertex) (467 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1986 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 113 = false ∨ valuation q 116 = false ∨ valuation q 118 = false := by
  rw [value112, value113, value116, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (453 : Vertex) (455 : Vertex) (461 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1987 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 115 = false ∨ valuation q 116 = false ∨ valuation q 118 = false := by
  rw [value114, value115, value116, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (457 : Vertex) (459 : Vertex) (461 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1988 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 120 = false ∨ valuation q 123 = false ∨ valuation q 124 = false := by
  rw [value119, value120, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (464 : Vertex) (466 : Vertex) (472 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1989 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 124 = false ∨ valuation q 125 = false ∨ valuation q 127 = false := by
  rw [value123, value124, value125, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (472 : Vertex) (474 : Vertex) (476 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block62 (q : Snake 81) (h : Conditions q) : B112E052.Block62 (valuation q) :=
  ⟨clause1985 q h, clause1986 q h, clause1987 q h, clause1988 q h, clause1989 q h⟩

end
end Snake9.Regrowth.E112052
