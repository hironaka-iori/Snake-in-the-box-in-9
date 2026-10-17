import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec49 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1569 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 107 = false ∨ valuation q 114 = false ∨ valuation q 115 = false := by
  rw [value106, value107, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (456 : Vertex) (457 : Vertex) (472 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block49 (q : Snake 81) (h : Conditions q) : B112E158.Block49 (valuation q) :=
  ⟨clause1569 q h⟩

end
end Snake9.Regrowth.E112158
