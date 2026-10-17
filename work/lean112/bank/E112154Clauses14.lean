import E112154Semantics
import B112E154Inputs
namespace Snake9.Regrowth.E112154
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 89 = false ∨ valuation q 92 = false ∨ valuation q 93 = false := by
  rw [value88, value89, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (454 : Vertex) (455 : Vertex) (462 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E154.Block14 (valuation q) :=
  ⟨clause449 q h⟩

end
end Snake9.Regrowth.E112154
