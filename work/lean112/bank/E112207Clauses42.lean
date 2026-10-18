import E112207Semantics
import B112E207Inputs
namespace Snake9.Regrowth.E112207
noncomputable section
local instance blockDec42 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1345 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 92 = false ∨ valuation q 93 = false ∨ valuation q 94 = false := by
  rw [value91, value92, value93, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (393 : Vertex) (395 : Vertex) (397 : Vertex) (399 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1346 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 96 = false ∨ valuation q 97 = false ∨ valuation q 98 = false := by
  rw [value95, value96, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (400 : Vertex) (401 : Vertex) (402 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block42 (q : Snake 81) (h : Conditions q) : B112E207.Block42 (valuation q) :=
  ⟨clause1345 q h, clause1346 q h⟩

end
end Snake9.Regrowth.E112207
