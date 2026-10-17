import E112079Semantics
import B112E079Inputs
namespace Snake9.Regrowth.E112079
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 20 = false ∨ valuation q 34 = false ∨ valuation q 37 = false := by
  rw [value17, value20, value34, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (162 : Vertex) (166 : Vertex) (226 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 38 = false ∨ valuation q 83 = false ∨ valuation q 99 = false := by
  rw [value21, value38, value83, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (171 : Vertex) (235 : Vertex) (427 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 40 = false ∨ valuation q 41 = false := by
  rw [value35, value36, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (228 : Vertex) (229 : Vertex) (244 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E079.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h⟩

end
end Snake9.Regrowth.E112079
