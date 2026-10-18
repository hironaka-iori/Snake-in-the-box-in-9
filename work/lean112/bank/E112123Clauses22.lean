import E112123Semantics
import B112E123Inputs
namespace Snake9.Regrowth.E112123
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 15 = false ∨ valuation q 71 = false ∨ valuation q 75 = false := by
  rw [value10, value15, value71, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (16 : Vertex) (24 : Vertex) (272 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 19 = false := by
  rw [value16, value17, value18, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (28 : Vertex) (29 : Vertex) (30 : Vertex) (31 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 26 = false ∨ valuation q 27 = false := by
  rw [value21, value22, value26, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (68 : Vertex) (69 : Vertex) (84 : Vertex) (85 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 34 = false ∨ valuation q 40 = false ∨ valuation q 41 = false := by
  rw [value33, value34, value40, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (161 : Vertex) (176 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 63 = false ∨ valuation q 64 = false ∨ valuation q 67 = false ∨ valuation q 68 = false := by
  rw [value63, value64, value67, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (258 : Vertex) (259 : Vertex) (266 : Vertex) (267 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 65 = false ∨ valuation q 66 = false ∨ valuation q 72 = false ∨ valuation q 73 = false := by
  rw [value65, value66, value72, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (260 : Vertex) (261 : Vertex) (276 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E123.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h⟩

end
end Snake9.Regrowth.E112123
