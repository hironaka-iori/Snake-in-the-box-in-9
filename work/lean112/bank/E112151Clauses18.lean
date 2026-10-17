import E112151Semantics
import B112E151Inputs
namespace Snake9.Regrowth.E112151
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 83 = false ∨ valuation q 89 = false ∨ valuation q 91 = false := by
  rw [value81, value83, value89, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (425 : Vertex) (427 : Vertex) (441 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 83 = false ∨ valuation q 90 = false ∨ valuation q 91 = false := by
  rw [value82, value83, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (426 : Vertex) (427 : Vertex) (442 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 90 = false ∨ valuation q 105 = false ∨ valuation q 106 = false := by
  rw [value85, value90, value105, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (434 : Vertex) (442 : Vertex) (498 : Vertex) (506 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 89 = false ∨ valuation q 90 = false ∨ valuation q 91 = false := by
  rw [value88, value89, value90, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (440 : Vertex) (441 : Vertex) (442 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E151.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h⟩

end
end Snake9.Regrowth.E112151
