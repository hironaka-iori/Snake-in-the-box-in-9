import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec48 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1537 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 79 = false ∨ valuation q 86 = false ∨ valuation q 89 = false := by
  rw [value75, value79, value86, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (164 : Vertex) (176 : Vertex) (180 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1538 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 90 = false ∨ valuation q 92 = false ∨ valuation q 94 = false := by
  rw [value87, value90, value92, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (177 : Vertex) (181 : Vertex) (185 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1539 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 105 = false ∨ valuation q 107 = false ∨ valuation q 108 = false := by
  rw [value104, value105, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (225 : Vertex) (227 : Vertex) (233 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block48 (q : Snake 81) (h : Conditions q) : B112E259.Block48 (valuation q) :=
  ⟨clause1537 q h, clause1538 q h, clause1539 q h⟩

end
end Snake9.Regrowth.E112259
