import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec48 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1537 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 91 = false ∨ valuation q 110 = false ∨ valuation q 112 = false := by
  rw [value90, value91, value110, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (401 : Vertex) (403 : Vertex) (465 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1538 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 92 = false ∨ valuation q 96 = false ∨ valuation q 99 = false := by
  rw [value90, value92, value96, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (401 : Vertex) (405 : Vertex) (409 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1539 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 96 = false ∨ valuation q 97 = false ∨ valuation q 98 = false := by
  rw [value95, value96, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (408 : Vertex) (409 : Vertex) (410 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1540 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 101 = false ∨ valuation q 105 = false ∨ valuation q 106 = false := by
  rw [value100, value101, value105, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (450 : Vertex) (451 : Vertex) (458 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1541 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 106 = false ∨ valuation q 107 = false ∨ valuation q 108 = false := by
  rw [value104, value106, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (457 : Vertex) (459 : Vertex) (461 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1542 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 110 = false ∨ valuation q 111 = false ∨ valuation q 112 = false := by
  rw [value109, value110, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (464 : Vertex) (465 : Vertex) (466 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block48 (q : Snake 81) (h : Conditions q) : B112E047.Block48 (valuation q) :=
  ⟨clause1537 q h, clause1538 q h, clause1539 q h, clause1540 q h, clause1541 q h, clause1542 q h⟩

end
end Snake9.Regrowth.E112047
