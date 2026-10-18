import E112254Semantics
import B112E254Inputs
namespace Snake9.Regrowth.E112254
noncomputable section
local instance blockDec44 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1409 (q : Snake 81) (h : Conditions q) : valuation q 69 = false ∨ valuation q 73 = false ∨ valuation q 76 = false ∨ valuation q 81 = false := by
  rw [value69, value73, value76, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (391 : Vertex) (399 : Vertex) (407 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1410 (q : Snake 81) (h : Conditions q) : valuation q 72 = false ∨ valuation q 79 = false ∨ valuation q 105 = false ∨ valuation q 109 = false := by
  rw [value72, value79, value105, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (396 : Vertex) (412 : Vertex) (460 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1411 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 88 = false ∨ valuation q 93 = false ∨ valuation q 99 = false := by
  rw [value83, value88, value93, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (419 : Vertex) (427 : Vertex) (435 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1412 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 98 = false ∨ valuation q 99 = false := by
  rw [value87, value88, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (426 : Vertex) (427 : Vertex) (442 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1413 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 90 = false ∨ valuation q 98 = false ∨ valuation q 101 = false := by
  rw [value87, value90, value98, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (426 : Vertex) (430 : Vertex) (442 : Vertex) (446 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1414 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 109 = false ∨ valuation q 116 = false ∨ valuation q 122 = false := by
  rw [value105, value109, value116, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (460 : Vertex) (476 : Vertex) (492 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block44 (q : Snake 81) (h : Conditions q) : B112E254.Block44 (valuation q) :=
  ⟨clause1409 q h, clause1410 q h, clause1411 q h, clause1412 q h, clause1413 q h, clause1414 q h⟩

end
end Snake9.Regrowth.E112254
