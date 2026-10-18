import E112064Semantics
import B112E064Inputs
namespace Snake9.Regrowth.E112064
noncomputable section
local instance blockDec44 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1409 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 77 = false ∨ valuation q 80 = false ∨ valuation q 83 = false := by
  rw [value74, value77, value80, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (336 : Vertex) (340 : Vertex) (344 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1410 (q : Snake 81) (h : Conditions q) : valuation q 74 = false ∨ valuation q 80 = false ∨ valuation q 109 = false ∨ valuation q 114 = false := by
  rw [value74, value80, value109, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (336 : Vertex) (344 : Vertex) (464 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1411 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 76 = false ∨ valuation q 78 = false ∨ valuation q 79 = false := by
  rw [value75, value76, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (338 : Vertex) (339 : Vertex) (342 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1412 (q : Snake 81) (h : Conditions q) : valuation q 75 = false ∨ valuation q 78 = false ∨ valuation q 82 = false ∨ valuation q 85 = false := by
  rw [value75, value78, value82, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (338 : Vertex) (342 : Vertex) (346 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1413 (q : Snake 81) (h : Conditions q) : valuation q 77 = false ∨ valuation q 78 = false ∨ valuation q 83 = false ∨ valuation q 85 = false := by
  rw [value77, value78, value83, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (340 : Vertex) (342 : Vertex) (348 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1414 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 82 = false ∨ valuation q 83 = false ∨ valuation q 85 = false := by
  rw [value80, value82, value83, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (344 : Vertex) (346 : Vertex) (348 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1415 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 86 = false ∨ valuation q 116 = false ∨ valuation q 117 = false := by
  rw [value85, value86, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (350 : Vertex) (351 : Vertex) (478 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1416 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 104 = false ∨ valuation q 106 = false ∨ valuation q 108 = false := by
  rw [value101, value104, value106, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (450 : Vertex) (454 : Vertex) (458 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1417 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 110 = false ∨ valuation q 114 = false ∨ valuation q 115 = false := by
  rw [value109, value110, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (464 : Vertex) (465 : Vertex) (472 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1418 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 111 = false ∨ valuation q 112 = false ∨ valuation q 113 = false := by
  rw [value110, value111, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (465 : Vertex) (467 : Vertex) (469 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block44 (q : Snake 81) (h : Conditions q) : B112E064.Block44 (valuation q) :=
  ⟨clause1409 q h, clause1410 q h, clause1411 q h, clause1412 q h, clause1413 q h, clause1414 q h, clause1415 q h, clause1416 q h, clause1417 q h, clause1418 q h⟩

end
end Snake9.Regrowth.E112064
