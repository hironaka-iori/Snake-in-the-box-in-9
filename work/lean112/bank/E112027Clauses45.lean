import E112027Semantics
import B112E027Inputs
namespace Snake9.Regrowth.E112027
noncomputable section
local instance blockDec45 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1441 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 89 = false ∨ valuation q 98 = false ∨ valuation q 99 = false := by
  rw [value88, value89, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (396 : Vertex) (397 : Vertex) (412 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1442 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 90 = false ∨ valuation q 98 = false ∨ valuation q 100 = false := by
  rw [value88, value90, value98, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (396 : Vertex) (398 : Vertex) (412 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1443 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 90 = false ∨ valuation q 108 = false ∨ valuation q 109 = false := by
  rw [value88, value90, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (396 : Vertex) (398 : Vertex) (460 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1444 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 93 = false ∨ valuation q 94 = false ∨ valuation q 95 = false := by
  rw [value92, value93, value94, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (400 : Vertex) (401 : Vertex) (402 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1445 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 96 = false ∨ valuation q 97 = false ∨ valuation q 100 = false := by
  rw [value94, value96, value97, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (402 : Vertex) (406 : Vertex) (410 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1446 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 102 = false ∨ valuation q 106 = false ∨ valuation q 107 = false := by
  rw [value101, value102, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (450 : Vertex) (451 : Vertex) (458 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1447 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 104 = false ∨ valuation q 111 = false ∨ valuation q 112 = false := by
  rw [value103, value104, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (452 : Vertex) (453 : Vertex) (468 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1448 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 107 = false ∨ valuation q 116 = false ∨ valuation q 117 = false := by
  rw [value105, value107, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (457 : Vertex) (459 : Vertex) (473 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1449 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 112 = false ∨ valuation q 113 = false ∨ valuation q 114 = false := by
  rw [value111, value112, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (468 : Vertex) (469 : Vertex) (470 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block45 (q : Snake 81) (h : Conditions q) : B112E027.Block45 (valuation q) :=
  ⟨clause1441 q h, clause1442 q h, clause1443 q h, clause1444 q h, clause1445 q h, clause1446 q h, clause1447 q h, clause1448 q h, clause1449 q h⟩

end
end Snake9.Regrowth.E112027
