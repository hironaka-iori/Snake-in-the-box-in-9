import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec48 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1537 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 108 = false ∨ valuation q 115 = false ∨ valuation q 120 = false := by
  rw [value102, value108, value115, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (448 : Vertex) (456 : Vertex) (464 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1538 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 104 = false ∨ valuation q 106 = false ∨ valuation q 107 = false := by
  rw [value103, value104, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (449 : Vertex) (451 : Vertex) (453 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1539 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 104 = false ∨ valuation q 109 = false ∨ valuation q 111 = false := by
  rw [value103, value104, value109, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (449 : Vertex) (451 : Vertex) (457 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1540 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 106 = false ∨ valuation q 109 = false ∨ valuation q 112 = false := by
  rw [value103, value106, value109, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (449 : Vertex) (453 : Vertex) (457 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1541 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 107 = false ∨ valuation q 112 = false ∨ valuation q 114 = false := by
  rw [value106, value107, value112, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (453 : Vertex) (455 : Vertex) (461 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1542 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 111 = false ∨ valuation q 112 = false ∨ valuation q 114 = false := by
  rw [value109, value111, value112, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (457 : Vertex) (459 : Vertex) (461 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1543 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 111 = false ∨ valuation q 121 = false ∨ valuation q 122 = false := by
  rw [value110, value111, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (458 : Vertex) (459 : Vertex) (474 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1544 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 116 = false ∨ valuation q 120 = false ∨ valuation q 123 = false := by
  rw [value115, value116, value120, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (464 : Vertex) (468 : Vertex) (472 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1545 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 117 = false ∨ valuation q 118 = false ∨ valuation q 119 = false := by
  rw [value116, value117, value118, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (468 : Vertex) (469 : Vertex) (470 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1546 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 118 = false ∨ valuation q 123 = false ∨ valuation q 124 = false := by
  rw [value116, value118, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (468 : Vertex) (470 : Vertex) (476 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block48 (q : Snake 81) (h : Conditions q) : B112E153.Block48 (valuation q) :=
  ⟨clause1537 q h, clause1538 q h, clause1539 q h, clause1540 q h, clause1541 q h, clause1542 q h, clause1543 q h, clause1544 q h, clause1545 q h, clause1546 q h⟩

end
end Snake9.Regrowth.E112153
