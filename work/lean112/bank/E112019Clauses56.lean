import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec56 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1793 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 102 = false ∨ valuation q 103 = false ∨ valuation q 104 = false := by
  rw [value100, value102, value103, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (449 : Vertex) (451 : Vertex) (453 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1794 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 102 = false ∨ valuation q 112 = false ∨ valuation q 114 = false := by
  rw [value100, value102, value112, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (449 : Vertex) (451 : Vertex) (465 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1795 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 102 = false ∨ valuation q 113 = false ∨ valuation q 114 = false := by
  rw [value101, value102, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (450 : Vertex) (451 : Vertex) (466 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1796 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 106 = false ∨ valuation q 114 = false ∨ valuation q 118 = false := by
  rw [value102, value106, value114, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (451 : Vertex) (459 : Vertex) (467 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1797 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 104 = false ∨ valuation q 108 = false ∨ valuation q 110 = false := by
  rw [value103, value104, value108, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (453 : Vertex) (455 : Vertex) (461 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1798 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 110 = false ∨ valuation q 118 = false ∨ valuation q 121 = false := by
  rw [value106, value110, value118, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (459 : Vertex) (463 : Vertex) (475 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1799 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 108 = false ∨ valuation q 109 = false ∨ valuation q 110 = false := by
  rw [value107, value108, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (460 : Vertex) (461 : Vertex) (462 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1800 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 109 = false ∨ valuation q 119 = false ∨ valuation q 120 = false := by
  rw [value107, value109, value119, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (460 : Vertex) (462 : Vertex) (476 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1801 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 110 = false ∨ valuation q 120 = false ∨ valuation q 121 = false := by
  rw [value109, value110, value120, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (462 : Vertex) (463 : Vertex) (478 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1802 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 112 = false ∨ valuation q 113 = false ∨ valuation q 114 = false := by
  rw [value111, value112, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (464 : Vertex) (465 : Vertex) (466 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1803 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 115 = false ∨ valuation q 116 = false ∨ valuation q 119 = false := by
  rw [value111, value115, value116, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (464 : Vertex) (468 : Vertex) (472 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1804 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 117 = false ∨ valuation q 119 = false ∨ valuation q 120 = false := by
  rw [value116, value117, value119, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (472 : Vertex) (474 : Vertex) (476 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1805 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 118 = false ∨ valuation q 120 = false ∨ valuation q 121 = false := by
  rw [value117, value118, value120, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (474 : Vertex) (475 : Vertex) (478 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block56 (q : Snake 81) (h : Conditions q) : B112E019.Block56 (valuation q) :=
  ⟨clause1793 q h, clause1794 q h, clause1795 q h, clause1796 q h, clause1797 q h, clause1798 q h, clause1799 q h, clause1800 q h, clause1801 q h, clause1802 q h, clause1803 q h, clause1804 q h, clause1805 q h⟩

end
end Snake9.Regrowth.E112019
