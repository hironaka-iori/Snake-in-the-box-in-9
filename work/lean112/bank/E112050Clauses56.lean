import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec56 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1793 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 91 = false ∨ valuation q 113 = false ∨ valuation q 114 = false := by
  rw [value89, value91, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (389 : Vertex) (391 : Vertex) (453 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1794 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 96 = false ∨ valuation q 100 = false ∨ valuation q 106 = false := by
  rw [value89, value96, value100, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (389 : Vertex) (397 : Vertex) (405 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1795 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 91 = false ∨ valuation q 101 = false ∨ valuation q 102 = false := by
  rw [value90, value91, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (390 : Vertex) (391 : Vertex) (406 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1796 (q : Snake 81) (h : Conditions q) : valuation q 90 = false ∨ valuation q 97 = false ∨ valuation q 101 = false ∨ valuation q 107 = false := by
  rw [value90, value97, value101, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (390 : Vertex) (398 : Vertex) (406 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1797 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 102 = false ∨ valuation q 114 = false ∨ valuation q 123 = false := by
  rw [value91, value102, value114, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (391 : Vertex) (407 : Vertex) (455 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1798 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 93 = false ∨ valuation q 94 = false ∨ valuation q 95 = false := by
  rw [value92, value93, value94, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (392 : Vertex) (393 : Vertex) (394 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1799 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 95 = false ∨ valuation q 103 = false ∨ valuation q 105 = false := by
  rw [value93, value95, value103, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (393 : Vertex) (395 : Vertex) (409 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1800 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 95 = false ∨ valuation q 115 = false ∨ valuation q 116 = false := by
  rw [value93, value95, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (393 : Vertex) (395 : Vertex) (457 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1801 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 96 = false ∨ valuation q 103 = false ∨ valuation q 106 = false := by
  rw [value93, value96, value103, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (393 : Vertex) (397 : Vertex) (409 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1802 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 96 = false ∨ valuation q 115 = false ∨ valuation q 117 = false := by
  rw [value93, value96, value115, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (393 : Vertex) (397 : Vertex) (457 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1803 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 95 = false ∨ valuation q 104 = false ∨ valuation q 105 = false := by
  rw [value94, value95, value104, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (394 : Vertex) (395 : Vertex) (410 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1804 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 97 = false ∨ valuation q 104 = false ∨ valuation q 107 = false := by
  rw [value94, value97, value104, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (394 : Vertex) (398 : Vertex) (410 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1805 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 107 = false ∨ valuation q 118 = false ∨ valuation q 128 = false := by
  rw [value97, value107, value118, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (398 : Vertex) (414 : Vertex) (462 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1806 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 100 = false ∨ valuation q 103 = false ∨ valuation q 106 = false := by
  rw [value98, value100, value103, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (401 : Vertex) (405 : Vertex) (409 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1807 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 100 = false ∨ valuation q 101 = false ∨ valuation q 102 = false := by
  rw [value99, value100, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (404 : Vertex) (405 : Vertex) (406 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1808 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 102 = false ∨ valuation q 107 = false ∨ valuation q 108 = false := by
  rw [value101, value102, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (406 : Vertex) (407 : Vertex) (414 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1809 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 105 = false ∨ valuation q 106 = false ∨ valuation q 108 = false := by
  rw [value103, value105, value106, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (409 : Vertex) (411 : Vertex) (413 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1810 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 105 = false ∨ valuation q 107 = false ∨ valuation q 108 = false := by
  rw [value104, value105, value107, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (410 : Vertex) (411 : Vertex) (414 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1811 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 111 = false ∨ valuation q 115 = false ∨ valuation q 116 = false := by
  rw [value110, value111, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (449 : Vertex) (451 : Vertex) (457 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1812 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 113 = false ∨ valuation q 115 = false ∨ valuation q 117 = false := by
  rw [value110, value113, value115, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (449 : Vertex) (453 : Vertex) (457 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1813 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 114 = false ∨ valuation q 122 = false ∨ valuation q 123 = false := by
  rw [value111, value114, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (451 : Vertex) (455 : Vertex) (467 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1814 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 121 = false ∨ valuation q 124 = false ∨ valuation q 125 = false := by
  rw [value120, value121, value124, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (464 : Vertex) (466 : Vertex) (472 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1815 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 125 = false ∨ valuation q 126 = false ∨ valuation q 128 = false := by
  rw [value124, value125, value126, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (472 : Vertex) (474 : Vertex) (476 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block56 (q : Snake 81) (h : Conditions q) : B112E050.Block56 (valuation q) :=
  ⟨clause1793 q h, clause1794 q h, clause1795 q h, clause1796 q h, clause1797 q h, clause1798 q h, clause1799 q h, clause1800 q h, clause1801 q h, clause1802 q h, clause1803 q h, clause1804 q h, clause1805 q h, clause1806 q h, clause1807 q h, clause1808 q h, clause1809 q h, clause1810 q h, clause1811 q h, clause1812 q h, clause1813 q h, clause1814 q h, clause1815 q h⟩

end
end Snake9.Regrowth.E112050
