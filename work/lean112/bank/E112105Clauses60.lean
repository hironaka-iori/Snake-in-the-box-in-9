import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec60 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1921 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 111 = false ∨ valuation q 121 = false ∨ valuation q 122 = false := by
  rw [value110, value111, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (460 : Vertex) (461 : Vertex) (476 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1922 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 112 = false ∨ valuation q 121 = false ∨ valuation q 123 = false := by
  rw [value110, value112, value121, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (460 : Vertex) (462 : Vertex) (476 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1923 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 113 = false ∨ valuation q 122 = false ∨ valuation q 124 = false := by
  rw [value111, value113, value122, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (461 : Vertex) (463 : Vertex) (477 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1924 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 113 = false ∨ valuation q 123 = false ∨ valuation q 124 = false := by
  rw [value112, value113, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (462 : Vertex) (463 : Vertex) (478 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1925 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 115 = false ∨ valuation q 117 = false ∨ valuation q 118 = false := by
  rw [value114, value115, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (464 : Vertex) (465 : Vertex) (468 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1926 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 119 = false ∨ valuation q 120 = false ∨ valuation q 123 = false := by
  rw [value116, value119, value120, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (466 : Vertex) (470 : Vertex) (474 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1927 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 118 = false ∨ valuation q 121 = false ∨ valuation q 122 = false := by
  rw [value117, value118, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (468 : Vertex) (469 : Vertex) (476 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1928 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 122 = false ∨ valuation q 123 = false ∨ valuation q 124 = false := by
  rw [value121, value122, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (476 : Vertex) (477 : Vertex) (478 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block60 (q : Snake 81) (h : Conditions q) : B112E105.Block60 (valuation q) :=
  ⟨clause1921 q h, clause1922 q h, clause1923 q h, clause1924 q h, clause1925 q h, clause1926 q h, clause1927 q h, clause1928 q h⟩

end
end Snake9.Regrowth.E112105
