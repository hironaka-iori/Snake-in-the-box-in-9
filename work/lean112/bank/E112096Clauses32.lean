import E112096Semantics
import B112E096Inputs
namespace Snake9.Regrowth.E112096
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 99 = false ∨ valuation q 102 = false ∨ valuation q 103 = false := by
  rw [value97, value99, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (449 : Vertex) (451 : Vertex) (457 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 99 = false ∨ valuation q 109 = false ∨ valuation q 110 = false := by
  rw [value98, value99, value109, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (450 : Vertex) (451 : Vertex) (466 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 107 = false ∨ valuation q 113 = false ∨ valuation q 118 = false := by
  rw [value101, value107, value113, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (455 : Vertex) (463 : Vertex) (471 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 103 = false ∨ valuation q 105 = false ∨ valuation q 107 = false := by
  rw [value102, value103, value105, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (457 : Vertex) (459 : Vertex) (461 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 105 = false ∨ valuation q 106 = false ∨ valuation q 107 = false := by
  rw [value104, value105, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (460 : Vertex) (461 : Vertex) (462 : Vertex) (463 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 105 = false ∨ valuation q 115 = false ∨ valuation q 116 = false := by
  rw [value104, value105, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (460 : Vertex) (461 : Vertex) (476 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 107 = false ∨ valuation q 116 = false ∨ valuation q 118 = false := by
  rw [value105, value107, value116, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (461 : Vertex) (463 : Vertex) (477 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 107 = false ∨ valuation q 117 = false ∨ valuation q 118 = false := by
  rw [value106, value107, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (462 : Vertex) (463 : Vertex) (478 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 109 = false ∨ valuation q 111 = false ∨ valuation q 112 = false := by
  rw [value108, value109, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (464 : Vertex) (466 : Vertex) (468 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 110 = false ∨ valuation q 112 = false ∨ valuation q 113 = false := by
  rw [value109, value110, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (466 : Vertex) (467 : Vertex) (470 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 116 = false ∨ valuation q 117 = false ∨ valuation q 118 = false := by
  rw [value115, value116, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (476 : Vertex) (477 : Vertex) (478 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E096.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h⟩

end
end Snake9.Regrowth.E112096
