import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 55 = false ∨ valuation q 113 = false ∨ valuation q 120 = false := by
  rw [value55, value113, value117, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (466 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 55 = false ∨ valuation q 116 = false ∨ valuation q 118 = false := by
  rw [value55, value116, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (472 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 55 = false ∨ valuation q 116 = false ∨ valuation q 120 = false := by
  rw [value55, value116, value117, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (472 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 55 = false ∨ valuation q 118 = false ∨ valuation q 120 = false := by
  rw [value55, value117, value118, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (475 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 76 = false ∨ valuation q 113 = false ∨ valuation q 116 = false := by
  rw [value76, value113, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (346 : Vertex) (466 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 76 = false ∨ valuation q 113 = false ∨ valuation q 118 = false := by
  rw [value76, value113, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (346 : Vertex) (466 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 76 = false ∨ valuation q 113 = false ∨ valuation q 120 = false := by
  rw [value76, value113, value117, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (346 : Vertex) (466 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 76 = false ∨ valuation q 116 = false ∨ valuation q 118 = false := by
  rw [value76, value116, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (346 : Vertex) (472 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 76 = false ∨ valuation q 116 = false ∨ valuation q 120 = false := by
  rw [value76, value116, value117, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (346 : Vertex) (472 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 76 = false ∨ valuation q 118 = false ∨ valuation q 120 = false := by
  rw [value76, value117, value118, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (346 : Vertex) (475 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 113 = false ∨ valuation q 116 = false ∨ valuation q 118 = false := by
  rw [value113, value116, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (466 : Vertex) (472 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 113 = false ∨ valuation q 116 = false ∨ valuation q 120 = false := by
  rw [value113, value116, value117, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (466 : Vertex) (472 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 113 = false ∨ valuation q 118 = false ∨ valuation q 120 = false := by
  rw [value113, value117, value118, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (466 : Vertex) (475 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 116 = false ∨ valuation q 118 = false ∨ valuation q 120 = false := by
  rw [value116, value117, value118, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (472 : Vertex) (475 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 238 = true ∨ valuation q 76 = true ∨ valuation q 113 = true ∨ valuation q 116 = true ∨ valuation q 118 = true ∨ valuation q 120 = true := by
  rw [value76, value113, value116, value117, value118, value120, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (474 : Vertex) w → w ∈ region → w ≠ (218 : Vertex) → w ∈ [(346 : Vertex), (466 : Vertex), (472 : Vertex), (475 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (474 : Vertex) (218 : Vertex) [(346 : Vertex), (466 : Vertex), (472 : Vertex), (475 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 239 = false ∨ valuation q 118 = true := by
  rw [value118, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (475 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 56 = false ∨ valuation q 77 = false ∨ valuation q 96 = false := by
  rw [value56, value77, value96, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (475 : Vertex) (219 : Vertex) (347 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 77 = false ∨ valuation q 96 = false ∨ valuation q 114 = false := by
  rw [value77, value96, value114, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (475 : Vertex) (347 : Vertex) (411 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 77 = false ∨ valuation q 96 = false ∨ valuation q 121 = false := by
  rw [value77, value96, value118, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (475 : Vertex) (347 : Vertex) (411 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 77 = false ∨ valuation q 106 = false ∨ valuation q 117 = false := by
  rw [value77, value106, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (475 : Vertex) (347 : Vertex) (459 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 77 = false ∨ valuation q 106 = false ∨ valuation q 121 = false := by
  rw [value77, value106, value118, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (475 : Vertex) (347 : Vertex) (459 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 77 = false ∨ valuation q 114 = false ∨ valuation q 121 = false := by
  rw [value77, value114, value118, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (475 : Vertex) (347 : Vertex) (467 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 96 = false ∨ valuation q 106 = false ∨ valuation q 121 = false := by
  rw [value96, value106, value118, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (475 : Vertex) (411 : Vertex) (459 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 96 = false ∨ valuation q 114 = false ∨ valuation q 121 = false := by
  rw [value96, value114, value118, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (475 : Vertex) (411 : Vertex) (467 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 106 = false ∨ valuation q 114 = false ∨ valuation q 117 = false := by
  rw [value106, value114, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (475 : Vertex) (459 : Vertex) (467 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 106 = false ∨ valuation q 114 = false ∨ valuation q 121 = false := by
  rw [value106, value114, value118, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (475 : Vertex) (459 : Vertex) (467 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 239 = true ∨ valuation q 56 = true ∨ valuation q 77 = true ∨ valuation q 106 = true ∨ valuation q 114 = true ∨ valuation q 117 = true ∨ valuation q 121 = true := by
  rw [value56, value77, value106, value114, value117, value118, value121, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (475 : Vertex) w → w ∈ region → w ≠ (411 : Vertex) → w ∈ [(219 : Vertex), (347 : Vertex), (459 : Vertex), (467 : Vertex), (474 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (475 : Vertex) (411 : Vertex) [(219 : Vertex), (347 : Vertex), (459 : Vertex), (467 : Vertex), (474 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 107 = false ∨ valuation q 115 = false ∨ valuation q 116 = false := by
  rw [value107, value115, value116, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (460 : Vertex) (468 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 107 = false ∨ valuation q 115 = false ∨ valuation q 120 = false := by
  rw [value107, value115, value119, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (460 : Vertex) (468 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 107 = false ∨ valuation q 116 = false ∨ valuation q 120 = false := by
  rw [value107, value116, value119, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (460 : Vertex) (472 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 115 = false ∨ valuation q 116 = false ∨ valuation q 120 = false := by
  rw [value115, value116, value119, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (468 : Vertex) (472 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 240 = true ∨ valuation q 107 = true ∨ valuation q 116 = true ∨ valuation q 120 = true := by
  rw [value107, value116, value119, value120, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (476 : Vertex) w → w ∈ region → w ≠ (468 : Vertex) → w ∈ [(460 : Vertex), (472 : Vertex), (478 : Vertex)] := by decide
  have hg := other_cover q (476 : Vertex) (468 : Vertex) [(460 : Vertex), (472 : Vertex), (478 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block25 (q : Snake 81) (h : Conditions q) : B112E019.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112019
