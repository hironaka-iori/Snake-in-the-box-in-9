import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 240 = true ∨ valuation q 104 = true ∨ valuation q 114 = true ∨ valuation q 119 = true := by
  rw [value104, value114, value116, value119, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (466 : Vertex) w → w ∈ region → w ≠ (474 : Vertex) → w ∈ [(450 : Vertex), (464 : Vertex), (470 : Vertex)] := by decide
  have hg := other_cover q (466 : Vertex) (474 : Vertex) [(450 : Vertex), (464 : Vertex), (470 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 77 = false ∨ valuation q 94 = false ∨ valuation q 114 = false := by
  rw [value77, value94, value114, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (340 : Vertex) (404 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 77 = false ∨ valuation q 94 = false ∨ valuation q 118 = false := by
  rw [value77, value94, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (340 : Vertex) (404 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 77 = false ∨ valuation q 94 = false ∨ valuation q 119 = false := by
  rw [value77, value94, value117, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (340 : Vertex) (404 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 77 = false ∨ valuation q 94 = false ∨ valuation q 121 = false := by
  rw [value77, value94, value117, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (340 : Vertex) (404 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 77 = false ∨ valuation q 114 = false ∨ valuation q 118 = false := by
  rw [value77, value114, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (340 : Vertex) (464 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 77 = false ∨ valuation q 114 = false ∨ valuation q 121 = false := by
  rw [value77, value114, value117, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (340 : Vertex) (464 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 77 = false ∨ valuation q 118 = false ∨ valuation q 119 = false := by
  rw [value77, value117, value118, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (340 : Vertex) (469 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 94 = false ∨ valuation q 114 = false ∨ valuation q 118 = false := by
  rw [value94, value114, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (404 : Vertex) (464 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 94 = false ∨ valuation q 114 = false ∨ valuation q 119 = false := by
  rw [value94, value114, value117, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (404 : Vertex) (464 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 94 = false ∨ valuation q 114 = false ∨ valuation q 121 = false := by
  rw [value94, value114, value117, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (404 : Vertex) (464 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 94 = false ∨ valuation q 118 = false ∨ valuation q 119 = false := by
  rw [value94, value117, value118, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (404 : Vertex) (469 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 94 = false ∨ valuation q 119 = false ∨ valuation q 121 = false := by
  rw [value94, value117, value119, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (404 : Vertex) (470 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 114 = false ∨ valuation q 118 = false ∨ valuation q 119 = false := by
  rw [value114, value117, value118, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (464 : Vertex) (469 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 114 = false ∨ valuation q 118 = false ∨ valuation q 121 = false := by
  rw [value114, value117, value118, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (464 : Vertex) (469 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 114 = false ∨ valuation q 119 = false ∨ valuation q 121 = false := by
  rw [value114, value117, value119, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (464 : Vertex) (470 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 118 = false ∨ valuation q 119 = false ∨ valuation q 121 = false := by
  rw [value117, value118, value119, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (469 : Vertex) (470 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 241 = true ∨ valuation q 94 = true ∨ valuation q 114 = true ∨ valuation q 118 = true ∨ valuation q 119 = true ∨ valuation q 121 = true := by
  rw [value94, value114, value117, value118, value119, value121, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (468 : Vertex) w → w ∈ region → w ≠ (340 : Vertex) → w ∈ [(404 : Vertex), (464 : Vertex), (469 : Vertex), (470 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (468 : Vertex) (340 : Vertex) [(404 : Vertex), (464 : Vertex), (469 : Vertex), (470 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 241 = true ∨ valuation q 77 = true ∨ valuation q 114 = true ∨ valuation q 118 = true ∨ valuation q 119 = true ∨ valuation q 121 = true := by
  rw [value77, value114, value117, value118, value119, value121, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (468 : Vertex) w → w ∈ region → w ≠ (404 : Vertex) → w ∈ [(340 : Vertex), (464 : Vertex), (469 : Vertex), (470 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (468 : Vertex) (404 : Vertex) [(340 : Vertex), (464 : Vertex), (469 : Vertex), (470 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 241 = true ∨ valuation q 77 = true ∨ valuation q 94 = true ∨ valuation q 118 = true ∨ valuation q 119 = true ∨ valuation q 121 = true := by
  rw [value77, value94, value117, value118, value119, value121, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (468 : Vertex) w → w ∈ region → w ≠ (464 : Vertex) → w ∈ [(340 : Vertex), (404 : Vertex), (469 : Vertex), (470 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (468 : Vertex) (464 : Vertex) [(340 : Vertex), (404 : Vertex), (469 : Vertex), (470 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 241 = true ∨ valuation q 77 = true ∨ valuation q 94 = true ∨ valuation q 114 = true ∨ valuation q 118 = true ∨ valuation q 119 = true := by
  rw [value77, value94, value114, value117, value118, value119, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (468 : Vertex) w → w ∈ region → w ≠ (476 : Vertex) → w ∈ [(340 : Vertex), (404 : Vertex), (464 : Vertex), (469 : Vertex), (470 : Vertex)] := by decide
  have hg := other_cover q (468 : Vertex) (476 : Vertex) [(340 : Vertex), (404 : Vertex), (464 : Vertex), (469 : Vertex), (470 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 60 = false ∨ valuation q 78 = false ∨ valuation q 95 = false := by
  rw [value60, value78, value95, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (213 : Vertex) (341 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 60 = false ∨ valuation q 78 = false ∨ valuation q 106 = false := by
  rw [value60, value78, value106, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (213 : Vertex) (341 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 60 = false ∨ valuation q 78 = false ∨ valuation q 115 = false := by
  rw [value60, value78, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (213 : Vertex) (341 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 60 = false ∨ valuation q 78 = false ∨ valuation q 117 = false := by
  rw [value60, value78, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (213 : Vertex) (341 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 60 = false ∨ valuation q 78 = false ∨ valuation q 122 = false := by
  rw [value60, value78, value118, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (213 : Vertex) (341 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 60 = false ∨ valuation q 95 = false ∨ valuation q 106 = false := by
  rw [value60, value95, value106, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (213 : Vertex) (405 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 60 = false ∨ valuation q 95 = false ∨ valuation q 115 = false := by
  rw [value60, value95, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (213 : Vertex) (405 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 60 = false ∨ valuation q 95 = false ∨ valuation q 117 = false := by
  rw [value60, value95, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (213 : Vertex) (405 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 60 = false ∨ valuation q 95 = false ∨ valuation q 122 = false := by
  rw [value60, value95, value118, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (213 : Vertex) (405 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 60 = false ∨ valuation q 106 = false ∨ valuation q 115 = false := by
  rw [value60, value106, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (213 : Vertex) (453 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 60 = false ∨ valuation q 106 = false ∨ valuation q 117 = false := by
  rw [value60, value106, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (469 : Vertex) (213 : Vertex) (453 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E105.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112105
