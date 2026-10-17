import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 44 = false ∨ valuation q 102 = false ∨ valuation q 122 = false := by
  rw [value44, value102, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (471 : Vertex) (215 : Vertex) (407 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 44 = false ∨ valuation q 114 = false ∨ valuation q 122 = false := by
  rw [value44, value114, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (471 : Vertex) (215 : Vertex) (455 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 80 = false ∨ valuation q 102 = false ∨ valuation q 114 = false := by
  rw [value80, value102, value114, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (471 : Vertex) (343 : Vertex) (407 : Vertex) (455 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 80 = false ∨ valuation q 102 = false ∨ valuation q 122 = false := by
  rw [value80, value102, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (471 : Vertex) (343 : Vertex) (407 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 80 = false ∨ valuation q 114 = false ∨ valuation q 122 = false := by
  rw [value80, value114, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (471 : Vertex) (343 : Vertex) (455 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 102 = false ∨ valuation q 114 = false ∨ valuation q 122 = false := by
  rw [value102, value114, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (471 : Vertex) (407 : Vertex) (455 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 251 = true ∨ valuation q 44 = true ∨ valuation q 80 = true ∨ valuation q 102 = true ∨ valuation q 122 = true := by
  rw [value44, value80, value102, value122, value123, value251]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (471 : Vertex) w → w ∈ region → w ≠ (455 : Vertex) → w ∈ [(215 : Vertex), (343 : Vertex), (407 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (471 : Vertex) (455 : Vertex) [(215 : Vertex), (343 : Vertex), (407 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 251 = true ∨ valuation q 44 = true ∨ valuation q 80 = true ∨ valuation q 102 = true ∨ valuation q 114 = true := by
  rw [value44, value80, value102, value114, value123, value251]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (471 : Vertex) w → w ∈ region → w ≠ (467 : Vertex) → w ∈ [(215 : Vertex), (343 : Vertex), (407 : Vertex), (455 : Vertex)] := by decide
  have hg := other_cover q (471 : Vertex) (467 : Vertex) [(215 : Vertex), (343 : Vertex), (407 : Vertex), (455 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 81 = false ∨ valuation q 120 = false ∨ valuation q 126 = false := by
  rw [value81, value120, value124, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (472 : Vertex) (344 : Vertex) (464 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 81 = false ∨ valuation q 125 = false ∨ valuation q 126 = false := by
  rw [value81, value124, value125, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (472 : Vertex) (344 : Vertex) (474 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 120 = false ∨ valuation q 125 = false ∨ valuation q 126 = false := by
  rw [value120, value124, value125, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (472 : Vertex) (464 : Vertex) (474 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 252 = true ∨ valuation q 81 = true ∨ valuation q 125 = true ∨ valuation q 126 = true := by
  rw [value81, value124, value125, value126, value252]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (464 : Vertex) → w ∈ [(344 : Vertex), (474 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (464 : Vertex) [(344 : Vertex), (474 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 252 = true ∨ valuation q 81 = true ∨ valuation q 120 = true ∨ valuation q 126 = true := by
  rw [value81, value120, value124, value126, value252]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (474 : Vertex) → w ∈ [(344 : Vertex), (464 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (474 : Vertex) [(344 : Vertex), (464 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 46 = false ∨ valuation q 83 = false ∨ valuation q 104 = false := by
  rw [value46, value83, value104, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (346 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 46 = false ∨ valuation q 83 = false ∨ valuation q 121 = false := by
  rw [value46, value83, value121, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (346 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 46 = false ∨ valuation q 83 = false ∨ valuation q 124 = false := by
  rw [value46, value83, value124, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (346 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 46 = false ∨ valuation q 83 = false ∨ valuation q 128 = false := by
  rw [value46, value83, value125, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (346 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 46 = false ∨ valuation q 104 = false ∨ valuation q 121 = false := by
  rw [value46, value104, value121, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (410 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 46 = false ∨ valuation q 104 = false ∨ valuation q 124 = false := by
  rw [value46, value104, value124, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (410 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 46 = false ∨ valuation q 104 = false ∨ valuation q 128 = false := by
  rw [value46, value104, value125, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (410 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 46 = false ∨ valuation q 121 = false ∨ valuation q 124 = false := by
  rw [value46, value121, value124, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (466 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 46 = false ∨ valuation q 121 = false ∨ valuation q 128 = false := by
  rw [value46, value121, value125, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (466 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 46 = false ∨ valuation q 124 = false ∨ valuation q 128 = false := by
  rw [value46, value124, value125, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (472 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 83 = false ∨ valuation q 104 = false ∨ valuation q 121 = false := by
  rw [value83, value104, value121, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (346 : Vertex) (410 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 83 = false ∨ valuation q 104 = false ∨ valuation q 124 = false := by
  rw [value83, value104, value124, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (346 : Vertex) (410 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 83 = false ∨ valuation q 104 = false ∨ valuation q 128 = false := by
  rw [value83, value104, value125, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (346 : Vertex) (410 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 83 = false ∨ valuation q 121 = false ∨ valuation q 124 = false := by
  rw [value83, value121, value124, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (346 : Vertex) (466 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 83 = false ∨ valuation q 121 = false ∨ valuation q 128 = false := by
  rw [value83, value121, value125, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (346 : Vertex) (466 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 83 = false ∨ valuation q 124 = false ∨ valuation q 128 = false := by
  rw [value83, value124, value125, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (346 : Vertex) (472 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 104 = false ∨ valuation q 121 = false ∨ valuation q 124 = false := by
  rw [value104, value121, value124, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (410 : Vertex) (466 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 104 = false ∨ valuation q 121 = false ∨ valuation q 128 = false := by
  rw [value104, value121, value125, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (410 : Vertex) (466 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 125 = false ∨ valuation q 104 = false ∨ valuation q 124 = false ∨ valuation q 128 = false := by
  rw [value104, value124, value125, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (410 : Vertex) (472 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E050.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112050
