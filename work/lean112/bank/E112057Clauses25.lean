import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 220 = false ∨ valuation q 91 = false ∨ valuation q 96 = false := by
  rw [value91, value96, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (322 : Vertex) (320 : Vertex) (330 : Vertex) (by decide) (by decide) (by decide)

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 220 = false ∨ valuation q 94 = false ∨ valuation q 96 = false := by
  rw [value94, value96, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (322 : Vertex) (323 : Vertex) (330 : Vertex) (by decide) (by decide) (by decide)

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 220 = true ∨ valuation q 94 = true ∨ valuation q 96 = true := by
  rw [value93, value94, value96, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (322 : Vertex) w → w ∈ region → w ≠ (320 : Vertex) → w ∈ [(323 : Vertex), (330 : Vertex)] := by decide
  have hg := other_cover q (322 : Vertex) (320 : Vertex) [(323 : Vertex), (330 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 220 = true ∨ valuation q 91 = true ∨ valuation q 94 = true := by
  rw [value91, value93, value94, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (322 : Vertex) w → w ∈ region → w ≠ (330 : Vertex) → w ∈ [(320 : Vertex), (323 : Vertex)] := by decide
  have hg := other_cover q (322 : Vertex) (330 : Vertex) [(320 : Vertex), (323 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 21 = false ∨ valuation q 68 = false ∨ valuation q 93 = false := by
  rw [value21, value68, value93, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (67 : Vertex) (259 : Vertex) (322 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 68 = false ∨ valuation q 92 = false ∨ valuation q 93 = false := by
  rw [value68, value92, value93, value94]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (323 : Vertex) (259 : Vertex) (321 : Vertex) (322 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 221 = true ∨ valuation q 21 = true ∨ valuation q 68 = true ∨ valuation q 92 = true := by
  rw [value21, value68, value92, value94, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (323 : Vertex) w → w ∈ region → w ≠ (322 : Vertex) → w ∈ [(67 : Vertex), (259 : Vertex), (321 : Vertex)] := by decide
  have hg := other_cover q (323 : Vertex) (322 : Vertex) [(67 : Vertex), (259 : Vertex), (321 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 23 = false ∨ valuation q 70 = false ∨ valuation q 98 = false := by
  rw [value23, value70, value95, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (69 : Vertex) (261 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 23 = false ∨ valuation q 92 = false ∨ valuation q 98 = false := by
  rw [value23, value92, value95, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (325 : Vertex) (69 : Vertex) (321 : Vertex) (333 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 222 = true ∨ valuation q 70 = true ∨ valuation q 92 = true ∨ valuation q 98 = true := by
  rw [value70, value92, value95, value98, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (325 : Vertex) w → w ∈ region → w ≠ (69 : Vertex) → w ∈ [(261 : Vertex), (321 : Vertex), (333 : Vertex)] := by decide
  have hg := other_cover q (325 : Vertex) (69 : Vertex) [(261 : Vertex), (321 : Vertex), (333 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 222 = true ∨ valuation q 23 = true ∨ valuation q 92 = true ∨ valuation q 98 = true := by
  rw [value23, value92, value95, value98, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (325 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(69 : Vertex), (321 : Vertex), (333 : Vertex)] := by decide
  have hg := other_cover q (325 : Vertex) (261 : Vertex) [(69 : Vertex), (321 : Vertex), (333 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 222 = true ∨ valuation q 23 = true ∨ valuation q 70 = true ∨ valuation q 98 = true := by
  rw [value23, value70, value95, value98, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (325 : Vertex) w → w ∈ region → w ≠ (321 : Vertex) → w ∈ [(69 : Vertex), (261 : Vertex), (333 : Vertex)] := by decide
  have hg := other_cover q (325 : Vertex) (321 : Vertex) [(69 : Vertex), (261 : Vertex), (333 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 222 = true ∨ valuation q 23 = true ∨ valuation q 70 = true ∨ valuation q 92 = true := by
  rw [value23, value70, value92, value95, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (325 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(69 : Vertex), (261 : Vertex), (321 : Vertex)] := by decide
  have hg := other_cover q (325 : Vertex) (333 : Vertex) [(69 : Vertex), (261 : Vertex), (321 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 223 = true ∨ valuation q 99 = true := by
  rw [value96, value99, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (330 : Vertex) w → w ∈ region → w ≠ (322 : Vertex) → w ∈ [(334 : Vertex)] := by decide
  have hg := other_cover q (330 : Vertex) (322 : Vertex) [(334 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 223 = true ∨ valuation q 93 = true := by
  rw [value93, value96, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (330 : Vertex) w → w ∈ region → w ≠ (334 : Vertex) → w ∈ [(322 : Vertex)] := by decide
  have hg := other_cover q (330 : Vertex) (334 : Vertex) [(322 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 76 = false ∨ valuation q 98 = false ∨ valuation q 99 = false := by
  rw [value76, value97, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (332 : Vertex) (268 : Vertex) (333 : Vertex) (334 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 98 = false ∨ valuation q 99 = false ∨ valuation q 106 = false := by
  rw [value97, value98, value99, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (332 : Vertex) (333 : Vertex) (334 : Vertex) (348 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 224 = true ∨ valuation q 76 = true ∨ valuation q 99 = true ∨ valuation q 106 = true := by
  rw [value76, value97, value99, value106, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (332 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(268 : Vertex), (334 : Vertex), (348 : Vertex)] := by decide
  have hg := other_cover q (332 : Vertex) (333 : Vertex) [(268 : Vertex), (334 : Vertex), (348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 224 = true ∨ valuation q 76 = true ∨ valuation q 98 = true ∨ valuation q 106 = true := by
  rw [value76, value97, value98, value106, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (332 : Vertex) w → w ∈ region → w ≠ (334 : Vertex) → w ∈ [(268 : Vertex), (333 : Vertex), (348 : Vertex)] := by decide
  have hg := other_cover q (332 : Vertex) (334 : Vertex) [(268 : Vertex), (333 : Vertex), (348 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 224 = true ∨ valuation q 76 = true ∨ valuation q 98 = true ∨ valuation q 99 = true := by
  rw [value76, value97, value98, value99, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (332 : Vertex) w → w ∈ region → w ≠ (348 : Vertex) → w ∈ [(268 : Vertex), (333 : Vertex), (334 : Vertex)] := by decide
  have hg := other_cover q (332 : Vertex) (348 : Vertex) [(268 : Vertex), (333 : Vertex), (334 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 77 = false ∨ valuation q 95 = false ∨ valuation q 97 = false := by
  rw [value77, value95, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (333 : Vertex) (269 : Vertex) (325 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 225 = false ∨ valuation q 95 = false ∨ valuation q 97 = false := by
  rw [value95, value97, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (333 : Vertex) (325 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide)

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 225 = true ∨ valuation q 77 = true ∨ valuation q 97 = true := by
  rw [value77, value97, value98, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (325 : Vertex) → w ∈ [(269 : Vertex), (332 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (325 : Vertex) [(269 : Vertex), (332 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 225 = true ∨ valuation q 77 = true ∨ valuation q 95 = true := by
  rw [value77, value95, value98, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (333 : Vertex) w → w ∈ region → w ≠ (332 : Vertex) → w ∈ [(269 : Vertex), (325 : Vertex)] := by decide
  have hg := other_cover q (333 : Vertex) (332 : Vertex) [(269 : Vertex), (325 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 96 = false ∨ valuation q 97 = false ∨ valuation q 107 = false := by
  rw [value96, value97, value99, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (334 : Vertex) (330 : Vertex) (332 : Vertex) (350 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 226 = false ∨ valuation q 96 = false ∨ valuation q 97 = false := by
  rw [value96, value97, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (334 : Vertex) (330 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide)

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 226 = true ∨ valuation q 97 = true ∨ valuation q 107 = true := by
  rw [value97, value99, value107, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (334 : Vertex) w → w ∈ region → w ≠ (330 : Vertex) → w ∈ [(332 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (334 : Vertex) (330 : Vertex) [(332 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 226 = true ∨ valuation q 96 = true ∨ valuation q 107 = true := by
  rw [value96, value99, value107, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (334 : Vertex) w → w ∈ region → w ≠ (332 : Vertex) → w ∈ [(330 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (334 : Vertex) (332 : Vertex) [(330 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 100 = true := by
  rw [value100, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (336 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 30 = false ∨ valuation q 79 = false ∨ valuation q 91 = false := by
  rw [value30, value79, value91, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (336 : Vertex) (80 : Vertex) (272 : Vertex) (320 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 30 = false ∨ valuation q 79 = false ∨ valuation q 101 = false := by
  rw [value30, value79, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (336 : Vertex) (80 : Vertex) (272 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 30 = false ∨ valuation q 91 = false ∨ valuation q 101 = false := by
  rw [value30, value91, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (336 : Vertex) (80 : Vertex) (320 : Vertex) (337 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E057.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112057
