import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 88 = false ∨ valuation q 98 = false ∨ valuation q 101 = false := by
  rw [value88, value98, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (405 : Vertex) (389 : Vertex) (404 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 88 = false ∨ valuation q 98 = false ∨ valuation q 105 = false := by
  rw [value88, value98, value99, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (405 : Vertex) (389 : Vertex) (404 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 88 = false ∨ valuation q 101 = false ∨ valuation q 105 = false := by
  rw [value88, value99, value101, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (405 : Vertex) (389 : Vertex) (407 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 97 = false ∨ valuation q 98 = false ∨ valuation q 101 = false := by
  rw [value97, value98, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (405 : Vertex) (401 : Vertex) (404 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 226 = true ∨ valuation q 97 = true ∨ valuation q 98 = true ∨ valuation q 101 = true ∨ valuation q 105 = true := by
  rw [value97, value98, value99, value101, value105, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(401 : Vertex), (404 : Vertex), (407 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (405 : Vertex) (389 : Vertex) [(401 : Vertex), (404 : Vertex), (407 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 226 = true ∨ valuation q 88 = true ∨ valuation q 98 = true ∨ valuation q 101 = true ∨ valuation q 105 = true := by
  rw [value88, value98, value99, value101, value105, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(389 : Vertex), (404 : Vertex), (407 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (405 : Vertex) (401 : Vertex) [(389 : Vertex), (404 : Vertex), (407 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 226 = true ∨ valuation q 88 = true ∨ valuation q 97 = true ∨ valuation q 101 = true ∨ valuation q 105 = true := by
  rw [value88, value97, value99, value101, value105, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ≠ (404 : Vertex) → w ∈ [(389 : Vertex), (401 : Vertex), (407 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (405 : Vertex) (404 : Vertex) [(389 : Vertex), (401 : Vertex), (407 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 226 = true ∨ valuation q 88 = true ∨ valuation q 97 = true ∨ valuation q 98 = true ∨ valuation q 105 = true := by
  rw [value88, value97, value98, value99, value105, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(389 : Vertex), (401 : Vertex), (404 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (405 : Vertex) (407 : Vertex) [(389 : Vertex), (401 : Vertex), (404 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 226 = true ∨ valuation q 88 = true ∨ valuation q 97 = true ∨ valuation q 98 = true ∨ valuation q 101 = true := by
  rw [value88, value97, value98, value99, value101, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(389 : Vertex), (401 : Vertex), (404 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (405 : Vertex) (413 : Vertex) [(389 : Vertex), (401 : Vertex), (404 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 89 = true ∨ valuation q 98 = true ∨ valuation q 101 = true ∨ valuation q 106 = true := by
  rw [value89, value98, value100, value101, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ∈ [(390 : Vertex), (404 : Vertex), (407 : Vertex), (414 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (406 : Vertex) [(390 : Vertex), (404 : Vertex), (407 : Vertex), (414 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 89 = false ∨ valuation q 98 = false ∨ valuation q 101 = false := by
  rw [value89, value98, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (406 : Vertex) (390 : Vertex) (404 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 89 = false ∨ valuation q 98 = false ∨ valuation q 106 = false := by
  rw [value89, value98, value100, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (406 : Vertex) (390 : Vertex) (404 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 89 = false ∨ valuation q 101 = false ∨ valuation q 106 = false := by
  rw [value89, value100, value101, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (406 : Vertex) (390 : Vertex) (407 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 98 = false ∨ valuation q 101 = false ∨ valuation q 106 = false := by
  rw [value98, value100, value101, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (406 : Vertex) (404 : Vertex) (407 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 227 = true ∨ valuation q 98 = true ∨ valuation q 101 = true ∨ valuation q 106 = true := by
  rw [value98, value100, value101, value106, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (390 : Vertex) → w ∈ [(404 : Vertex), (407 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (390 : Vertex) [(404 : Vertex), (407 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 227 = true ∨ valuation q 89 = true ∨ valuation q 101 = true ∨ valuation q 106 = true := by
  rw [value89, value100, value101, value106, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (404 : Vertex) → w ∈ [(390 : Vertex), (407 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (404 : Vertex) [(390 : Vertex), (407 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 227 = true ∨ valuation q 89 = true ∨ valuation q 98 = true ∨ valuation q 106 = true := by
  rw [value89, value98, value100, value106, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(390 : Vertex), (404 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (407 : Vertex) [(390 : Vertex), (404 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 227 = true ∨ valuation q 89 = true ∨ valuation q 98 = true ∨ valuation q 101 = true := by
  rw [value89, value98, value100, value101, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(390 : Vertex), (404 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (414 : Vertex) [(390 : Vertex), (404 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 27 = false ∨ valuation q 62 = false ∨ valuation q 90 = false := by
  rw [value27, value62, value90, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (279 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 27 = false ∨ valuation q 62 = false ∨ valuation q 99 = false := by
  rw [value27, value62, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (279 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 27 = false ∨ valuation q 62 = false ∨ valuation q 100 = false := by
  rw [value27, value62, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (279 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 27 = false ∨ valuation q 62 = false ∨ valuation q 107 = false := by
  rw [value27, value62, value101, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (279 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 27 = false ∨ valuation q 62 = false ∨ valuation q 122 = false := by
  rw [value27, value62, value101, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (279 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 27 = false ∨ valuation q 90 = false ∨ valuation q 99 = false := by
  rw [value27, value90, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (391 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 27 = false ∨ valuation q 90 = false ∨ valuation q 100 = false := by
  rw [value27, value90, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (391 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 27 = false ∨ valuation q 90 = false ∨ valuation q 107 = false := by
  rw [value27, value90, value101, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (391 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 27 = false ∨ valuation q 90 = false ∨ valuation q 122 = false := by
  rw [value27, value90, value101, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (391 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 27 = false ∨ valuation q 99 = false ∨ valuation q 100 = false := by
  rw [value27, value99, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (405 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 27 = false ∨ valuation q 99 = false ∨ valuation q 107 = false := by
  rw [value27, value99, value101, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (405 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 27 = false ∨ valuation q 99 = false ∨ valuation q 122 = false := by
  rw [value27, value99, value101, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (405 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 27 = false ∨ valuation q 100 = false ∨ valuation q 107 = false := by
  rw [value27, value100, value101, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (406 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 27 = false ∨ valuation q 100 = false ∨ valuation q 122 = false := by
  rw [value27, value100, value101, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (406 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E052.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112052
