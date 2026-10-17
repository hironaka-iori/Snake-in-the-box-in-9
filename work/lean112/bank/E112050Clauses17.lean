import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 100 = false ∨ valuation q 101 = false := by
  rw [value100, value101, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (404 : Vertex) (405 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide)

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 227 = true ∨ valuation q 88 = true ∨ valuation q 101 = true := by
  rw [value88, value99, value101, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (404 : Vertex) w → w ∈ region → w ≠ (405 : Vertex) → w ∈ [(388 : Vertex), (406 : Vertex)] := by decide
  have hg := other_cover q (404 : Vertex) (405 : Vertex) [(388 : Vertex), (406 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 227 = true ∨ valuation q 88 = true ∨ valuation q 100 = true := by
  rw [value88, value99, value100, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (404 : Vertex) w → w ∈ region → w ≠ (406 : Vertex) → w ∈ [(388 : Vertex), (405 : Vertex)] := by decide
  have hg := other_cover q (404 : Vertex) (406 : Vertex) [(388 : Vertex), (405 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 89 = false ∨ valuation q 98 = false ∨ valuation q 99 = false := by
  rw [value89, value98, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (405 : Vertex) (389 : Vertex) (401 : Vertex) (404 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 89 = false ∨ valuation q 98 = false ∨ valuation q 102 = false := by
  rw [value89, value98, value100, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (405 : Vertex) (389 : Vertex) (401 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 89 = false ∨ valuation q 99 = false ∨ valuation q 106 = false := by
  rw [value89, value99, value100, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (405 : Vertex) (389 : Vertex) (404 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 89 = false ∨ valuation q 102 = false ∨ valuation q 106 = false := by
  rw [value89, value100, value102, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (405 : Vertex) (389 : Vertex) (407 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 98 = false ∨ valuation q 99 = false ∨ valuation q 102 = false := by
  rw [value98, value99, value100, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (405 : Vertex) (401 : Vertex) (404 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 228 = true ∨ valuation q 98 = true ∨ valuation q 99 = true ∨ valuation q 102 = true ∨ valuation q 106 = true := by
  rw [value98, value99, value100, value102, value106, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(401 : Vertex), (404 : Vertex), (407 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (405 : Vertex) (389 : Vertex) [(401 : Vertex), (404 : Vertex), (407 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 228 = true ∨ valuation q 89 = true ∨ valuation q 99 = true ∨ valuation q 102 = true ∨ valuation q 106 = true := by
  rw [value89, value99, value100, value102, value106, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(389 : Vertex), (404 : Vertex), (407 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (405 : Vertex) (401 : Vertex) [(389 : Vertex), (404 : Vertex), (407 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 228 = true ∨ valuation q 89 = true ∨ valuation q 98 = true ∨ valuation q 102 = true ∨ valuation q 106 = true := by
  rw [value89, value98, value100, value102, value106, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ≠ (404 : Vertex) → w ∈ [(389 : Vertex), (401 : Vertex), (407 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (405 : Vertex) (404 : Vertex) [(389 : Vertex), (401 : Vertex), (407 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 228 = true ∨ valuation q 89 = true ∨ valuation q 98 = true ∨ valuation q 99 = true ∨ valuation q 106 = true := by
  rw [value89, value98, value99, value100, value106, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(389 : Vertex), (401 : Vertex), (404 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (405 : Vertex) (407 : Vertex) [(389 : Vertex), (401 : Vertex), (404 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 228 = true ∨ valuation q 89 = true ∨ valuation q 98 = true ∨ valuation q 99 = true ∨ valuation q 102 = true := by
  rw [value89, value98, value99, value100, value102, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (405 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(389 : Vertex), (401 : Vertex), (404 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (405 : Vertex) (413 : Vertex) [(389 : Vertex), (401 : Vertex), (404 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 90 = false ∨ valuation q 99 = false ∨ valuation q 107 = false := by
  rw [value90, value99, value101, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (406 : Vertex) (390 : Vertex) (404 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 229 = true ∨ valuation q 99 = true ∨ valuation q 102 = true ∨ valuation q 107 = true := by
  rw [value99, value101, value102, value107, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (390 : Vertex) → w ∈ [(404 : Vertex), (407 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (390 : Vertex) [(404 : Vertex), (407 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 229 = true ∨ valuation q 90 = true ∨ valuation q 102 = true ∨ valuation q 107 = true := by
  rw [value90, value101, value102, value107, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (404 : Vertex) → w ∈ [(390 : Vertex), (407 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (404 : Vertex) [(390 : Vertex), (407 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 229 = true ∨ valuation q 90 = true ∨ valuation q 99 = true ∨ valuation q 107 = true := by
  rw [value90, value99, value101, value107, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(390 : Vertex), (404 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (407 : Vertex) [(390 : Vertex), (404 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 229 = true ∨ valuation q 90 = true ∨ valuation q 99 = true ∨ valuation q 102 = true := by
  rw [value90, value99, value101, value102, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(390 : Vertex), (404 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (414 : Vertex) [(390 : Vertex), (404 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 27 = false ∨ valuation q 62 = false ∨ valuation q 91 = false := by
  rw [value27, value62, value91, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (279 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 27 = false ∨ valuation q 62 = false ∨ valuation q 100 = false := by
  rw [value27, value62, value100, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (279 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 27 = false ∨ valuation q 62 = false ∨ valuation q 101 = false := by
  rw [value27, value62, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (279 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 27 = false ∨ valuation q 62 = false ∨ valuation q 108 = false := by
  rw [value27, value62, value102, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (279 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 27 = false ∨ valuation q 62 = false ∨ valuation q 123 = false := by
  rw [value27, value62, value102, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (279 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 27 = false ∨ valuation q 91 = false ∨ valuation q 100 = false := by
  rw [value27, value91, value100, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (391 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 27 = false ∨ valuation q 91 = false ∨ valuation q 101 = false := by
  rw [value27, value91, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (391 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 27 = false ∨ valuation q 91 = false ∨ valuation q 108 = false := by
  rw [value27, value91, value102, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (391 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 27 = false ∨ valuation q 91 = false ∨ valuation q 123 = false := by
  rw [value27, value91, value102, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (391 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 27 = false ∨ valuation q 100 = false ∨ valuation q 101 = false := by
  rw [value27, value100, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (405 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 27 = false ∨ valuation q 100 = false ∨ valuation q 108 = false := by
  rw [value27, value100, value102, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (405 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 27 = false ∨ valuation q 100 = false ∨ valuation q 123 = false := by
  rw [value27, value100, value102, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (405 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 27 = false ∨ valuation q 101 = false ∨ valuation q 108 = false := by
  rw [value27, value101, value102, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (406 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 27 = false ∨ valuation q 101 = false ∨ valuation q 123 = false := by
  rw [value27, value101, value102, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (407 : Vertex) (151 : Vertex) (406 : Vertex) (471 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E050.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112050
