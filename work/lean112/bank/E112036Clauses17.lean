import E112036Semantics
import B112E036Inputs
namespace Snake9.Regrowth.E112036
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 38 = false ∨ valuation q 75 = false ∨ valuation q 100 = false := by
  rw [value38, value75, value97, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (171 : Vertex) (299 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 38 = false ∨ valuation q 75 = false ∨ valuation q 109 = false := by
  rw [value38, value75, value97, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (171 : Vertex) (299 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 38 = false ∨ valuation q 75 = false ∨ valuation q 117 = false := by
  rw [value38, value75, value97, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (171 : Vertex) (299 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 38 = false ∨ valuation q 96 = false ∨ valuation q 100 = false := by
  rw [value38, value96, value97, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (171 : Vertex) (426 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 38 = false ∨ valuation q 96 = false ∨ valuation q 109 = false := by
  rw [value38, value96, value97, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (171 : Vertex) (426 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 38 = false ∨ valuation q 96 = false ∨ valuation q 117 = false := by
  rw [value38, value96, value97, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (171 : Vertex) (426 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 38 = false ∨ valuation q 100 = false ∨ valuation q 109 = false := by
  rw [value38, value97, value100, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (171 : Vertex) (431 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 38 = false ∨ valuation q 100 = false ∨ valuation q 117 = false := by
  rw [value38, value97, value100, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (171 : Vertex) (431 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 38 = false ∨ valuation q 109 = false ∨ valuation q 117 = false := by
  rw [value38, value97, value109, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (171 : Vertex) (443 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 75 = false ∨ valuation q 96 = false ∨ valuation q 100 = false := by
  rw [value75, value96, value97, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (299 : Vertex) (426 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 75 = false ∨ valuation q 96 = false ∨ valuation q 109 = false := by
  rw [value75, value96, value97, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (299 : Vertex) (426 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 75 = false ∨ valuation q 96 = false ∨ valuation q 117 = false := by
  rw [value75, value96, value97, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (299 : Vertex) (426 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 75 = false ∨ valuation q 100 = false ∨ valuation q 109 = false := by
  rw [value75, value97, value100, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (299 : Vertex) (431 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 75 = false ∨ valuation q 100 = false ∨ valuation q 117 = false := by
  rw [value75, value97, value100, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (299 : Vertex) (431 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 75 = false ∨ valuation q 109 = false ∨ valuation q 117 = false := by
  rw [value75, value97, value109, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (299 : Vertex) (443 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 96 = false ∨ valuation q 100 = false ∨ valuation q 109 = false := by
  rw [value96, value97, value100, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (426 : Vertex) (431 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 96 = false ∨ valuation q 100 = false ∨ valuation q 117 = false := by
  rw [value96, value97, value100, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (426 : Vertex) (431 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 96 = false ∨ valuation q 109 = false ∨ valuation q 117 = false := by
  rw [value96, value97, value109, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (426 : Vertex) (443 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 100 = false ∨ valuation q 109 = false ∨ valuation q 117 = false := by
  rw [value97, value100, value109, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (427 : Vertex) (431 : Vertex) (443 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 225 = true ∨ valuation q 38 = true ∨ valuation q 96 = true ∨ valuation q 100 = true ∨ valuation q 109 = true ∨ valuation q 117 = true := by
  rw [value38, value96, value97, value100, value109, value117, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (427 : Vertex) w → w ∈ region → w ≠ (299 : Vertex) → w ∈ [(171 : Vertex), (426 : Vertex), (431 : Vertex), (443 : Vertex), (491 : Vertex)] := by decide
  have hg := other_cover q (427 : Vertex) (299 : Vertex) [(171 : Vertex), (426 : Vertex), (431 : Vertex), (443 : Vertex), (491 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 226 = true ∨ valuation q 95 = true ∨ valuation q 99 = true := by
  rw [value95, value98, value99, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (428 : Vertex) w → w ∈ region → w ≠ (420 : Vertex) → w ∈ [(424 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (428 : Vertex) (420 : Vertex) [(424 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 226 = true ∨ valuation q 91 = true ∨ valuation q 99 = true := by
  rw [value91, value98, value99, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (428 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(420 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (428 : Vertex) (424 : Vertex) [(420 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 226 = true ∨ valuation q 91 = true ∨ valuation q 95 = true := by
  rw [value91, value95, value98, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (428 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(420 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (428 : Vertex) (430 : Vertex) [(420 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 93 = false ∨ valuation q 96 = false ∨ valuation q 98 = false := by
  rw [value93, value96, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (422 : Vertex) (426 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 93 = false ∨ valuation q 96 = false ∨ valuation q 100 = false := by
  rw [value93, value96, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (422 : Vertex) (426 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 93 = false ∨ valuation q 98 = false ∨ valuation q 100 = false := by
  rw [value93, value98, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (422 : Vertex) (428 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 96 = false ∨ valuation q 98 = false ∨ valuation q 100 = false := by
  rw [value96, value98, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (426 : Vertex) (428 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 93 = false ∨ valuation q 96 = false := by
  rw [value93, value96, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (430 : Vertex) (422 : Vertex) (426 : Vertex) (by decide) (by decide) (by decide)

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 96 = false ∨ valuation q 98 = false := by
  rw [value96, value98, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (430 : Vertex) (426 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide)

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 98 = false ∨ valuation q 100 = false := by
  rw [value98, value100, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (430 : Vertex) (428 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide)

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 227 = true ∨ valuation q 93 = true ∨ valuation q 98 = true ∨ valuation q 100 = true := by
  rw [value93, value98, value99, value100, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (426 : Vertex) → w ∈ [(422 : Vertex), (428 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (426 : Vertex) [(422 : Vertex), (428 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 227 = true ∨ valuation q 93 = true ∨ valuation q 96 = true ∨ valuation q 100 = true := by
  rw [value93, value96, value99, value100, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (428 : Vertex) → w ∈ [(422 : Vertex), (426 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (428 : Vertex) [(422 : Vertex), (426 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block17 (q : Snake 81) (h : Conditions q) : B112E036.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112036
