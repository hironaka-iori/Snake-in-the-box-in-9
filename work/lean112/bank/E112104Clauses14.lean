import E112104Semantics
import B112E104Inputs
namespace Snake9.Regrowth.E112104
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 109 = false ∨ valuation q 112 = false ∨ valuation q 118 = false := by
  rw [value109, value112, value113, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (503 : Vertex) (499 : Vertex) (502 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 111 = false ∨ valuation q 112 = false ∨ valuation q 118 = false := by
  rw [value111, value112, value113, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (503 : Vertex) (501 : Vertex) (502 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 231 = true ∨ valuation q 101 = true ∨ valuation q 111 = true ∨ valuation q 112 = true ∨ valuation q 118 = true := by
  rw [value101, value111, value112, value113, value118, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (503 : Vertex) w → w ∈ region → w ≠ (499 : Vertex) → w ∈ [(487 : Vertex), (501 : Vertex), (502 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (503 : Vertex) (499 : Vertex) [(487 : Vertex), (501 : Vertex), (502 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 231 = true ∨ valuation q 101 = true ∨ valuation q 109 = true ∨ valuation q 111 = true ∨ valuation q 118 = true := by
  rw [value101, value109, value111, value113, value118, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (503 : Vertex) w → w ∈ region → w ≠ (502 : Vertex) → w ∈ [(487 : Vertex), (499 : Vertex), (501 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (503 : Vertex) (502 : Vertex) [(487 : Vertex), (499 : Vertex), (501 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 232 = true ∨ valuation q 115 = true := by
  rw [value114, value115, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (504 : Vertex) w → w ∈ region → w ≠ (488 : Vertex) → w ∈ [(505 : Vertex)] := by decide
  have hg := other_cover q (504 : Vertex) (488 : Vertex) [(505 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 232 = true ∨ valuation q 102 = true := by
  rw [value102, value114, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (504 : Vertex) w → w ∈ region → w ≠ (505 : Vertex) → w ∈ [(488 : Vertex)] := by decide
  have hg := other_cover q (504 : Vertex) (505 : Vertex) [(488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 103 = false ∨ valuation q 114 = false ∨ valuation q 117 = false := by
  rw [value103, value114, value115, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (505 : Vertex) (489 : Vertex) (504 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 233 = true ∨ valuation q 114 = true ∨ valuation q 116 = true ∨ valuation q 117 = true := by
  rw [value114, value115, value116, value117, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (505 : Vertex) w → w ∈ region → w ≠ (489 : Vertex) → w ∈ [(504 : Vertex), (507 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (505 : Vertex) (489 : Vertex) [(504 : Vertex), (507 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 233 = true ∨ valuation q 103 = true ∨ valuation q 116 = true ∨ valuation q 117 = true := by
  rw [value103, value115, value116, value117, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (505 : Vertex) w → w ∈ region → w ≠ (504 : Vertex) → w ∈ [(489 : Vertex), (507 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (505 : Vertex) (504 : Vertex) [(489 : Vertex), (507 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 233 = true ∨ valuation q 103 = true ∨ valuation q 114 = true ∨ valuation q 117 = true := by
  rw [value103, value114, value115, value117, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (505 : Vertex) w → w ∈ region → w ≠ (507 : Vertex) → w ∈ [(489 : Vertex), (504 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (505 : Vertex) (507 : Vertex) [(489 : Vertex), (504 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 105 = false ∨ valuation q 109 = false ∨ valuation q 115 = false := by
  rw [value105, value109, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (507 : Vertex) (491 : Vertex) (499 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 105 = false ∨ valuation q 109 = false ∨ valuation q 118 = false := by
  rw [value105, value109, value116, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (507 : Vertex) (491 : Vertex) (499 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 105 = false ∨ valuation q 115 = false ∨ valuation q 118 = false := by
  rw [value105, value115, value116, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (507 : Vertex) (491 : Vertex) (505 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 109 = false ∨ valuation q 115 = false ∨ valuation q 118 = false := by
  rw [value109, value115, value116, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (507 : Vertex) (499 : Vertex) (505 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 234 = true ∨ valuation q 105 = true ∨ valuation q 115 = true ∨ valuation q 118 = true := by
  rw [value105, value115, value116, value118, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (507 : Vertex) w → w ∈ region → w ≠ (499 : Vertex) → w ∈ [(491 : Vertex), (505 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (507 : Vertex) (499 : Vertex) [(491 : Vertex), (505 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 234 = true ∨ valuation q 105 = true ∨ valuation q 109 = true ∨ valuation q 118 = true := by
  rw [value105, value109, value116, value118, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (507 : Vertex) w → w ∈ region → w ≠ (505 : Vertex) → w ∈ [(491 : Vertex), (499 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (507 : Vertex) (505 : Vertex) [(491 : Vertex), (499 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 44 = false ∨ valuation q 76 = false ∨ valuation q 93 = false := by
  rw [value44, value76, value93, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (253 : Vertex) (381 : Vertex) (445 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 44 = false ∨ valuation q 76 = false ∨ valuation q 107 = false := by
  rw [value44, value76, value107, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (253 : Vertex) (381 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 44 = false ∨ valuation q 76 = false ∨ valuation q 111 = false := by
  rw [value44, value76, value111, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (253 : Vertex) (381 : Vertex) (501 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 44 = false ∨ valuation q 76 = false ∨ valuation q 115 = false := by
  rw [value44, value76, value115, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (253 : Vertex) (381 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 44 = false ∨ valuation q 76 = false ∨ valuation q 118 = false := by
  rw [value44, value76, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (253 : Vertex) (381 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 44 = false ∨ valuation q 93 = false ∨ valuation q 107 = false := by
  rw [value44, value93, value107, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (253 : Vertex) (445 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 44 = false ∨ valuation q 93 = false ∨ valuation q 111 = false := by
  rw [value44, value93, value111, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (253 : Vertex) (445 : Vertex) (501 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 44 = false ∨ valuation q 93 = false ∨ valuation q 115 = false := by
  rw [value44, value93, value115, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (253 : Vertex) (445 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 44 = false ∨ valuation q 93 = false ∨ valuation q 118 = false := by
  rw [value44, value93, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (253 : Vertex) (445 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 44 = false ∨ valuation q 107 = false ∨ valuation q 111 = false := by
  rw [value44, value107, value111, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (253 : Vertex) (493 : Vertex) (501 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 44 = false ∨ valuation q 107 = false ∨ valuation q 115 = false := by
  rw [value44, value107, value115, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (253 : Vertex) (493 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 44 = false ∨ valuation q 107 = false ∨ valuation q 118 = false := by
  rw [value44, value107, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (253 : Vertex) (493 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 44 = false ∨ valuation q 111 = false ∨ valuation q 115 = false := by
  rw [value44, value111, value115, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (253 : Vertex) (501 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 76 = false ∨ valuation q 93 = false ∨ valuation q 107 = false := by
  rw [value76, value93, value107, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (381 : Vertex) (445 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 76 = false ∨ valuation q 93 = false ∨ valuation q 111 = false := by
  rw [value76, value93, value111, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (381 : Vertex) (445 : Vertex) (501 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 76 = false ∨ valuation q 93 = false ∨ valuation q 115 = false := by
  rw [value76, value93, value115, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (381 : Vertex) (445 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E104.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112104
