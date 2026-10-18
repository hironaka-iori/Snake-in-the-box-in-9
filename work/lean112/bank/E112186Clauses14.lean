import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 83 = false ∨ valuation q 94 = false ∨ valuation q 100 = false := by
  rw [value83, value94, value95, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (385 : Vertex) (400 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 83 = false ∨ valuation q 97 = false ∨ valuation q 100 = false := by
  rw [value83, value95, value97, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (385 : Vertex) (403 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 94 = false ∨ valuation q 97 = false ∨ valuation q 100 = false := by
  rw [value94, value95, value97, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (400 : Vertex) (403 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 219 = true ∨ valuation q 94 = true ∨ valuation q 97 = true ∨ valuation q 100 = true := by
  rw [value94, value95, value97, value100, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ≠ (385 : Vertex) → w ∈ [(400 : Vertex), (403 : Vertex), (409 : Vertex)] := by decide
  have hg := other_cover q (401 : Vertex) (385 : Vertex) [(400 : Vertex), (403 : Vertex), (409 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 84 = false ∨ valuation q 94 = false ∨ valuation q 98 = false := by
  rw [value84, value94, value96, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (386 : Vertex) (400 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 84 = false ∨ valuation q 94 = false ∨ valuation q 101 = false := by
  rw [value84, value94, value96, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (386 : Vertex) (400 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 84 = false ∨ valuation q 97 = false ∨ valuation q 98 = false := by
  rw [value84, value96, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (386 : Vertex) (403 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 84 = false ∨ valuation q 97 = false ∨ valuation q 101 = false := by
  rw [value84, value96, value97, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (386 : Vertex) (403 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 84 = false ∨ valuation q 98 = false ∨ valuation q 101 = false := by
  rw [value84, value96, value98, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (386 : Vertex) (406 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 94 = false ∨ valuation q 97 = false ∨ valuation q 98 = false := by
  rw [value94, value96, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (400 : Vertex) (403 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 94 = false ∨ valuation q 97 = false ∨ valuation q 101 = false := by
  rw [value94, value96, value97, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (400 : Vertex) (403 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 94 = false ∨ valuation q 98 = false ∨ valuation q 101 = false := by
  rw [value94, value96, value98, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (400 : Vertex) (406 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 97 = false ∨ valuation q 98 = false ∨ valuation q 101 = false := by
  rw [value96, value97, value98, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (402 : Vertex) (403 : Vertex) (406 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 221 = true ∨ valuation q 95 = true ∨ valuation q 96 = true := by
  rw [value95, value96, value97, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (387 : Vertex) → w ∈ [(401 : Vertex), (402 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (387 : Vertex) [(401 : Vertex), (402 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 221 = true ∨ valuation q 85 = true ∨ valuation q 96 = true := by
  rw [value85, value96, value97, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (401 : Vertex) → w ∈ [(387 : Vertex), (402 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (401 : Vertex) [(387 : Vertex), (402 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 221 = true ∨ valuation q 85 = true ∨ valuation q 95 = true := by
  rw [value85, value95, value97, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (403 : Vertex) w → w ∈ region → w ≠ (402 : Vertex) → w ∈ [(387 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (403 : Vertex) (402 : Vertex) [(387 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 24 = false ∨ valuation q 96 = false ∨ valuation q 104 = false := by
  rw [value24, value96, value98, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (406 : Vertex) (150 : Vertex) (402 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 222 = true ∨ valuation q 96 = true ∨ valuation q 104 = true := by
  rw [value96, value98, value104, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (150 : Vertex) → w ∈ [(402 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (150 : Vertex) [(402 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 222 = true ∨ valuation q 24 = true ∨ valuation q 104 = true := by
  rw [value24, value98, value104, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (402 : Vertex) → w ∈ [(150 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (402 : Vertex) [(150 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 222 = true ∨ valuation q 24 = true ∨ valuation q 96 = true := by
  rw [value24, value96, value98, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (406 : Vertex) w → w ∈ region → w ≠ (414 : Vertex) → w ∈ [(150 : Vertex), (402 : Vertex)] := by decide
  have hg := other_cover q (406 : Vertex) (414 : Vertex) [(150 : Vertex), (402 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 26 = false ∨ valuation q 60 = false ∨ valuation q 100 = false := by
  rw [value26, value60, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (152 : Vertex) (280 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 26 = false ∨ valuation q 60 = false ∨ valuation q 101 = false := by
  rw [value26, value60, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (152 : Vertex) (280 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 26 = false ∨ valuation q 60 = false ∨ valuation q 102 = false := by
  rw [value26, value60, value99, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (152 : Vertex) (280 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 26 = false ∨ valuation q 100 = false ∨ valuation q 101 = false := by
  rw [value26, value99, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (152 : Vertex) (409 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 26 = false ∨ valuation q 100 = false ∨ valuation q 102 = false := by
  rw [value26, value99, value100, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (152 : Vertex) (409 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 26 = false ∨ valuation q 101 = false ∨ valuation q 102 = false := by
  rw [value26, value99, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (152 : Vertex) (410 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 60 = false ∨ valuation q 94 = false ∨ valuation q 100 = false := by
  rw [value60, value94, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (280 : Vertex) (400 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 60 = false ∨ valuation q 94 = false ∨ valuation q 101 = false := by
  rw [value60, value94, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (280 : Vertex) (400 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 60 = false ∨ valuation q 94 = false ∨ valuation q 102 = false := by
  rw [value60, value94, value99, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (280 : Vertex) (400 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 60 = false ∨ valuation q 100 = false ∨ valuation q 101 = false := by
  rw [value60, value99, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (280 : Vertex) (409 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 60 = false ∨ valuation q 100 = false ∨ valuation q 102 = false := by
  rw [value60, value99, value100, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (280 : Vertex) (409 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 60 = false ∨ valuation q 101 = false ∨ valuation q 102 = false := by
  rw [value60, value99, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (280 : Vertex) (410 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E186.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112186
