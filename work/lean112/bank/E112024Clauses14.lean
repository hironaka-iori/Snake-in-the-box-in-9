import E112024Semantics
import B112E024Inputs
namespace Snake9.Regrowth.E112024
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 212 = true ∨ valuation q 88 = true ∨ valuation q 92 = true := by
  rw [value88, value91, value92, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (428 : Vertex) w → w ∈ region → w ≠ (420 : Vertex) → w ∈ [(424 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (428 : Vertex) (420 : Vertex) [(424 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 212 = true ∨ valuation q 84 = true ∨ valuation q 92 = true := by
  rw [value84, value91, value92, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (428 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(420 : Vertex), (430 : Vertex)] := by decide
  have hg := other_cover q (428 : Vertex) (424 : Vertex) [(420 : Vertex), (430 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 91 = false ∨ valuation q 212 = true ∨ valuation q 84 = true ∨ valuation q 88 = true := by
  rw [value84, value88, value91, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (428 : Vertex) w → w ∈ region → w ≠ (430 : Vertex) → w ∈ [(420 : Vertex), (424 : Vertex)] := by decide
  have hg := other_cover q (428 : Vertex) (430 : Vertex) [(420 : Vertex), (424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 86 = false ∨ valuation q 89 = false ∨ valuation q 91 = false := by
  rw [value86, value89, value91, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (422 : Vertex) (426 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 86 = false ∨ valuation q 89 = false ∨ valuation q 93 = false := by
  rw [value86, value89, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (422 : Vertex) (426 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 86 = false ∨ valuation q 91 = false ∨ valuation q 93 = false := by
  rw [value86, value91, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (422 : Vertex) (428 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 89 = false ∨ valuation q 91 = false ∨ valuation q 93 = false := by
  rw [value89, value91, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (430 : Vertex) (426 : Vertex) (428 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 213 = true ∨ valuation q 86 = true ∨ valuation q 89 = true ∨ valuation q 93 = true := by
  rw [value86, value89, value92, value93, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (430 : Vertex) w → w ∈ region → w ≠ (428 : Vertex) → w ∈ [(422 : Vertex), (426 : Vertex), (431 : Vertex)] := by decide
  have hg := other_cover q (430 : Vertex) (428 : Vertex) [(422 : Vertex), (426 : Vertex), (431 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 57 = false ∨ valuation q 87 = false ∨ valuation q 103 = false := by
  rw [value57, value87, value93, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (303 : Vertex) (423 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 57 = false ∨ valuation q 87 = false ∨ valuation q 112 = false := by
  rw [value57, value87, value93, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (303 : Vertex) (423 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 87 = false ∨ valuation q 90 = false ∨ valuation q 92 = false := by
  rw [value87, value90, value92, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (423 : Vertex) (427 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 87 = false ∨ valuation q 90 = false ∨ valuation q 103 = false := by
  rw [value87, value90, value93, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (423 : Vertex) (427 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 23 = false ∨ valuation q 59 = false ∨ valuation q 97 = false := by
  rw [value23, value59, value94, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (305 : Vertex) (437 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 23 = false ∨ valuation q 59 = false ∨ valuation q 100 = false := by
  rw [value23, value59, value94, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (305 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 23 = false ∨ valuation q 95 = false ∨ valuation q 113 = false := by
  rw [value23, value94, value95, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (177 : Vertex) (435 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 59 = false ∨ valuation q 95 = false ∨ valuation q 113 = false := by
  rw [value59, value94, value95, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (305 : Vertex) (435 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 59 = false ∨ valuation q 97 = false ∨ valuation q 100 = false := by
  rw [value59, value94, value97, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (305 : Vertex) (437 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 25 = false ∨ valuation q 61 = false ∨ valuation q 98 = false := by
  rw [value25, value61, value95, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (307 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 25 = false ∨ valuation q 61 = false ∨ valuation q 102 = false := by
  rw [value25, value61, value95, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (307 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 25 = false ∨ valuation q 61 = false ∨ valuation q 115 = false := by
  rw [value25, value61, value95, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (307 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 25 = false ∨ valuation q 94 = false ∨ valuation q 98 = false := by
  rw [value25, value94, value95, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (433 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 25 = false ∨ valuation q 94 = false ∨ valuation q 102 = false := by
  rw [value25, value94, value95, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (433 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 25 = false ∨ valuation q 94 = false ∨ valuation q 115 = false := by
  rw [value25, value94, value95, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (433 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 25 = false ∨ valuation q 98 = false ∨ valuation q 102 = false := by
  rw [value25, value95, value98, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (439 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 25 = false ∨ valuation q 98 = false ∨ valuation q 115 = false := by
  rw [value25, value95, value98, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (439 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 25 = false ∨ valuation q 102 = false ∨ valuation q 115 = false := by
  rw [value25, value95, value102, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (179 : Vertex) (443 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 61 = false ∨ valuation q 94 = false ∨ valuation q 102 = false := by
  rw [value61, value94, value95, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (433 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 61 = false ∨ valuation q 94 = false ∨ valuation q 115 = false := by
  rw [value61, value94, value95, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (433 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 61 = false ∨ valuation q 98 = false ∨ valuation q 102 = false := by
  rw [value61, value95, value98, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (439 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 61 = false ∨ valuation q 98 = false ∨ valuation q 115 = false := by
  rw [value61, value95, value98, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (439 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 61 = false ∨ valuation q 102 = false ∨ valuation q 115 = false := by
  rw [value61, value95, value102, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (307 : Vertex) (443 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 94 = false ∨ valuation q 98 = false ∨ valuation q 102 = false := by
  rw [value94, value95, value98, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (435 : Vertex) (433 : Vertex) (439 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E024.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112024
