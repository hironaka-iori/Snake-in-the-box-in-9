import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 213 = true ∨ valuation q 50 = true ∨ valuation q 85 = true ∨ valuation q 89 = true ∨ valuation q 93 = true := by
  rw [value50, value85, value86, value89, value93, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (130 : Vertex) → w ∈ [(258 : Vertex), (384 : Vertex), (390 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (130 : Vertex) [(258 : Vertex), (384 : Vertex), (390 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 213 = true ∨ valuation q 14 = true ∨ valuation q 85 = true ∨ valuation q 89 = true ∨ valuation q 93 = true := by
  rw [value14, value85, value86, value89, value93, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (258 : Vertex) → w ∈ [(130 : Vertex), (384 : Vertex), (390 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (258 : Vertex) [(130 : Vertex), (384 : Vertex), (390 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 213 = true ∨ valuation q 14 = true ∨ valuation q 50 = true ∨ valuation q 89 = true ∨ valuation q 93 = true := by
  rw [value14, value50, value86, value89, value93, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (384 : Vertex) → w ∈ [(130 : Vertex), (258 : Vertex), (390 : Vertex), (394 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (384 : Vertex) [(130 : Vertex), (258 : Vertex), (390 : Vertex), (394 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 213 = true ∨ valuation q 14 = true ∨ valuation q 50 = true ∨ valuation q 85 = true ∨ valuation q 89 = true := by
  rw [value14, value50, value85, value86, value89, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (386 : Vertex) w → w ∈ region → w ≠ (394 : Vertex) → w ∈ [(130 : Vertex), (258 : Vertex), (384 : Vertex), (390 : Vertex)] := by decide
  have hg := other_cover q (386 : Vertex) (394 : Vertex) [(130 : Vertex), (258 : Vertex), (384 : Vertex), (390 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 16 = false ∨ valuation q 52 = false ∨ valuation q 85 = false := by
  rw [value16, value52, value85, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (132 : Vertex) (260 : Vertex) (384 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 16 = false ∨ valuation q 52 = false ∨ valuation q 89 = false := by
  rw [value16, value52, value87, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (132 : Vertex) (260 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 16 = false ∨ valuation q 52 = false ∨ valuation q 98 = false := by
  rw [value16, value52, value87, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (132 : Vertex) (260 : Vertex) (404 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 16 = false ∨ valuation q 85 = false ∨ valuation q 89 = false := by
  rw [value16, value85, value87, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (132 : Vertex) (384 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 16 = false ∨ valuation q 85 = false ∨ valuation q 98 = false := by
  rw [value16, value85, value87, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (132 : Vertex) (384 : Vertex) (404 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 16 = false ∨ valuation q 85 = false ∨ valuation q 111 = false := by
  rw [value16, value85, value87, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (132 : Vertex) (384 : Vertex) (452 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 16 = false ∨ valuation q 89 = false ∨ valuation q 98 = false := by
  rw [value16, value87, value89, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (132 : Vertex) (390 : Vertex) (404 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 16 = false ∨ valuation q 89 = false ∨ valuation q 111 = false := by
  rw [value16, value87, value89, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (132 : Vertex) (390 : Vertex) (452 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 16 = false ∨ valuation q 98 = false ∨ valuation q 111 = false := by
  rw [value16, value87, value98, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (132 : Vertex) (404 : Vertex) (452 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 52 = false ∨ valuation q 85 = false ∨ valuation q 89 = false := by
  rw [value52, value85, value87, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (260 : Vertex) (384 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 52 = false ∨ valuation q 85 = false ∨ valuation q 98 = false := by
  rw [value52, value85, value87, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (260 : Vertex) (384 : Vertex) (404 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 52 = false ∨ valuation q 85 = false ∨ valuation q 111 = false := by
  rw [value52, value85, value87, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (260 : Vertex) (384 : Vertex) (452 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 52 = false ∨ valuation q 89 = false ∨ valuation q 98 = false := by
  rw [value52, value87, value89, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (260 : Vertex) (390 : Vertex) (404 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 52 = false ∨ valuation q 89 = false ∨ valuation q 111 = false := by
  rw [value52, value87, value89, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (260 : Vertex) (390 : Vertex) (452 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 52 = false ∨ valuation q 98 = false ∨ valuation q 111 = false := by
  rw [value52, value87, value98, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (260 : Vertex) (404 : Vertex) (452 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 85 = false ∨ valuation q 88 = false ∨ valuation q 89 = false := by
  rw [value85, value87, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (384 : Vertex) (389 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 85 = false ∨ valuation q 88 = false ∨ valuation q 98 = false := by
  rw [value85, value87, value88, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (384 : Vertex) (389 : Vertex) (404 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 85 = false ∨ valuation q 89 = false ∨ valuation q 98 = false := by
  rw [value85, value87, value89, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (384 : Vertex) (390 : Vertex) (404 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 85 = false ∨ valuation q 89 = false ∨ valuation q 111 = false := by
  rw [value85, value87, value89, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (384 : Vertex) (390 : Vertex) (452 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 85 = false ∨ valuation q 98 = false ∨ valuation q 111 = false := by
  rw [value85, value87, value98, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (384 : Vertex) (404 : Vertex) (452 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 98 = false ∨ valuation q 111 = false := by
  rw [value87, value88, value98, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (388 : Vertex) (389 : Vertex) (404 : Vertex) (452 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 214 = true ∨ valuation q 52 = true ∨ valuation q 85 = true ∨ valuation q 88 = true ∨ valuation q 89 = true ∨ valuation q 98 = true ∨ valuation q 111 = true := by
  rw [value52, value85, value87, value88, value89, value98, value111, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (388 : Vertex) w → w ∈ region → w ≠ (132 : Vertex) → w ∈ [(260 : Vertex), (384 : Vertex), (389 : Vertex), (390 : Vertex), (404 : Vertex), (452 : Vertex)] := by decide
  have hg := other_cover q (388 : Vertex) (132 : Vertex) [(260 : Vertex), (384 : Vertex), (389 : Vertex), (390 : Vertex), (404 : Vertex), (452 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 17 = false ∨ valuation q 53 = false ∨ valuation q 87 = false := by
  rw [value17, value53, value87, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (261 : Vertex) (388 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 17 = false ∨ valuation q 53 = false ∨ valuation q 90 = false := by
  rw [value17, value53, value88, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (261 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 17 = false ∨ valuation q 53 = false ∨ valuation q 95 = false := by
  rw [value17, value53, value88, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (261 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 17 = false ∨ valuation q 53 = false ∨ valuation q 99 = false := by
  rw [value17, value53, value88, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (261 : Vertex) (405 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 17 = false ∨ valuation q 53 = false ∨ valuation q 112 = false := by
  rw [value17, value53, value88, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (261 : Vertex) (453 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 17 = false ∨ valuation q 87 = false ∨ valuation q 90 = false := by
  rw [value17, value87, value88, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (389 : Vertex) (133 : Vertex) (388 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E052.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112052
