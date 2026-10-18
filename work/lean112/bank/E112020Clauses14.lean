import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 202 = true ∨ valuation q 79 = true ∨ valuation q 82 = true ∨ valuation q 115 = true := by
  rw [value78, value79, value82, value115, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (370 : Vertex) w → w ∈ region → w ≠ (114 : Vertex) → w ∈ [(371 : Vertex), (378 : Vertex), (498 : Vertex)] := by decide
  have hg := other_cover q (370 : Vertex) (114 : Vertex) [(371 : Vertex), (378 : Vertex), (498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 202 = true ∨ valuation q 26 = true ∨ valuation q 82 = true ∨ valuation q 115 = true := by
  rw [value26, value78, value82, value115, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (370 : Vertex) w → w ∈ region → w ≠ (371 : Vertex) → w ∈ [(114 : Vertex), (378 : Vertex), (498 : Vertex)] := by decide
  have hg := other_cover q (370 : Vertex) (371 : Vertex) [(114 : Vertex), (378 : Vertex), (498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 202 = true ∨ valuation q 26 = true ∨ valuation q 79 = true ∨ valuation q 115 = true := by
  rw [value26, value78, value79, value115, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (370 : Vertex) w → w ∈ region → w ≠ (378 : Vertex) → w ∈ [(114 : Vertex), (371 : Vertex), (498 : Vertex)] := by decide
  have hg := other_cover q (370 : Vertex) (378 : Vertex) [(114 : Vertex), (371 : Vertex), (498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 78 = false ∨ valuation q 202 = true ∨ valuation q 26 = true ∨ valuation q 79 = true ∨ valuation q 82 = true := by
  rw [value26, value78, value79, value82, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (370 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(114 : Vertex), (371 : Vertex), (378 : Vertex)] := by decide
  have hg := other_cover q (370 : Vertex) (498 : Vertex) [(114 : Vertex), (371 : Vertex), (378 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 27 = false ∨ valuation q 78 = false ∨ valuation q 83 = false := by
  rw [value27, value78, value79, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (371 : Vertex) (115 : Vertex) (370 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 27 = false ∨ valuation q 78 = false ∨ valuation q 116 = false := by
  rw [value27, value78, value79, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (371 : Vertex) (115 : Vertex) (370 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 78 = false ∨ valuation q 83 = false ∨ valuation q 116 = false := by
  rw [value78, value79, value83, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (371 : Vertex) (370 : Vertex) (379 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 203 = true ∨ valuation q 27 = true ∨ valuation q 83 = true ∨ valuation q 116 = true := by
  rw [value27, value79, value83, value116, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (371 : Vertex) w → w ∈ region → w ≠ (370 : Vertex) → w ∈ [(115 : Vertex), (379 : Vertex), (499 : Vertex)] := by decide
  have hg := other_cover q (371 : Vertex) (370 : Vertex) [(115 : Vertex), (379 : Vertex), (499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 203 = true ∨ valuation q 27 = true ∨ valuation q 78 = true ∨ valuation q 116 = true := by
  rw [value27, value78, value79, value116, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (371 : Vertex) w → w ∈ region → w ≠ (379 : Vertex) → w ∈ [(115 : Vertex), (370 : Vertex), (499 : Vertex)] := by decide
  have hg := other_cover q (371 : Vertex) (379 : Vertex) [(115 : Vertex), (370 : Vertex), (499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 28 = false ∨ valuation q 72 = false ∨ valuation q 81 = false := by
  rw [value28, value72, value80, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (372 : Vertex) (116 : Vertex) (356 : Vertex) (373 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 72 = false ∨ valuation q 81 = false ∨ valuation q 117 = false := by
  rw [value72, value80, value81, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (372 : Vertex) (356 : Vertex) (373 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 205 = true ∨ valuation q 80 = true := by
  rw [value80, value81, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (373 : Vertex) w → w ∈ region → w ≠ (381 : Vertex) → w ∈ [(372 : Vertex)] := by decide
  have hg := other_cover q (373 : Vertex) (381 : Vertex) [(372 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 30 = false ∨ valuation q 76 = false ∨ valuation q 78 = false := by
  rw [value30, value76, value78, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (122 : Vertex) (362 : Vertex) (370 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 30 = false ∨ valuation q 76 = false ∨ valuation q 83 = false := by
  rw [value30, value76, value82, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (122 : Vertex) (362 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 30 = false ∨ valuation q 78 = false ∨ valuation q 83 = false := by
  rw [value30, value78, value82, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (122 : Vertex) (370 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 76 = false ∨ valuation q 78 = false ∨ valuation q 83 = false := by
  rw [value76, value78, value82, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (378 : Vertex) (362 : Vertex) (370 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 79 = false ∨ valuation q 82 = false ∨ valuation q 85 = false := by
  rw [value79, value82, value83, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (379 : Vertex) (371 : Vertex) (378 : Vertex) (383 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 79 = false ∨ valuation q 85 = false ∨ valuation q 120 = false := by
  rw [value79, value83, value85, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (379 : Vertex) (371 : Vertex) (383 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 82 = false ∨ valuation q 85 = false ∨ valuation q 120 = false := by
  rw [value82, value83, value85, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (379 : Vertex) (378 : Vertex) (383 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 207 = true ∨ valuation q 82 = true ∨ valuation q 85 = true ∨ valuation q 120 = true := by
  rw [value82, value83, value85, value120, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (379 : Vertex) w → w ∈ region → w ≠ (371 : Vertex) → w ∈ [(378 : Vertex), (383 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (379 : Vertex) (371 : Vertex) [(378 : Vertex), (383 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 207 = true ∨ valuation q 79 = true ∨ valuation q 85 = true ∨ valuation q 120 = true := by
  rw [value79, value83, value85, value120, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (379 : Vertex) w → w ∈ region → w ≠ (378 : Vertex) → w ∈ [(371 : Vertex), (383 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (379 : Vertex) (378 : Vertex) [(371 : Vertex), (383 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 207 = true ∨ valuation q 79 = true ∨ valuation q 82 = true ∨ valuation q 120 = true := by
  rw [value79, value82, value83, value120, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (379 : Vertex) w → w ∈ region → w ≠ (383 : Vertex) → w ∈ [(371 : Vertex), (378 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (379 : Vertex) (383 : Vertex) [(371 : Vertex), (378 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 207 = true ∨ valuation q 79 = true ∨ valuation q 82 = true ∨ valuation q 85 = true := by
  rw [value79, value82, value83, value85, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (379 : Vertex) w → w ∈ region → w ≠ (507 : Vertex) → w ∈ [(371 : Vertex), (378 : Vertex), (383 : Vertex)] := by decide
  have hg := other_cover q (379 : Vertex) (507 : Vertex) [(371 : Vertex), (378 : Vertex), (383 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 81 = false ∨ valuation q 85 = false ∨ valuation q 122 = false := by
  rw [value81, value84, value85, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (381 : Vertex) (373 : Vertex) (383 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 208 = true ∨ valuation q 85 = true ∨ valuation q 122 = true := by
  rw [value84, value85, value122, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (381 : Vertex) w → w ∈ region → w ≠ (373 : Vertex) → w ∈ [(383 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (381 : Vertex) (373 : Vertex) [(383 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 208 = true ∨ valuation q 81 = true ∨ valuation q 122 = true := by
  rw [value81, value84, value122, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (381 : Vertex) w → w ∈ region → w ≠ (383 : Vertex) → w ∈ [(373 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (381 : Vertex) (383 : Vertex) [(373 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 208 = true ∨ valuation q 81 = true ∨ valuation q 85 = true := by
  rw [value81, value84, value85, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (381 : Vertex) w → w ∈ region → w ≠ (509 : Vertex) → w ∈ [(373 : Vertex), (383 : Vertex)] := by decide
  have hg := other_cover q (381 : Vertex) (509 : Vertex) [(373 : Vertex), (383 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 83 = true ∨ valuation q 84 = true ∨ valuation q 124 = true := by
  rw [value83, value84, value85, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (383 : Vertex) w → w ∈ region → w ∈ [(379 : Vertex), (381 : Vertex), (511 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (383 : Vertex) [(379 : Vertex), (381 : Vertex), (511 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 83 = false ∨ valuation q 84 = false ∨ valuation q 124 = false := by
  rw [value83, value84, value85, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (383 : Vertex) (379 : Vertex) (381 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 209 = true ∨ valuation q 83 = true ∨ valuation q 124 = true := by
  rw [value83, value85, value124, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (383 : Vertex) w → w ∈ region → w ≠ (381 : Vertex) → w ∈ [(379 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (383 : Vertex) (381 : Vertex) [(379 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 34 = false ∨ valuation q 91 = false ∨ valuation q 103 = false := by
  rw [value34, value86, value91, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (417 : Vertex) (161 : Vertex) (425 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 210 = false ∨ valuation q 34 = false ∨ valuation q 91 = false := by
  rw [value34, value91, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (417 : Vertex) (161 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E020.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112020
