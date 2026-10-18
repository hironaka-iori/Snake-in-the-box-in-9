import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 80 = false ∨ valuation q 98 = false ∨ valuation q 106 = false := by
  rw [value80, value97, value98, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (360 : Vertex) (296 : Vertex) (361 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 80 = false ∨ valuation q 99 = false ∨ valuation q 106 = false := by
  rw [value80, value97, value99, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (360 : Vertex) (296 : Vertex) (362 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 92 = false ∨ valuation q 98 = false ∨ valuation q 99 = false := by
  rw [value92, value97, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (360 : Vertex) (352 : Vertex) (361 : Vertex) (362 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 92 = false ∨ valuation q 98 = false ∨ valuation q 106 = false := by
  rw [value92, value97, value98, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (360 : Vertex) (352 : Vertex) (361 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 92 = false ∨ valuation q 99 = false ∨ valuation q 106 = false := by
  rw [value92, value97, value99, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (360 : Vertex) (352 : Vertex) (362 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 98 = false ∨ valuation q 99 = false ∨ valuation q 106 = false := by
  rw [value97, value98, value99, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (360 : Vertex) (361 : Vertex) (362 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 217 = true ∨ valuation q 80 = true ∨ valuation q 92 = true ∨ valuation q 99 = true ∨ valuation q 106 = true := by
  rw [value80, value92, value97, value99, value106, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (360 : Vertex) w → w ∈ region → w ≠ (361 : Vertex) → w ∈ [(296 : Vertex), (352 : Vertex), (362 : Vertex), (376 : Vertex)] := by decide
  have hg := other_cover q (360 : Vertex) (361 : Vertex) [(296 : Vertex), (352 : Vertex), (362 : Vertex), (376 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 25 = false ∨ valuation q 97 = false ∨ valuation q 100 = false := by
  rw [value25, value97, value98, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (361 : Vertex) (105 : Vertex) (360 : Vertex) (363 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 25 = false ∨ valuation q 97 = false ∨ valuation q 107 = false := by
  rw [value25, value97, value98, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (361 : Vertex) (105 : Vertex) (360 : Vertex) (377 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 25 = false ∨ valuation q 100 = false ∨ valuation q 107 = false := by
  rw [value25, value98, value100, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (361 : Vertex) (105 : Vertex) (363 : Vertex) (377 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 218 = true ∨ valuation q 97 = true ∨ valuation q 100 = true ∨ valuation q 107 = true := by
  rw [value97, value98, value100, value107, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (361 : Vertex) w → w ∈ region → w ≠ (105 : Vertex) → w ∈ [(360 : Vertex), (363 : Vertex), (377 : Vertex)] := by decide
  have hg := other_cover q (361 : Vertex) (105 : Vertex) [(360 : Vertex), (363 : Vertex), (377 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 218 = true ∨ valuation q 25 = true ∨ valuation q 100 = true ∨ valuation q 107 = true := by
  rw [value25, value98, value100, value107, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (361 : Vertex) w → w ∈ region → w ≠ (360 : Vertex) → w ∈ [(105 : Vertex), (363 : Vertex), (377 : Vertex)] := by decide
  have hg := other_cover q (361 : Vertex) (360 : Vertex) [(105 : Vertex), (363 : Vertex), (377 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 218 = true ∨ valuation q 25 = true ∨ valuation q 97 = true ∨ valuation q 107 = true := by
  rw [value25, value97, value98, value107, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (361 : Vertex) w → w ∈ region → w ≠ (363 : Vertex) → w ∈ [(105 : Vertex), (360 : Vertex), (377 : Vertex)] := by decide
  have hg := other_cover q (361 : Vertex) (363 : Vertex) [(105 : Vertex), (360 : Vertex), (377 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 218 = true ∨ valuation q 25 = true ∨ valuation q 97 = true ∨ valuation q 100 = true := by
  rw [value25, value97, value98, value100, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (361 : Vertex) w → w ∈ region → w ≠ (377 : Vertex) → w ∈ [(105 : Vertex), (360 : Vertex), (363 : Vertex)] := by decide
  have hg := other_cover q (361 : Vertex) (377 : Vertex) [(105 : Vertex), (360 : Vertex), (363 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 97 = false ∨ valuation q 101 = false ∨ valuation q 108 = false := by
  rw [value97, value99, value101, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (362 : Vertex) (360 : Vertex) (366 : Vertex) (378 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 100 = false ∨ valuation q 101 = false ∨ valuation q 108 = false := by
  rw [value99, value100, value101, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (362 : Vertex) (363 : Vertex) (366 : Vertex) (378 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 219 = true ∨ valuation q 97 = true ∨ valuation q 101 = true ∨ valuation q 108 = true := by
  rw [value97, value99, value101, value108, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (362 : Vertex) w → w ∈ region → w ≠ (363 : Vertex) → w ∈ [(360 : Vertex), (366 : Vertex), (378 : Vertex)] := by decide
  have hg := other_cover q (362 : Vertex) (363 : Vertex) [(360 : Vertex), (366 : Vertex), (378 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 219 = true ∨ valuation q 97 = true ∨ valuation q 100 = true ∨ valuation q 108 = true := by
  rw [value97, value99, value100, value108, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (362 : Vertex) w → w ∈ region → w ≠ (366 : Vertex) → w ∈ [(360 : Vertex), (363 : Vertex), (378 : Vertex)] := by decide
  have hg := other_cover q (362 : Vertex) (366 : Vertex) [(360 : Vertex), (363 : Vertex), (378 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 219 = true ∨ valuation q 97 = true ∨ valuation q 100 = true ∨ valuation q 101 = true := by
  rw [value97, value99, value100, value101, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (362 : Vertex) w → w ∈ region → w ≠ (378 : Vertex) → w ∈ [(360 : Vertex), (363 : Vertex), (366 : Vertex)] := by decide
  have hg := other_cover q (362 : Vertex) (378 : Vertex) [(360 : Vertex), (363 : Vertex), (366 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 26 = false ∨ valuation q 98 = false ∨ valuation q 99 = false := by
  rw [value26, value98, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (107 : Vertex) (361 : Vertex) (362 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 26 = false ∨ valuation q 98 = false ∨ valuation q 109 = false := by
  rw [value26, value98, value100, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (107 : Vertex) (361 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 26 = false ∨ valuation q 99 = false ∨ valuation q 109 = false := by
  rw [value26, value99, value100, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (107 : Vertex) (362 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 98 = false ∨ valuation q 99 = false ∨ valuation q 109 = false := by
  rw [value98, value99, value100, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (363 : Vertex) (361 : Vertex) (362 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 220 = true ∨ valuation q 26 = true ∨ valuation q 99 = true ∨ valuation q 109 = true := by
  rw [value26, value99, value100, value109, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (363 : Vertex) w → w ∈ region → w ≠ (361 : Vertex) → w ∈ [(107 : Vertex), (362 : Vertex), (379 : Vertex)] := by decide
  have hg := other_cover q (363 : Vertex) (361 : Vertex) [(107 : Vertex), (362 : Vertex), (379 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 95 = false ∨ valuation q 99 = false ∨ valuation q 111 = false := by
  rw [value95, value99, value101, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (366 : Vertex) (358 : Vertex) (362 : Vertex) (382 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 221 = true ∨ valuation q 99 = true ∨ valuation q 111 = true := by
  rw [value99, value101, value111, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (366 : Vertex) w → w ∈ region → w ≠ (358 : Vertex) → w ∈ [(362 : Vertex), (382 : Vertex)] := by decide
  have hg := other_cover q (366 : Vertex) (358 : Vertex) [(362 : Vertex), (382 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 221 = true ∨ valuation q 95 = true ∨ valuation q 111 = true := by
  rw [value95, value101, value111, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (366 : Vertex) w → w ∈ region → w ≠ (362 : Vertex) → w ∈ [(358 : Vertex), (382 : Vertex)] := by decide
  have hg := other_cover q (366 : Vertex) (362 : Vertex) [(358 : Vertex), (382 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 221 = true ∨ valuation q 95 = true ∨ valuation q 99 = true := by
  rw [value95, value99, value101, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (366 : Vertex) w → w ∈ region → w ≠ (382 : Vertex) → w ∈ [(358 : Vertex), (362 : Vertex)] := by decide
  have hg := other_cover q (366 : Vertex) (382 : Vertex) [(358 : Vertex), (362 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 30 = false ∨ valuation q 92 = false ∨ valuation q 106 = false := by
  rw [value30, value92, value102, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (368 : Vertex) (112 : Vertex) (352 : Vertex) (376 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 222 = true ∨ valuation q 30 = true ∨ valuation q 92 = true := by
  rw [value30, value92, value102, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (368 : Vertex) w → w ∈ region → w ≠ (376 : Vertex) → w ∈ [(112 : Vertex), (352 : Vertex)] := by decide
  have hg := other_cover q (368 : Vertex) (376 : Vertex) [(112 : Vertex), (352 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 32 = false ∨ valuation q 105 = false ∨ valuation q 109 = false := by
  rw [value32, value103, value105, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (371 : Vertex) (115 : Vertex) (375 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 85 = false ∨ valuation q 105 = false ∨ valuation q 109 = false := by
  rw [value85, value103, value105, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (371 : Vertex) (307 : Vertex) (375 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E040.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112040
