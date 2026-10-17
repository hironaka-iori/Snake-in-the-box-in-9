import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 98 = false ∨ valuation q 99 = false ∨ valuation q 101 = false := by
  rw [value97, value98, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (408 : Vertex) (409 : Vertex) (410 : Vertex) (412 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 221 = true ∨ valuation q 98 = true ∨ valuation q 99 = true ∨ valuation q 101 = true := by
  rw [value97, value98, value99, value101, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (408 : Vertex) w → w ∈ region → w ≠ (392 : Vertex) → w ∈ [(409 : Vertex), (410 : Vertex), (412 : Vertex)] := by decide
  have hg := other_cover q (408 : Vertex) (392 : Vertex) [(409 : Vertex), (410 : Vertex), (412 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 221 = true ∨ valuation q 89 = true ∨ valuation q 98 = true ∨ valuation q 99 = true := by
  rw [value89, value97, value98, value99, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (408 : Vertex) w → w ∈ region → w ≠ (412 : Vertex) → w ∈ [(392 : Vertex), (409 : Vertex), (410 : Vertex)] := by decide
  have hg := other_cover q (408 : Vertex) (412 : Vertex) [(392 : Vertex), (409 : Vertex), (410 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 222 = false ∨ valuation q 98 = true := by
  rw [value98, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (409 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 90 = true ∨ valuation q 97 = true ∨ valuation q 100 = true := by
  rw [value90, value97, value98, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ∈ [(393 : Vertex), (408 : Vertex), (411 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (409 : Vertex) [(393 : Vertex), (408 : Vertex), (411 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 90 = false ∨ valuation q 97 = false ∨ valuation q 100 = false := by
  rw [value90, value97, value98, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (409 : Vertex) (393 : Vertex) (408 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 222 = false ∨ valuation q 90 = false ∨ valuation q 97 = false := by
  rw [value90, value97, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (409 : Vertex) (393 : Vertex) (408 : Vertex) (by decide) (by decide) (by decide)

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 222 = false ∨ valuation q 90 = false ∨ valuation q 100 = false := by
  rw [value90, value100, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (409 : Vertex) (393 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide)

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 222 = true ∨ valuation q 97 = true ∨ valuation q 100 = true := by
  rw [value97, value98, value100, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(408 : Vertex), (411 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (393 : Vertex) [(408 : Vertex), (411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 222 = true ∨ valuation q 90 = true ∨ valuation q 100 = true := by
  rw [value90, value98, value100, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (408 : Vertex) → w ∈ [(393 : Vertex), (411 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (408 : Vertex) [(393 : Vertex), (411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 222 = true ∨ valuation q 90 = true ∨ valuation q 97 = true := by
  rw [value90, value97, value98, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (411 : Vertex) → w ∈ [(393 : Vertex), (408 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (411 : Vertex) [(393 : Vertex), (408 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 43 = false ∨ valuation q 97 = false ∨ valuation q 100 = false := by
  rw [value43, value97, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (410 : Vertex) (154 : Vertex) (408 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 43 = false ∨ valuation q 97 = false ∨ valuation q 120 = false := by
  rw [value43, value97, value99, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (410 : Vertex) (154 : Vertex) (408 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 43 = false ∨ valuation q 100 = false ∨ valuation q 120 = false := by
  rw [value43, value99, value100, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (410 : Vertex) (154 : Vertex) (411 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 97 = false ∨ valuation q 100 = false ∨ valuation q 120 = false := by
  rw [value97, value99, value100, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (410 : Vertex) (408 : Vertex) (411 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 223 = true ∨ valuation q 97 = true ∨ valuation q 100 = true ∨ valuation q 120 = true := by
  rw [value97, value99, value100, value120, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (154 : Vertex) → w ∈ [(408 : Vertex), (411 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (154 : Vertex) [(408 : Vertex), (411 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 223 = true ∨ valuation q 43 = true ∨ valuation q 97 = true ∨ valuation q 120 = true := by
  rw [value43, value97, value99, value120, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (410 : Vertex) w → w ∈ region → w ≠ (411 : Vertex) → w ∈ [(154 : Vertex), (408 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (410 : Vertex) (411 : Vertex) [(154 : Vertex), (408 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 93 = false ∨ valuation q 98 = false ∨ valuation q 99 = false := by
  rw [value93, value98, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (411 : Vertex) (403 : Vertex) (409 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 224 = true ∨ valuation q 98 = true ∨ valuation q 99 = true := by
  rw [value98, value99, value100, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (411 : Vertex) w → w ∈ region → w ≠ (403 : Vertex) → w ∈ [(409 : Vertex), (410 : Vertex)] := by decide
  have hg := other_cover q (411 : Vertex) (403 : Vertex) [(409 : Vertex), (410 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 224 = true ∨ valuation q 93 = true ∨ valuation q 99 = true := by
  rw [value93, value99, value100, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (411 : Vertex) w → w ∈ region → w ≠ (409 : Vertex) → w ∈ [(403 : Vertex), (410 : Vertex)] := by decide
  have hg := other_cover q (411 : Vertex) (409 : Vertex) [(403 : Vertex), (410 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 225 = false ∨ valuation q 101 = true := by
  rw [value101, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (412 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 94 = true ∨ valuation q 97 = true ∨ valuation q 121 = true := by
  rw [value94, value97, value101, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ∈ [(404 : Vertex), (408 : Vertex), (476 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (412 : Vertex) [(404 : Vertex), (408 : Vertex), (476 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 94 = false ∨ valuation q 97 = false ∨ valuation q 121 = false := by
  rw [value94, value97, value101, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (412 : Vertex) (404 : Vertex) (408 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 225 = false ∨ valuation q 94 = false ∨ valuation q 121 = false := by
  rw [value94, value121, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (412 : Vertex) (404 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide)

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 225 = false ∨ valuation q 97 = false ∨ valuation q 121 = false := by
  rw [value97, value121, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (412 : Vertex) (408 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide)

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 225 = true ∨ valuation q 97 = true ∨ valuation q 121 = true := by
  rw [value97, value101, value121, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (404 : Vertex) → w ∈ [(408 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (404 : Vertex) [(408 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 225 = true ∨ valuation q 94 = true ∨ valuation q 121 = true := by
  rw [value94, value101, value121, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (408 : Vertex) → w ∈ [(404 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (408 : Vertex) [(404 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 225 = true ∨ valuation q 94 = true ∨ valuation q 97 = true := by
  rw [value94, value97, value101, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (412 : Vertex) w → w ∈ region → w ≠ (476 : Vertex) → w ∈ [(404 : Vertex), (408 : Vertex)] := by decide
  have hg := other_cover q (412 : Vertex) (476 : Vertex) [(404 : Vertex), (408 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 47 = false ∨ valuation q 67 = false ∨ valuation q 84 = false := by
  rw [value47, value67, value84, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (192 : Vertex) (320 : Vertex) (384 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 47 = false ∨ valuation q 67 = false ∨ valuation q 103 = false := by
  rw [value47, value67, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (192 : Vertex) (320 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 47 = false ∨ valuation q 67 = false ∨ valuation q 104 = false := by
  rw [value47, value67, value102, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (192 : Vertex) (320 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 47 = false ∨ valuation q 67 = false ∨ valuation q 114 = false := by
  rw [value47, value67, value102, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (192 : Vertex) (320 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E105.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112105
