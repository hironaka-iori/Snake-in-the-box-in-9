import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 21 = false ∨ valuation q 82 = false ∨ valuation q 109 = false := by
  rw [value21, value79, value82, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (360 : Vertex) (104 : Vertex) (376 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 80 = false ∨ valuation q 82 = false ∨ valuation q 109 = false := by
  rw [value79, value80, value82, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (360 : Vertex) (361 : Vertex) (376 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 199 = false ∨ valuation q 21 = false ∨ valuation q 80 = false := by
  rw [value21, value80, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (360 : Vertex) (104 : Vertex) (361 : Vertex) (by decide) (by decide) (by decide)

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 199 = true ∨ valuation q 80 = true ∨ valuation q 82 = true ∨ valuation q 109 = true := by
  rw [value79, value80, value82, value109, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (360 : Vertex) w → w ∈ region → w ≠ (104 : Vertex) → w ∈ [(361 : Vertex), (376 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (360 : Vertex) (104 : Vertex) [(361 : Vertex), (376 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 199 = true ∨ valuation q 21 = true ∨ valuation q 82 = true ∨ valuation q 109 = true := by
  rw [value21, value79, value82, value109, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (360 : Vertex) w → w ∈ region → w ≠ (361 : Vertex) → w ∈ [(104 : Vertex), (376 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (360 : Vertex) (361 : Vertex) [(104 : Vertex), (376 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 199 = true ∨ valuation q 21 = true ∨ valuation q 80 = true ∨ valuation q 109 = true := by
  rw [value21, value79, value80, value109, value199]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (360 : Vertex) w → w ∈ region → w ≠ (376 : Vertex) → w ∈ [(104 : Vertex), (361 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (360 : Vertex) (376 : Vertex) [(104 : Vertex), (361 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 200 = true ∨ valuation q 81 = true := by
  rw [value80, value81, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (361 : Vertex) w → w ∈ region → w ≠ (360 : Vertex) → w ∈ [(363 : Vertex)] := by decide
  have hg := other_cover q (361 : Vertex) (360 : Vertex) [(363 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 200 = true ∨ valuation q 79 = true := by
  rw [value79, value80, value200]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (361 : Vertex) w → w ∈ region → w ≠ (363 : Vertex) → w ∈ [(360 : Vertex)] := by decide
  have hg := other_cover q (361 : Vertex) (363 : Vertex) [(360 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 201 = false ∨ valuation q 81 = true := by
  rw [value81, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (363 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 201 = false ∨ valuation q 80 = false ∨ valuation q 83 = false := by
  rw [value80, value83, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (363 : Vertex) (361 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide)

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 201 = true ∨ valuation q 83 = true := by
  rw [value81, value83, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (363 : Vertex) w → w ∈ region → w ≠ (361 : Vertex) → w ∈ [(379 : Vertex)] := by decide
  have hg := other_cover q (363 : Vertex) (361 : Vertex) [(379 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 201 = true ∨ valuation q 80 = true := by
  rw [value80, value81, value201]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (363 : Vertex) w → w ∈ region → w ≠ (379 : Vertex) → w ∈ [(361 : Vertex)] := by decide
  have hg := other_cover q (363 : Vertex) (379 : Vertex) [(361 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 202 = true ∨ valuation q 79 = true := by
  rw [value79, value82, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (376 : Vertex) w → w ∈ region → w ≠ (120 : Vertex) → w ∈ [(360 : Vertex)] := by decide
  have hg := other_cover q (376 : Vertex) (120 : Vertex) [(360 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 202 = true ∨ valuation q 29 = true := by
  rw [value29, value82, value202]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (376 : Vertex) w → w ∈ region → w ≠ (360 : Vertex) → w ∈ [(120 : Vertex)] := by decide
  have hg := other_cover q (376 : Vertex) (360 : Vertex) [(120 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 31 = false ∨ valuation q 77 = false ∨ valuation q 81 = false := by
  rw [value31, value77, value81, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (379 : Vertex) (123 : Vertex) (315 : Vertex) (363 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 31 = false ∨ valuation q 77 = false ∨ valuation q 118 = false := by
  rw [value31, value77, value83, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (379 : Vertex) (123 : Vertex) (315 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 31 = false ∨ valuation q 81 = false ∨ valuation q 118 = false := by
  rw [value31, value81, value83, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (379 : Vertex) (123 : Vertex) (363 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 77 = false ∨ valuation q 81 = false ∨ valuation q 118 = false := by
  rw [value77, value81, value83, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (379 : Vertex) (315 : Vertex) (363 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 203 = true ∨ valuation q 77 = true ∨ valuation q 81 = true ∨ valuation q 118 = true := by
  rw [value77, value81, value83, value118, value203]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (379 : Vertex) w → w ∈ region → w ≠ (123 : Vertex) → w ∈ [(315 : Vertex), (363 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (379 : Vertex) (123 : Vertex) [(315 : Vertex), (363 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 34 = false ∨ valuation q 89 = false ∨ valuation q 104 = false := by
  rw [value34, value84, value89, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (160 : Vertex) (424 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 34 = false ∨ valuation q 94 = false ∨ valuation q 104 = false := by
  rw [value34, value84, value94, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (160 : Vertex) (432 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 89 = false ∨ valuation q 104 = false := by
  rw [value84, value85, value89, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (420 : Vertex) (424 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 85 = false ∨ valuation q 94 = false ∨ valuation q 104 = false := by
  rw [value84, value85, value94, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (416 : Vertex) (420 : Vertex) (432 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 204 = true ∨ valuation q 34 = true ∨ valuation q 89 = true ∨ valuation q 94 = true ∨ valuation q 104 = true := by
  rw [value34, value84, value89, value94, value104, value204]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (416 : Vertex) w → w ∈ region → w ≠ (420 : Vertex) → w ∈ [(160 : Vertex), (424 : Vertex), (432 : Vertex), (480 : Vertex)] := by decide
  have hg := other_cover q (416 : Vertex) (420 : Vertex) [(160 : Vertex), (424 : Vertex), (432 : Vertex), (480 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 84 = false ∨ valuation q 86 = false ∨ valuation q 87 = false := by
  rw [value84, value85, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (420 : Vertex) (416 : Vertex) (421 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 205 = false ∨ valuation q 86 = false ∨ valuation q 87 = false := by
  rw [value86, value87, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (420 : Vertex) (421 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide)

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 205 = true ∨ valuation q 86 = true ∨ valuation q 87 = true := by
  rw [value85, value86, value87, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (420 : Vertex) w → w ∈ region → w ≠ (416 : Vertex) → w ∈ [(421 : Vertex), (422 : Vertex)] := by decide
  have hg := other_cover q (420 : Vertex) (416 : Vertex) [(421 : Vertex), (422 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 205 = true ∨ valuation q 84 = true ∨ valuation q 87 = true := by
  rw [value84, value85, value87, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (420 : Vertex) w → w ∈ region → w ≠ (421 : Vertex) → w ∈ [(416 : Vertex), (422 : Vertex)] := by decide
  have hg := other_cover q (420 : Vertex) (421 : Vertex) [(416 : Vertex), (422 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 205 = true ∨ valuation q 84 = true ∨ valuation q 86 = true := by
  rw [value84, value85, value86, value205]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (420 : Vertex) w → w ∈ region → w ≠ (422 : Vertex) → w ∈ [(416 : Vertex), (421 : Vertex)] := by decide
  have hg := other_cover q (420 : Vertex) (422 : Vertex) [(416 : Vertex), (421 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 206 = true ∨ valuation q 88 = true ∨ valuation q 96 = true := by
  rw [value86, value88, value96, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (420 : Vertex) → w ∈ [(423 : Vertex), (437 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (420 : Vertex) [(423 : Vertex), (437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 206 = true ∨ valuation q 85 = true ∨ valuation q 96 = true := by
  rw [value85, value86, value96, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (423 : Vertex) → w ∈ [(420 : Vertex), (437 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (423 : Vertex) [(420 : Vertex), (437 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 206 = true ∨ valuation q 85 = true ∨ valuation q 88 = true := by
  rw [value85, value86, value88, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (421 : Vertex) w → w ∈ region → w ≠ (437 : Vertex) → w ∈ [(420 : Vertex), (423 : Vertex)] := by decide
  have hg := other_cover q (421 : Vertex) (437 : Vertex) [(420 : Vertex), (423 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block17 (q : Snake 81) (h : Conditions q) : B112E004.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112004
