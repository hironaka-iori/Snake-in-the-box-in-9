import E112254Semantics
import B112E254Inputs
namespace Snake9.Regrowth.E112254
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 225 = true ∨ valuation q 68 = true ∨ valuation q 104 = true ∨ valuation q 107 = true := by
  rw [value68, value103, value104, value107, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (454 : Vertex) w → w ∈ region → w ≠ (486 : Vertex) → w ∈ [(390 : Vertex), (455 : Vertex), (470 : Vertex)] := by decide
  have hg := other_cover q (454 : Vertex) (486 : Vertex) [(390 : Vertex), (455 : Vertex), (470 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 45 = false ∨ valuation q 69 = false ∨ valuation q 103 = false := by
  rw [value45, value69, value103, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (455 : Vertex) (327 : Vertex) (391 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 226 = false ∨ valuation q 45 = false ∨ valuation q 69 = false := by
  rw [value45, value69, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (455 : Vertex) (327 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide)

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 226 = false ∨ valuation q 45 = false ∨ valuation q 103 = false := by
  rw [value45, value103, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (455 : Vertex) (327 : Vertex) (454 : Vertex) (by decide) (by decide) (by decide)

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 226 = true ∨ valuation q 69 = true ∨ valuation q 103 = true := by
  rw [value69, value103, value104, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (455 : Vertex) w → w ∈ region → w ≠ (327 : Vertex) → w ∈ [(391 : Vertex), (454 : Vertex)] := by decide
  have hg := other_cover q (455 : Vertex) (327 : Vertex) [(391 : Vertex), (454 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 226 = true ∨ valuation q 45 = true ∨ valuation q 69 = true := by
  rw [value45, value69, value104, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (455 : Vertex) w → w ∈ region → w ≠ (454 : Vertex) → w ∈ [(327 : Vertex), (391 : Vertex)] := by decide
  have hg := other_cover q (455 : Vertex) (454 : Vertex) [(327 : Vertex), (391 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 72 = false ∨ valuation q 106 = false ∨ valuation q 109 = false := by
  rw [value72, value105, value106, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (460 : Vertex) (396 : Vertex) (461 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 227 = true ∨ valuation q 72 = true ∨ valuation q 109 = true ∨ valuation q 116 = true := by
  rw [value72, value105, value109, value116, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (460 : Vertex) w → w ∈ region → w ≠ (461 : Vertex) → w ∈ [(396 : Vertex), (476 : Vertex), (492 : Vertex)] := by decide
  have hg := other_cover q (460 : Vertex) (461 : Vertex) [(396 : Vertex), (476 : Vertex), (492 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 228 = true ∨ valuation q 105 = true := by
  rw [value105, value106, value228]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (461 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(460 : Vertex)] := by decide
  have hg := other_cover q (461 : Vertex) (333 : Vertex) [(460 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 229 = false ∨ valuation q 107 = true := by
  rw [value107, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (470 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 103 = true := by
  rw [value103, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (470 : Vertex) w → w ∈ region → w ∈ [(454 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (470 : Vertex) [(454 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 229 = true := by
  rw [value107, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (470 : Vertex) w → w ∈ region → w ≠ (454 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (470 : Vertex) (454 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 230 = true ∨ valuation q 109 = true ∨ valuation q 120 = true := by
  rw [value108, value109, value120, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (344 : Vertex) → w ∈ [(476 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (344 : Vertex) [(476 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 230 = true ∨ valuation q 50 = true ∨ valuation q 120 = true := by
  rw [value50, value108, value120, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (476 : Vertex) → w ∈ [(344 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (476 : Vertex) [(344 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 230 = true ∨ valuation q 50 = true ∨ valuation q 109 = true := by
  rw [value50, value108, value109, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (504 : Vertex) → w ∈ [(344 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (504 : Vertex) [(344 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 79 = false ∨ valuation q 105 = false ∨ valuation q 108 = false := by
  rw [value79, value105, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (412 : Vertex) (460 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 79 = false ∨ valuation q 105 = false ∨ valuation q 122 = false := by
  rw [value79, value105, value109, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (412 : Vertex) (460 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 79 = false ∨ valuation q 108 = false ∨ valuation q 122 = false := by
  rw [value79, value108, value109, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (412 : Vertex) (472 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 105 = false ∨ valuation q 108 = false ∨ valuation q 122 = false := by
  rw [value105, value108, value109, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (460 : Vertex) (472 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 232 = true ∨ valuation q 112 = true ∨ valuation q 115 = true := by
  rw [value110, value112, value115, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (481 : Vertex) w → w ∈ region → w ≠ (353 : Vertex) → w ∈ [(485 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (481 : Vertex) (353 : Vertex) [(485 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 110 = false ∨ valuation q 232 = true ∨ valuation q 52 = true ∨ valuation q 112 = true := by
  rw [value52, value110, value112, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (481 : Vertex) w → w ∈ region → w ≠ (489 : Vertex) → w ∈ [(353 : Vertex), (485 : Vertex)] := by decide
  have hg := other_cover q (481 : Vertex) (489 : Vertex) [(353 : Vertex), (485 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 233 = true ∨ valuation q 118 = true := by
  rw [value111, value118, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (482 : Vertex) w → w ∈ region → w ≠ (486 : Vertex) → w ∈ [(498 : Vertex)] := by decide
  have hg := other_cover q (482 : Vertex) (486 : Vertex) [(498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 233 = true ∨ valuation q 113 = true := by
  rw [value111, value113, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (482 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(486 : Vertex)] := by decide
  have hg := other_cover q (482 : Vertex) (498 : Vertex) [(486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 234 = true := by
  rw [value112, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (485 : Vertex) w → w ∈ region → w ≠ (481 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (485 : Vertex) (481 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 55 = false ∨ valuation q 103 = false ∨ valuation q 111 = false := by
  rw [value55, value103, value111, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (358 : Vertex) (454 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 235 = true ∨ valuation q 103 = true ∨ valuation q 111 = true := by
  rw [value103, value111, value113, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (486 : Vertex) w → w ∈ region → w ≠ (358 : Vertex) → w ∈ [(454 : Vertex), (482 : Vertex)] := by decide
  have hg := other_cover q (486 : Vertex) (358 : Vertex) [(454 : Vertex), (482 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 236 = true ∨ valuation q 115 = true ∨ valuation q 116 = true ∨ valuation q 120 = true := by
  rw [value114, value115, value116, value120, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (360 : Vertex) → w ∈ [(489 : Vertex), (492 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (360 : Vertex) [(489 : Vertex), (492 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 236 = true ∨ valuation q 56 = true ∨ valuation q 116 = true ∨ valuation q 120 = true := by
  rw [value56, value114, value116, value120, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (488 : Vertex) w → w ∈ region → w ≠ (489 : Vertex) → w ∈ [(360 : Vertex), (492 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (488 : Vertex) (489 : Vertex) [(360 : Vertex), (492 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 86 = false ∨ valuation q 110 = false ∨ valuation q 114 = false := by
  rw [value86, value110, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (489 : Vertex) (425 : Vertex) (481 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 237 = true ∨ valuation q 86 = true ∨ valuation q 114 = true := by
  rw [value86, value114, value115, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (489 : Vertex) w → w ∈ region → w ≠ (481 : Vertex) → w ∈ [(425 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (489 : Vertex) (481 : Vertex) [(425 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 105 = false ∨ valuation q 114 = false ∨ valuation q 122 = false := by
  rw [value105, value114, value116, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (492 : Vertex) (460 : Vertex) (488 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 91 = false ∨ valuation q 118 = false ∨ valuation q 119 = false := by
  rw [value91, value117, value118, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (496 : Vertex) (432 : Vertex) (498 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E254.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112254
