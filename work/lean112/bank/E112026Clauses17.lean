import E112026Semantics
import B112E026Inputs
namespace Snake9.Regrowth.E112026
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 222 = true ∨ valuation q 89 = true ∨ valuation q 99 = true ∨ valuation q 102 = true := by
  rw [value89, value99, value101, value102, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (442 : Vertex) w → w ∈ region → w ≠ (506 : Vertex) → w ∈ [(426 : Vertex), (440 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (442 : Vertex) (506 : Vertex) [(426 : Vertex), (440 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 90 = false ∨ valuation q 95 = false ∨ valuation q 100 = false := by
  rw [value90, value95, value100, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (427 : Vertex) (435 : Vertex) (441 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 90 = false ∨ valuation q 95 = false ∨ valuation q 101 = false := by
  rw [value90, value95, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (427 : Vertex) (435 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 90 = false ∨ valuation q 100 = false ∨ valuation q 101 = false := by
  rw [value90, value100, value101, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (427 : Vertex) (441 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 90 = false ∨ valuation q 100 = false ∨ valuation q 103 = false := by
  rw [value90, value100, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (427 : Vertex) (441 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 95 = false ∨ valuation q 100 = false ∨ valuation q 103 = false := by
  rw [value95, value100, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (435 : Vertex) (441 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 223 = true ∨ valuation q 95 = true ∨ valuation q 100 = true ∨ valuation q 101 = true ∨ valuation q 103 = true := by
  rw [value95, value100, value101, value102, value103, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(435 : Vertex), (441 : Vertex), (442 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (427 : Vertex) [(435 : Vertex), (441 : Vertex), (442 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 223 = true ∨ valuation q 90 = true ∨ valuation q 100 = true ∨ valuation q 101 = true ∨ valuation q 103 = true := by
  rw [value90, value100, value101, value102, value103, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(427 : Vertex), (441 : Vertex), (442 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (435 : Vertex) [(427 : Vertex), (441 : Vertex), (442 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 223 = true ∨ valuation q 90 = true ∨ valuation q 95 = true ∨ valuation q 101 = true ∨ valuation q 103 = true := by
  rw [value90, value95, value101, value102, value103, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (441 : Vertex) → w ∈ [(427 : Vertex), (435 : Vertex), (442 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (441 : Vertex) [(427 : Vertex), (435 : Vertex), (442 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 223 = true ∨ valuation q 90 = true ∨ valuation q 95 = true ∨ valuation q 100 = true ∨ valuation q 103 = true := by
  rw [value90, value95, value100, value102, value103, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(427 : Vertex), (435 : Vertex), (441 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (442 : Vertex) [(427 : Vertex), (435 : Vertex), (441 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 223 = true ∨ valuation q 90 = true ∨ valuation q 95 = true ∨ valuation q 100 = true ∨ valuation q 101 = true := by
  rw [value90, value95, value100, value101, value102, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (447 : Vertex) → w ∈ [(427 : Vertex), (435 : Vertex), (441 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (447 : Vertex) [(427 : Vertex), (435 : Vertex), (441 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 31 = false ∨ valuation q 93 = false ∨ valuation q 98 = false := by
  rw [value31, value93, value98, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (447 : Vertex) (191 : Vertex) (431 : Vertex) (439 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 31 = false ∨ valuation q 93 = false ∨ valuation q 102 = false := by
  rw [value31, value93, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (447 : Vertex) (191 : Vertex) (431 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 31 = false ∨ valuation q 98 = false ∨ valuation q 102 = false := by
  rw [value31, value98, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (447 : Vertex) (191 : Vertex) (439 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 93 = false ∨ valuation q 98 = false ∨ valuation q 102 = false := by
  rw [value93, value98, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (447 : Vertex) (431 : Vertex) (439 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 224 = true ∨ valuation q 31 = true ∨ valuation q 93 = true ∨ valuation q 102 = true := by
  rw [value31, value93, value102, value103, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (447 : Vertex) w → w ∈ region → w ≠ (439 : Vertex) → w ∈ [(191 : Vertex), (431 : Vertex), (443 : Vertex)] := by decide
  have hg := other_cover q (447 : Vertex) (439 : Vertex) [(191 : Vertex), (431 : Vertex), (443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 224 = true ∨ valuation q 31 = true ∨ valuation q 93 = true ∨ valuation q 98 = true := by
  rw [value31, value93, value98, value103, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (447 : Vertex) w → w ∈ region → w ≠ (443 : Vertex) → w ∈ [(191 : Vertex), (431 : Vertex), (439 : Vertex)] := by decide
  have hg := other_cover q (447 : Vertex) (443 : Vertex) [(191 : Vertex), (431 : Vertex), (439 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 81 = true ∨ valuation q 105 = true ∨ valuation q 108 = true := by
  rw [value81, value104, value105, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (480 : Vertex) w → w ∈ region → w ∈ [(416 : Vertex), (481 : Vertex), (488 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (480 : Vertex) [(416 : Vertex), (481 : Vertex), (488 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 81 = false ∨ valuation q 105 = false ∨ valuation q 108 = false := by
  rw [value81, value104, value105, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (480 : Vertex) (416 : Vertex) (481 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 225 = false ∨ valuation q 105 = false ∨ valuation q 108 = false := by
  rw [value105, value108, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (480 : Vertex) (481 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide)

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 225 = true ∨ valuation q 81 = true ∨ valuation q 108 = true := by
  rw [value81, value104, value108, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (480 : Vertex) w → w ∈ region → w ≠ (481 : Vertex) → w ∈ [(416 : Vertex), (488 : Vertex)] := by decide
  have hg := other_cover q (480 : Vertex) (481 : Vertex) [(416 : Vertex), (488 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 225 = true ∨ valuation q 81 = true ∨ valuation q 105 = true := by
  rw [value81, value104, value105, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (480 : Vertex) w → w ∈ region → w ≠ (488 : Vertex) → w ∈ [(416 : Vertex), (481 : Vertex)] := by decide
  have hg := other_cover q (480 : Vertex) (488 : Vertex) [(416 : Vertex), (481 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 82 = false ∨ valuation q 104 = false ∨ valuation q 113 = false := by
  rw [value82, value104, value105, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (481 : Vertex) (417 : Vertex) (480 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 82 = false ∨ valuation q 109 = false ∨ valuation q 113 = false := by
  rw [value82, value105, value109, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (481 : Vertex) (417 : Vertex) (489 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 226 = true ∨ valuation q 82 = true ∨ valuation q 109 = true ∨ valuation q 113 = true := by
  rw [value82, value105, value109, value113, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (481 : Vertex) w → w ∈ region → w ≠ (480 : Vertex) → w ∈ [(417 : Vertex), (489 : Vertex), (497 : Vertex)] := by decide
  have hg := other_cover q (481 : Vertex) (480 : Vertex) [(417 : Vertex), (489 : Vertex), (497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 226 = true ∨ valuation q 82 = true ∨ valuation q 104 = true ∨ valuation q 113 = true := by
  rw [value82, value104, value105, value113, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (481 : Vertex) w → w ∈ region → w ≠ (489 : Vertex) → w ∈ [(417 : Vertex), (480 : Vertex), (497 : Vertex)] := by decide
  have hg := other_cover q (481 : Vertex) (489 : Vertex) [(417 : Vertex), (480 : Vertex), (497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 226 = true ∨ valuation q 82 = true ∨ valuation q 104 = true ∨ valuation q 109 = true := by
  rw [value82, value104, value105, value109, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (481 : Vertex) w → w ∈ region → w ≠ (497 : Vertex) → w ∈ [(417 : Vertex), (480 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (481 : Vertex) (497 : Vertex) [(417 : Vertex), (480 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 36 = false ∨ valuation q 86 = false ∨ valuation q 107 = false := by
  rw [value36, value86, value106, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (230 : Vertex) (422 : Vertex) (487 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 36 = false ∨ valuation q 86 = false ∨ valuation q 117 = false := by
  rw [value36, value86, value106, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (230 : Vertex) (422 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 36 = false ∨ valuation q 107 = false ∨ valuation q 117 = false := by
  rw [value36, value106, value107, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (230 : Vertex) (487 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 86 = false ∨ valuation q 107 = false ∨ valuation q 117 = false := by
  rw [value86, value106, value107, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (486 : Vertex) (422 : Vertex) (487 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 227 = true ∨ valuation q 36 = true ∨ valuation q 86 = true ∨ valuation q 107 = true := by
  rw [value36, value86, value106, value107, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (486 : Vertex) w → w ∈ region → w ≠ (502 : Vertex) → w ∈ [(230 : Vertex), (422 : Vertex), (487 : Vertex)] := by decide
  have hg := other_cover q (486 : Vertex) (502 : Vertex) [(230 : Vertex), (422 : Vertex), (487 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block17 (q : Snake 81) (h : Conditions q) : B112E026.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112026
