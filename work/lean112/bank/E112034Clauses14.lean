import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 87 = false ∨ valuation q 94 = false ∨ valuation q 114 = false := by
  rw [value87, value92, value94, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (425 : Vertex) (417 : Vertex) (429 : Vertex) (489 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 220 = true ∨ valuation q 87 = true ∨ valuation q 94 = true ∨ valuation q 114 = true := by
  rw [value87, value92, value94, value114, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (425 : Vertex) w → w ∈ region → w ≠ (169 : Vertex) → w ∈ [(417 : Vertex), (429 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (425 : Vertex) (169 : Vertex) [(417 : Vertex), (429 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 220 = true ∨ valuation q 20 = true ∨ valuation q 94 = true ∨ valuation q 114 = true := by
  rw [value20, value92, value94, value114, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (425 : Vertex) w → w ∈ region → w ≠ (417 : Vertex) → w ∈ [(169 : Vertex), (429 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (425 : Vertex) (417 : Vertex) [(169 : Vertex), (429 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 220 = true ∨ valuation q 20 = true ∨ valuation q 87 = true ∨ valuation q 114 = true := by
  rw [value20, value87, value92, value114, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (425 : Vertex) w → w ∈ region → w ≠ (429 : Vertex) → w ∈ [(169 : Vertex), (417 : Vertex), (489 : Vertex)] := by decide
  have hg := other_cover q (425 : Vertex) (429 : Vertex) [(169 : Vertex), (417 : Vertex), (489 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 92 = false ∨ valuation q 220 = true ∨ valuation q 20 = true ∨ valuation q 87 = true ∨ valuation q 94 = true := by
  rw [value20, value87, value92, value94, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (425 : Vertex) w → w ∈ region → w ≠ (489 : Vertex) → w ∈ [(169 : Vertex), (417 : Vertex), (429 : Vertex)] := by decide
  have hg := other_cover q (425 : Vertex) (489 : Vertex) [(169 : Vertex), (417 : Vertex), (429 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 57 = false ∨ valuation q 88 = false ∨ valuation q 101 = false := by
  rw [value57, value88, value93, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (426 : Vertex) (298 : Vertex) (418 : Vertex) (442 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 57 = false ∨ valuation q 101 = false ∨ valuation q 115 = false := by
  rw [value57, value93, value101, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (426 : Vertex) (298 : Vertex) (442 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 88 = false ∨ valuation q 101 = false ∨ valuation q 115 = false := by
  rw [value88, value93, value101, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (426 : Vertex) (418 : Vertex) (442 : Vertex) (490 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 221 = true ∨ valuation q 88 = true ∨ valuation q 101 = true ∨ valuation q 115 = true := by
  rw [value88, value93, value101, value115, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (426 : Vertex) w → w ∈ region → w ≠ (298 : Vertex) → w ∈ [(418 : Vertex), (442 : Vertex), (490 : Vertex)] := by decide
  have hg := other_cover q (426 : Vertex) (298 : Vertex) [(418 : Vertex), (442 : Vertex), (490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 221 = true ∨ valuation q 57 = true ∨ valuation q 101 = true ∨ valuation q 115 = true := by
  rw [value57, value93, value101, value115, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (426 : Vertex) w → w ∈ region → w ≠ (418 : Vertex) → w ∈ [(298 : Vertex), (442 : Vertex), (490 : Vertex)] := by decide
  have hg := other_cover q (426 : Vertex) (418 : Vertex) [(298 : Vertex), (442 : Vertex), (490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 221 = true ∨ valuation q 57 = true ∨ valuation q 88 = true ∨ valuation q 115 = true := by
  rw [value57, value88, value93, value115, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (426 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(298 : Vertex), (418 : Vertex), (490 : Vertex)] := by decide
  have hg := other_cover q (426 : Vertex) (442 : Vertex) [(298 : Vertex), (418 : Vertex), (490 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 93 = false ∨ valuation q 221 = true ∨ valuation q 57 = true ∨ valuation q 88 = true ∨ valuation q 101 = true := by
  rw [value57, value88, value93, value101, value221]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (426 : Vertex) w → w ∈ region → w ≠ (490 : Vertex) → w ∈ [(298 : Vertex), (418 : Vertex), (442 : Vertex)] := by decide
  have hg := other_cover q (426 : Vertex) (490 : Vertex) [(298 : Vertex), (418 : Vertex), (442 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 92 = false ∨ valuation q 95 = false ∨ valuation q 103 = false := by
  rw [value92, value94, value95, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (429 : Vertex) (425 : Vertex) (431 : Vertex) (445 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 92 = false ∨ valuation q 95 = false ∨ valuation q 117 = false := by
  rw [value92, value94, value95, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (429 : Vertex) (425 : Vertex) (431 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 92 = false ∨ valuation q 103 = false ∨ valuation q 117 = false := by
  rw [value92, value94, value103, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (429 : Vertex) (425 : Vertex) (445 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 95 = false ∨ valuation q 103 = false ∨ valuation q 117 = false := by
  rw [value94, value95, value103, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (429 : Vertex) (431 : Vertex) (445 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 222 = true ∨ valuation q 95 = true ∨ valuation q 103 = true ∨ valuation q 117 = true := by
  rw [value94, value95, value103, value117, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (429 : Vertex) w → w ∈ region → w ≠ (425 : Vertex) → w ∈ [(431 : Vertex), (445 : Vertex), (493 : Vertex)] := by decide
  have hg := other_cover q (429 : Vertex) (425 : Vertex) [(431 : Vertex), (445 : Vertex), (493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 94 = false ∨ valuation q 222 = true ∨ valuation q 92 = true ∨ valuation q 103 = true ∨ valuation q 117 = true := by
  rw [value92, value94, value103, value117, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (429 : Vertex) w → w ∈ region → w ≠ (431 : Vertex) → w ∈ [(425 : Vertex), (445 : Vertex), (493 : Vertex)] := by decide
  have hg := other_cover q (429 : Vertex) (431 : Vertex) [(425 : Vertex), (445 : Vertex), (493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 91 = false ∨ valuation q 94 = false ∨ valuation q 105 = false := by
  rw [value91, value94, value95, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (431 : Vertex) (423 : Vertex) (429 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 223 = true ∨ valuation q 94 = true ∨ valuation q 105 = true := by
  rw [value94, value95, value105, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (431 : Vertex) w → w ∈ region → w ≠ (423 : Vertex) → w ∈ [(429 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (431 : Vertex) (423 : Vertex) [(429 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 223 = true ∨ valuation q 91 = true ∨ valuation q 105 = true := by
  rw [value91, value95, value105, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (431 : Vertex) w → w ∈ region → w ≠ (429 : Vertex) → w ∈ [(423 : Vertex), (447 : Vertex)] := by decide
  have hg := other_cover q (431 : Vertex) (429 : Vertex) [(423 : Vertex), (447 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 223 = true ∨ valuation q 91 = true ∨ valuation q 94 = true := by
  rw [value91, value94, value95, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (431 : Vertex) w → w ∈ region → w ≠ (447 : Vertex) → w ∈ [(423 : Vertex), (429 : Vertex)] := by decide
  have hg := other_cover q (431 : Vertex) (447 : Vertex) [(423 : Vertex), (429 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 86 = false ∨ valuation q 97 = false ∨ valuation q 98 = false := by
  rw [value86, value96, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (432 : Vertex) (416 : Vertex) (433 : Vertex) (434 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 86 = false ∨ valuation q 97 = false ∨ valuation q 100 = false := by
  rw [value86, value96, value97, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (432 : Vertex) (416 : Vertex) (433 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 86 = false ∨ valuation q 98 = false ∨ valuation q 100 = false := by
  rw [value86, value96, value98, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (432 : Vertex) (416 : Vertex) (434 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 97 = false ∨ valuation q 98 = false ∨ valuation q 100 = false := by
  rw [value96, value97, value98, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (432 : Vertex) (433 : Vertex) (434 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 224 = true ∨ valuation q 86 = true ∨ valuation q 97 = true ∨ valuation q 98 = true := by
  rw [value86, value96, value97, value98, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (432 : Vertex) w → w ∈ region → w ≠ (436 : Vertex) → w ∈ [(416 : Vertex), (433 : Vertex), (434 : Vertex)] := by decide
  have hg := other_cover q (432 : Vertex) (436 : Vertex) [(416 : Vertex), (433 : Vertex), (434 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 87 = false ∨ valuation q 99 = false ∨ valuation q 119 = false := by
  rw [value87, value97, value99, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (417 : Vertex) (435 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 96 = false ∨ valuation q 99 = false ∨ valuation q 119 = false := by
  rw [value96, value97, value99, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (433 : Vertex) (432 : Vertex) (435 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 225 = true ∨ valuation q 96 = true ∨ valuation q 99 = true ∨ valuation q 119 = true := by
  rw [value96, value97, value99, value119, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (433 : Vertex) w → w ∈ region → w ≠ (417 : Vertex) → w ∈ [(432 : Vertex), (435 : Vertex), (497 : Vertex)] := by decide
  have hg := other_cover q (433 : Vertex) (417 : Vertex) [(432 : Vertex), (435 : Vertex), (497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 225 = true ∨ valuation q 87 = true ∨ valuation q 99 = true ∨ valuation q 119 = true := by
  rw [value87, value97, value99, value119, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (433 : Vertex) w → w ∈ region → w ≠ (432 : Vertex) → w ∈ [(417 : Vertex), (435 : Vertex), (497 : Vertex)] := by decide
  have hg := other_cover q (433 : Vertex) (432 : Vertex) [(417 : Vertex), (435 : Vertex), (497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 225 = true ∨ valuation q 87 = true ∨ valuation q 96 = true ∨ valuation q 119 = true := by
  rw [value87, value96, value97, value119, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (433 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(417 : Vertex), (432 : Vertex), (497 : Vertex)] := by decide
  have hg := other_cover q (433 : Vertex) (435 : Vertex) [(417 : Vertex), (432 : Vertex), (497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block14 (q : Snake 81) (h : Conditions q) : B112E034.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112034
