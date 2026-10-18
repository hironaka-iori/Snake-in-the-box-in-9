import E112110Semantics
import B112E110Inputs
namespace Snake9.Regrowth.E112110
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 109 = false ∨ valuation q 112 = false ∨ valuation q 113 = false := by
  rw [value108, value109, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (465 : Vertex) (468 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 110 = false ∨ valuation q 112 = false ∨ valuation q 113 = false := by
  rw [value108, value110, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (464 : Vertex) (466 : Vertex) (468 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 227 = true ∨ valuation q 108 = true ∨ valuation q 111 = true := by
  rw [value108, value109, value111, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (465 : Vertex) w → w ∈ region → w ≠ (449 : Vertex) → w ∈ [(464 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (465 : Vertex) (449 : Vertex) [(464 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 227 = true ∨ valuation q 97 = true ∨ valuation q 111 = true := by
  rw [value97, value109, value111, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (465 : Vertex) w → w ∈ region → w ≠ (464 : Vertex) → w ∈ [(449 : Vertex), (467 : Vertex)] := by decide
  have hg := other_cover q (465 : Vertex) (464 : Vertex) [(449 : Vertex), (467 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 109 = false ∨ valuation q 227 = true ∨ valuation q 97 = true ∨ valuation q 108 = true := by
  rw [value97, value108, value109, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (465 : Vertex) w → w ∈ region → w ≠ (467 : Vertex) → w ∈ [(449 : Vertex), (464 : Vertex)] := by decide
  have hg := other_cover q (465 : Vertex) (467 : Vertex) [(449 : Vertex), (464 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 99 = false ∨ valuation q 109 = false ∨ valuation q 110 = false := by
  rw [value99, value109, value110, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (467 : Vertex) (451 : Vertex) (465 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 99 = false ∨ valuation q 109 = false ∨ valuation q 115 = false := by
  rw [value99, value109, value111, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (467 : Vertex) (451 : Vertex) (465 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 99 = false ∨ valuation q 110 = false ∨ valuation q 115 = false := by
  rw [value99, value110, value111, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (467 : Vertex) (451 : Vertex) (466 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 109 = false ∨ valuation q 110 = false ∨ valuation q 115 = false := by
  rw [value109, value110, value111, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (467 : Vertex) (465 : Vertex) (466 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 229 = true ∨ valuation q 99 = true ∨ valuation q 110 = true ∨ valuation q 115 = true := by
  rw [value99, value110, value111, value115, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (467 : Vertex) w → w ∈ region → w ≠ (465 : Vertex) → w ∈ [(451 : Vertex), (466 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (467 : Vertex) (465 : Vertex) [(451 : Vertex), (466 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 230 = true ∨ valuation q 108 = true ∨ valuation q 116 = true := by
  rw [value108, value112, value116, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (468 : Vertex) w → w ∈ region → w ≠ (212 : Vertex) → w ∈ [(464 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (468 : Vertex) (212 : Vertex) [(464 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 230 = true ∨ valuation q 44 = true ∨ valuation q 116 = true := by
  rw [value44, value112, value116, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (468 : Vertex) w → w ∈ region → w ≠ (464 : Vertex) → w ∈ [(212 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (468 : Vertex) (464 : Vertex) [(212 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 230 = true ∨ valuation q 44 = true ∨ valuation q 108 = true := by
  rw [value44, value108, value112, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (468 : Vertex) w → w ∈ region → w ≠ (476 : Vertex) → w ∈ [(212 : Vertex), (464 : Vertex)] := by decide
  have hg := other_cover q (468 : Vertex) (476 : Vertex) [(212 : Vertex), (464 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 91 = false ∨ valuation q 108 = false ∨ valuation q 114 = false := by
  rw [value91, value108, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (472 : Vertex) (408 : Vertex) (464 : Vertex) (474 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 231 = true ∨ valuation q 71 = true ∨ valuation q 102 = true ∨ valuation q 108 = true ∨ valuation q 114 = true ∨ valuation q 116 = true := by
  rw [value71, value102, value108, value113, value114, value116, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (408 : Vertex) → w ∈ [(344 : Vertex), (456 : Vertex), (464 : Vertex), (474 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (408 : Vertex) [(344 : Vertex), (456 : Vertex), (464 : Vertex), (474 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 231 = true ∨ valuation q 71 = true ∨ valuation q 91 = true ∨ valuation q 108 = true ∨ valuation q 114 = true ∨ valuation q 116 = true := by
  rw [value71, value91, value108, value113, value114, value116, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (456 : Vertex) → w ∈ [(344 : Vertex), (408 : Vertex), (464 : Vertex), (474 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (456 : Vertex) [(344 : Vertex), (408 : Vertex), (464 : Vertex), (474 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 231 = true ∨ valuation q 71 = true ∨ valuation q 91 = true ∨ valuation q 102 = true ∨ valuation q 108 = true ∨ valuation q 114 = true := by
  rw [value71, value91, value102, value108, value113, value114, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (476 : Vertex) → w ∈ [(344 : Vertex), (408 : Vertex), (456 : Vertex), (464 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (476 : Vertex) [(344 : Vertex), (408 : Vertex), (456 : Vertex), (464 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 49 = false ∨ valuation q 73 = false ∨ valuation q 110 = false := by
  rw [value49, value73, value110, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (346 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 49 = false ∨ valuation q 73 = false ∨ valuation q 113 = false := by
  rw [value49, value73, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (346 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 49 = false ∨ valuation q 73 = false ∨ valuation q 115 = false := by
  rw [value49, value73, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (346 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 49 = false ∨ valuation q 73 = false ∨ valuation q 117 = false := by
  rw [value49, value73, value114, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (346 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 49 = false ∨ valuation q 110 = false ∨ valuation q 113 = false := by
  rw [value49, value110, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (466 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 49 = false ∨ valuation q 110 = false ∨ valuation q 115 = false := by
  rw [value49, value110, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (466 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 49 = false ∨ valuation q 110 = false ∨ valuation q 117 = false := by
  rw [value49, value110, value114, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (466 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 49 = false ∨ valuation q 113 = false ∨ valuation q 115 = false := by
  rw [value49, value113, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (472 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 49 = false ∨ valuation q 113 = false ∨ valuation q 117 = false := by
  rw [value49, value113, value114, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (472 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 49 = false ∨ valuation q 115 = false ∨ valuation q 117 = false := by
  rw [value49, value114, value115, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (218 : Vertex) (475 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 73 = false ∨ valuation q 110 = false ∨ valuation q 113 = false := by
  rw [value73, value110, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (346 : Vertex) (466 : Vertex) (472 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 73 = false ∨ valuation q 110 = false ∨ valuation q 115 = false := by
  rw [value73, value110, value114, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (346 : Vertex) (466 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 73 = false ∨ valuation q 110 = false ∨ valuation q 117 = false := by
  rw [value73, value110, value114, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (346 : Vertex) (466 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 73 = false ∨ valuation q 113 = false ∨ valuation q 117 = false := by
  rw [value73, value113, value114, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (346 : Vertex) (472 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 73 = false ∨ valuation q 115 = false ∨ valuation q 117 = false := by
  rw [value73, value114, value115, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (346 : Vertex) (475 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E110.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112110
