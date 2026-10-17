import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 226 = true ∨ valuation q 33 = true ∨ valuation q 90 = true ∨ valuation q 93 = true ∨ valuation q 96 = true ∨ valuation q 101 = true ∨ valuation q 126 = true := by
  rw [value33, value90, value93, value96, value99, value101, value126, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (381 : Vertex) w → w ∈ region → w ≠ (317 : Vertex) → w ∈ [(125 : Vertex), (349 : Vertex), (365 : Vertex), (373 : Vertex), (383 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (381 : Vertex) (317 : Vertex) [(125 : Vertex), (349 : Vertex), (365 : Vertex), (373 : Vertex), (383 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 100 = false ∨ valuation q 227 = true ∨ valuation q 34 = true ∨ valuation q 91 = true := by
  rw [value34, value91, value100, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (382 : Vertex) w → w ∈ region → w ≠ (383 : Vertex) → w ∈ [(126 : Vertex), (350 : Vertex)] := by decide
  have hg := other_cover q (382 : Vertex) (383 : Vertex) [(126 : Vertex), (350 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 35 = false ∨ valuation q 77 = false ∨ valuation q 98 = false := by
  rw [value35, value77, value98, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (383 : Vertex) (127 : Vertex) (319 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 77 = false ∨ valuation q 92 = false ∨ valuation q 94 = false := by
  rw [value77, value92, value94, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (383 : Vertex) (319 : Vertex) (351 : Vertex) (367 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 77 = false ∨ valuation q 92 = false ∨ valuation q 97 = false := by
  rw [value77, value92, value97, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (383 : Vertex) (319 : Vertex) (351 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 77 = false ∨ valuation q 94 = false ∨ valuation q 97 = false := by
  rw [value77, value94, value97, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (383 : Vertex) (319 : Vertex) (367 : Vertex) (375 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 77 = false ∨ valuation q 94 = false ∨ valuation q 98 = false := by
  rw [value77, value94, value98, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (383 : Vertex) (319 : Vertex) (367 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 77 = false ∨ valuation q 97 = false ∨ valuation q 98 = false := by
  rw [value77, value97, value98, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (383 : Vertex) (319 : Vertex) (375 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 77 = false ∨ valuation q 98 = false ∨ valuation q 127 = false := by
  rw [value77, value98, value101, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (383 : Vertex) (319 : Vertex) (379 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 94 = false ∨ valuation q 97 = false ∨ valuation q 98 = false := by
  rw [value94, value97, value98, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (383 : Vertex) (367 : Vertex) (375 : Vertex) (379 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 94 = false ∨ valuation q 97 = false ∨ valuation q 99 = false := by
  rw [value94, value97, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (383 : Vertex) (367 : Vertex) (375 : Vertex) (381 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 97 = false ∨ valuation q 98 = false ∨ valuation q 99 = false := by
  rw [value97, value98, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (383 : Vertex) (375 : Vertex) (379 : Vertex) (381 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 101 = false ∨ valuation q 98 = false ∨ valuation q 99 = false ∨ valuation q 127 = false := by
  rw [value98, value99, value101, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (383 : Vertex) (379 : Vertex) (381 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 42 = false ∨ valuation q 79 = false ∨ valuation q 103 = false := by
  rw [value42, value79, value102, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (458 : Vertex) (202 : Vertex) (330 : Vertex) (459 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 102 = false ∨ valuation q 229 = true ∨ valuation q 42 = true ∨ valuation q 103 = true := by
  rw [value42, value102, value103, value229]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (458 : Vertex) w → w ∈ region → w ≠ (330 : Vertex) → w ∈ [(202 : Vertex), (459 : Vertex)] := by decide
  have hg := other_cover q (458 : Vertex) (330 : Vertex) [(202 : Vertex), (459 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 230 = false ∨ valuation q 103 = true := by
  rw [value103, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (459 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 230 = false ∨ valuation q 102 = false ∨ valuation q 112 = false := by
  rw [value102, value112, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (459 : Vertex) (458 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide)

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 230 = true ∨ valuation q 112 = true := by
  rw [value103, value112, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (459 : Vertex) w → w ∈ region → w ≠ (458 : Vertex) → w ∈ [(475 : Vertex)] := by decide
  have hg := other_cover q (459 : Vertex) (458 : Vertex) [(475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 103 = false ∨ valuation q 230 = true ∨ valuation q 102 = true := by
  rw [value102, value103, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (459 : Vertex) w → w ∈ region → w ≠ (475 : Vertex) → w ∈ [(458 : Vertex)] := by decide
  have hg := other_cover q (459 : Vertex) (475 : Vertex) [(458 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 43 = false ∨ valuation q 105 = false ∨ valuation q 113 = false := by
  rw [value43, value104, value105, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (460 : Vertex) (204 : Vertex) (461 : Vertex) (476 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 104 = false ∨ valuation q 231 = true ∨ valuation q 43 = true ∨ valuation q 113 = true := by
  rw [value43, value104, value113, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (460 : Vertex) w → w ∈ region → w ≠ (461 : Vertex) → w ∈ [(204 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (460 : Vertex) (461 : Vertex) [(204 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 232 = true ∨ valuation q 104 = true ∨ valuation q 114 = true := by
  rw [value104, value105, value114, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (461 : Vertex) w → w ∈ region → w ≠ (333 : Vertex) → w ∈ [(460 : Vertex), (477 : Vertex)] := by decide
  have hg := other_cover q (461 : Vertex) (333 : Vertex) [(460 : Vertex), (477 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 105 = false ∨ valuation q 232 = true ∨ valuation q 80 = true ∨ valuation q 114 = true := by
  rw [value80, value105, value114, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (461 : Vertex) w → w ∈ region → w ≠ (460 : Vertex) → w ∈ [(333 : Vertex), (477 : Vertex)] := by decide
  have hg := other_cover q (461 : Vertex) (460 : Vertex) [(333 : Vertex), (477 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 106 = false ∨ valuation q 233 = true ∨ valuation q 107 = true ∨ valuation q 110 = true ∨ valuation q 117 = true := by
  rw [value106, value107, value110, value117, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (464 : Vertex) w → w ∈ region → w ≠ (336 : Vertex) → w ∈ [(465 : Vertex), (472 : Vertex), (496 : Vertex)] := by decide
  have hg := other_cover q (464 : Vertex) (336 : Vertex) [(465 : Vertex), (472 : Vertex), (496 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 83 = false ∨ valuation q 108 = false ∨ valuation q 109 = false := by
  rw [value83, value107, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (465 : Vertex) (337 : Vertex) (467 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 83 = false ∨ valuation q 108 = false ∨ valuation q 111 = false := by
  rw [value83, value107, value108, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (465 : Vertex) (337 : Vertex) (467 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 83 = false ∨ valuation q 109 = false ∨ valuation q 111 = false := by
  rw [value83, value107, value109, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (465 : Vertex) (337 : Vertex) (469 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 106 = false ∨ valuation q 108 = false ∨ valuation q 109 = false := by
  rw [value106, value107, value108, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (465 : Vertex) (464 : Vertex) (467 : Vertex) (469 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 108 = false ∨ valuation q 109 = false ∨ valuation q 111 = false := by
  rw [value107, value108, value109, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (465 : Vertex) (467 : Vertex) (469 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 107 = false ∨ valuation q 234 = true ∨ valuation q 106 = true ∨ valuation q 108 = true ∨ valuation q 109 = true ∨ valuation q 111 = true := by
  rw [value106, value107, value108, value109, value111, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (465 : Vertex) w → w ∈ region → w ≠ (337 : Vertex) → w ∈ [(464 : Vertex), (467 : Vertex), (469 : Vertex), (473 : Vertex)] := by decide
  have hg := other_cover q (465 : Vertex) (337 : Vertex) [(464 : Vertex), (467 : Vertex), (469 : Vertex), (473 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 235 = true ∨ valuation q 107 = true ∨ valuation q 112 = true ∨ valuation q 119 = true := by
  rw [value107, value108, value112, value119, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (467 : Vertex) w → w ∈ region → w ≠ (211 : Vertex) → w ∈ [(465 : Vertex), (475 : Vertex), (499 : Vertex)] := by decide
  have hg := other_cover q (467 : Vertex) (211 : Vertex) [(465 : Vertex), (475 : Vertex), (499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 108 = false ∨ valuation q 235 = true ∨ valuation q 46 = true ∨ valuation q 112 = true ∨ valuation q 119 = true := by
  rw [value46, value108, value112, value119, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (467 : Vertex) w → w ∈ region → w ≠ (465 : Vertex) → w ∈ [(211 : Vertex), (475 : Vertex), (499 : Vertex)] := by decide
  have hg := other_cover q (467 : Vertex) (465 : Vertex) [(211 : Vertex), (475 : Vertex), (499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block20 (q : Snake 81) (h : Conditions q) : B112E256.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112256
