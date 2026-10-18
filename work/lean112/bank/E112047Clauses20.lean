import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 41 = false ∨ valuation q 72 = false ∨ valuation q 112 = false := by
  rw [value41, value72, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (466 : Vertex) (210 : Vertex) (338 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 41 = false ∨ valuation q 100 = false ∨ valuation q 109 = false := by
  rw [value41, value100, value109, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (466 : Vertex) (210 : Vertex) (450 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 41 = false ∨ valuation q 100 = false ∨ valuation q 112 = false := by
  rw [value41, value100, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (466 : Vertex) (210 : Vertex) (450 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 41 = false ∨ valuation q 100 = false ∨ valuation q 114 = false := by
  rw [value41, value100, value111, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (466 : Vertex) (210 : Vertex) (450 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 72 = false ∨ valuation q 100 = false ∨ valuation q 109 = false := by
  rw [value72, value100, value109, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (466 : Vertex) (338 : Vertex) (450 : Vertex) (464 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 72 = false ∨ valuation q 100 = false ∨ valuation q 112 = false := by
  rw [value72, value100, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (466 : Vertex) (338 : Vertex) (450 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 72 = false ∨ valuation q 100 = false ∨ valuation q 114 = false := by
  rw [value72, value100, value111, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (466 : Vertex) (338 : Vertex) (450 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 72 = false ∨ valuation q 109 = false ∨ valuation q 112 = false := by
  rw [value72, value109, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (466 : Vertex) (338 : Vertex) (464 : Vertex) (467 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 72 = false ∨ valuation q 109 = false ∨ valuation q 114 = false := by
  rw [value72, value109, value111, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (466 : Vertex) (338 : Vertex) (464 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 111 = false ∨ valuation q 72 = false ∨ valuation q 112 = false ∨ valuation q 114 = false := by
  rw [value72, value111, value112, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (466 : Vertex) (338 : Vertex) (467 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 91 = false ∨ valuation q 101 = false ∨ valuation q 110 = false := by
  rw [value91, value101, value110, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (467 : Vertex) (403 : Vertex) (451 : Vertex) (465 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 91 = false ∨ valuation q 101 = false ∨ valuation q 111 = false := by
  rw [value91, value101, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (467 : Vertex) (403 : Vertex) (451 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 91 = false ∨ valuation q 110 = false ∨ valuation q 111 = false := by
  rw [value91, value110, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (467 : Vertex) (403 : Vertex) (465 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 101 = false ∨ valuation q 110 = false ∨ valuation q 111 = false := by
  rw [value101, value110, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (467 : Vertex) (451 : Vertex) (465 : Vertex) (466 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 230 = true ∨ valuation q 91 = true ∨ valuation q 110 = true ∨ valuation q 111 = true := by
  rw [value91, value110, value111, value112, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (467 : Vertex) w → w ∈ region → w ≠ (451 : Vertex) → w ∈ [(403 : Vertex), (465 : Vertex), (466 : Vertex)] := by decide
  have hg := other_cover q (467 : Vertex) (451 : Vertex) [(403 : Vertex), (465 : Vertex), (466 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 230 = true ∨ valuation q 91 = true ∨ valuation q 101 = true ∨ valuation q 111 = true := by
  rw [value91, value101, value111, value112, value230]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (467 : Vertex) w → w ∈ region → w ≠ (465 : Vertex) → w ∈ [(403 : Vertex), (451 : Vertex), (466 : Vertex)] := by decide
  have hg := other_cover q (467 : Vertex) (465 : Vertex) [(403 : Vertex), (451 : Vertex), (466 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 102 = false ∨ valuation q 109 = false ∨ valuation q 114 = false := by
  rw [value102, value109, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (468 : Vertex) (452 : Vertex) (464 : Vertex) (470 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 231 = true ∨ valuation q 109 = true ∨ valuation q 114 = true ∨ valuation q 116 = true := by
  rw [value109, value113, value114, value116, value231]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (468 : Vertex) w → w ∈ region → w ≠ (452 : Vertex) → w ∈ [(464 : Vertex), (470 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (468 : Vertex) (452 : Vertex) [(464 : Vertex), (470 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 43 = false ∨ valuation q 113 = false ∨ valuation q 117 = false := by
  rw [value43, value113, value114, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (214 : Vertex) (468 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 93 = false ∨ valuation q 111 = false ∨ valuation q 113 = false := by
  rw [value93, value111, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (406 : Vertex) (466 : Vertex) (468 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 93 = false ∨ valuation q 111 = false ∨ valuation q 117 = false := by
  rw [value93, value111, value114, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (406 : Vertex) (466 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 93 = false ∨ valuation q 113 = false ∨ valuation q 117 = false := by
  rw [value93, value113, value114, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (406 : Vertex) (468 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 111 = false ∨ valuation q 113 = false ∨ valuation q 117 = false := by
  rw [value111, value113, value114, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (470 : Vertex) (466 : Vertex) (468 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 45 = true ∨ valuation q 95 = true ∨ valuation q 109 = true ∨ valuation q 116 = true := by
  rw [value45, value95, value109, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ∈ [(216 : Vertex), (408 : Vertex), (464 : Vertex), (476 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (472 : Vertex) [(216 : Vertex), (408 : Vertex), (464 : Vertex), (476 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 233 = true ∨ valuation q 95 = true ∨ valuation q 109 = true ∨ valuation q 116 = true := by
  rw [value95, value109, value115, value116, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (216 : Vertex) → w ∈ [(408 : Vertex), (464 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (216 : Vertex) [(408 : Vertex), (464 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 233 = true ∨ valuation q 45 = true ∨ valuation q 95 = true ∨ valuation q 116 = true := by
  rw [value45, value95, value115, value116, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (472 : Vertex) w → w ∈ region → w ≠ (464 : Vertex) → w ∈ [(216 : Vertex), (408 : Vertex), (476 : Vertex)] := by decide
  have hg := other_cover q (472 : Vertex) (464 : Vertex) [(216 : Vertex), (408 : Vertex), (476 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 113 = false ∨ valuation q 115 = false ∨ valuation q 117 = false := by
  rw [value113, value115, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (476 : Vertex) (468 : Vertex) (472 : Vertex) (478 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 234 = true ∨ valuation q 113 = true ∨ valuation q 115 = true := by
  rw [value113, value115, value116, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (476 : Vertex) w → w ∈ region → w ≠ (478 : Vertex) → w ∈ [(468 : Vertex), (472 : Vertex)] := by decide
  have hg := other_cover q (476 : Vertex) (478 : Vertex) [(468 : Vertex), (472 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 117 = true := by
  rw [value117, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (478 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 114 = true ∨ valuation q 116 = true ∨ valuation q 118 = true := by
  rw [value114, value116, value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (478 : Vertex) w → w ∈ region → w ∈ [(470 : Vertex), (476 : Vertex), (479 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (478 : Vertex) [(470 : Vertex), (476 : Vertex), (479 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 235 = false ∨ valuation q 114 = false ∨ valuation q 118 = false := by
  rw [value114, value118, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (478 : Vertex) (470 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide)

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 235 = true ∨ valuation q 116 = true ∨ valuation q 118 = true := by
  rw [value116, value117, value118, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (478 : Vertex) w → w ∈ region → w ≠ (470 : Vertex) → w ∈ [(476 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (478 : Vertex) (470 : Vertex) [(476 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block20 (q : Snake 81) (h : Conditions q) : B112E047.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112047
