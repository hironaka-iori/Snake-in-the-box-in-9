import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 244 = true ∨ valuation q 110 = true ∨ valuation q 120 = true ∨ valuation q 123 = true := by
  rw [value110, value120, value121, value123, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (507 : Vertex) w → w ∈ region → w ≠ (505 : Vertex) → w ∈ [(491 : Vertex), (506 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (507 : Vertex) (505 : Vertex) [(491 : Vertex), (506 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 244 = true ∨ valuation q 110 = true ∨ valuation q 119 = true ∨ valuation q 123 = true := by
  rw [value110, value119, value121, value123, value244]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (507 : Vertex) w → w ∈ region → w ≠ (506 : Vertex) → w ∈ [(491 : Vertex), (505 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (507 : Vertex) (506 : Vertex) [(491 : Vertex), (505 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 45 = false ∨ valuation q 80 = false ∨ valuation q 98 = false := by
  rw [value45, value80, value98, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (253 : Vertex) (381 : Vertex) (445 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 45 = false ∨ valuation q 80 = false ∨ valuation q 116 = false := by
  rw [value45, value80, value116, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (253 : Vertex) (381 : Vertex) (501 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 45 = false ∨ valuation q 80 = false ∨ valuation q 119 = false := by
  rw [value45, value80, value119, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (253 : Vertex) (381 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 45 = false ∨ valuation q 80 = false ∨ valuation q 123 = false := by
  rw [value45, value80, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (253 : Vertex) (381 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 45 = false ∨ valuation q 98 = false ∨ valuation q 123 = false := by
  rw [value45, value98, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (253 : Vertex) (445 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 80 = false ∨ valuation q 98 = false ∨ valuation q 116 = false := by
  rw [value80, value98, value116, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (381 : Vertex) (445 : Vertex) (501 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 80 = false ∨ valuation q 98 = false ∨ valuation q 119 = false := by
  rw [value80, value98, value119, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (381 : Vertex) (445 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 80 = false ∨ valuation q 116 = false ∨ valuation q 123 = false := by
  rw [value80, value116, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (381 : Vertex) (501 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 80 = false ∨ valuation q 119 = false ∨ valuation q 123 = false := by
  rw [value80, value119, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (381 : Vertex) (505 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 98 = false ∨ valuation q 116 = false ∨ valuation q 119 = false := by
  rw [value98, value116, value119, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (445 : Vertex) (501 : Vertex) (505 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 46 = false ∨ valuation q 81 = false ∨ valuation q 100 = false := by
  rw [value46, value81, value100, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (255 : Vertex) (383 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 46 = false ∨ valuation q 81 = false ∨ valuation q 113 = false := by
  rw [value46, value81, value113, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (255 : Vertex) (383 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 46 = false ∨ valuation q 81 = false ∨ valuation q 118 = false := by
  rw [value46, value81, value118, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (255 : Vertex) (383 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 46 = false ∨ valuation q 81 = false ∨ valuation q 121 = false := by
  rw [value46, value81, value121, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (255 : Vertex) (383 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 46 = false ∨ valuation q 81 = false ∨ valuation q 122 = false := by
  rw [value46, value81, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (255 : Vertex) (383 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 46 = false ∨ valuation q 100 = false ∨ valuation q 113 = false := by
  rw [value46, value100, value113, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (255 : Vertex) (447 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 46 = false ∨ valuation q 100 = false ∨ valuation q 118 = false := by
  rw [value46, value100, value118, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (255 : Vertex) (447 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 46 = false ∨ valuation q 100 = false ∨ valuation q 121 = false := by
  rw [value46, value100, value121, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (255 : Vertex) (447 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 46 = false ∨ valuation q 100 = false ∨ valuation q 122 = false := by
  rw [value46, value100, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (255 : Vertex) (447 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 46 = false ∨ valuation q 113 = false ∨ valuation q 118 = false := by
  rw [value46, value113, value118, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (255 : Vertex) (495 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 46 = false ∨ valuation q 113 = false ∨ valuation q 121 = false := by
  rw [value46, value113, value121, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (255 : Vertex) (495 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 46 = false ∨ valuation q 113 = false ∨ valuation q 122 = false := by
  rw [value46, value113, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (255 : Vertex) (495 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 46 = false ∨ valuation q 118 = false ∨ valuation q 121 = false := by
  rw [value46, value118, value121, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (255 : Vertex) (503 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 46 = false ∨ valuation q 118 = false ∨ valuation q 122 = false := by
  rw [value46, value118, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (255 : Vertex) (503 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 46 = false ∨ valuation q 121 = false ∨ valuation q 122 = false := by
  rw [value46, value121, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (255 : Vertex) (507 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 81 = false ∨ valuation q 100 = false ∨ valuation q 113 = false := by
  rw [value81, value100, value113, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (383 : Vertex) (447 : Vertex) (495 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 81 = false ∨ valuation q 100 = false ∨ valuation q 118 = false := by
  rw [value81, value100, value118, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (383 : Vertex) (447 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 81 = false ∨ valuation q 100 = false ∨ valuation q 121 = false := by
  rw [value81, value100, value121, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (383 : Vertex) (447 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 81 = false ∨ valuation q 100 = false ∨ valuation q 122 = false := by
  rw [value81, value100, value122, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (383 : Vertex) (447 : Vertex) (509 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 81 = false ∨ valuation q 113 = false ∨ valuation q 118 = false := by
  rw [value81, value113, value118, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (383 : Vertex) (495 : Vertex) (503 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E097.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112097
