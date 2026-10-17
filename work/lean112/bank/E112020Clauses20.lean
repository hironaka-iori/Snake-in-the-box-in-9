import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 78 = false ∨ valuation q 94 = false ∨ valuation q 104 = false := by
  rw [value78, value94, value104, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (370 : Vertex) (434 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 78 = false ∨ valuation q 94 = false ∨ valuation q 113 = false := by
  rw [value78, value94, value113, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (370 : Vertex) (434 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 78 = false ∨ valuation q 94 = false ∨ valuation q 116 = false := by
  rw [value78, value94, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (370 : Vertex) (434 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 78 = false ∨ valuation q 94 = false ∨ valuation q 118 = false := by
  rw [value78, value94, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (370 : Vertex) (434 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 78 = false ∨ valuation q 104 = false ∨ valuation q 113 = false := by
  rw [value78, value104, value113, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (370 : Vertex) (482 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 78 = false ∨ valuation q 104 = false ∨ valuation q 116 = false := by
  rw [value78, value104, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (370 : Vertex) (482 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 78 = false ∨ valuation q 104 = false ∨ valuation q 118 = false := by
  rw [value78, value104, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (370 : Vertex) (482 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 78 = false ∨ valuation q 113 = false ∨ valuation q 116 = false := by
  rw [value78, value113, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (370 : Vertex) (496 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 78 = false ∨ valuation q 113 = false ∨ valuation q 118 = false := by
  rw [value78, value113, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (370 : Vertex) (496 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 78 = false ∨ valuation q 116 = false ∨ valuation q 118 = false := by
  rw [value78, value115, value116, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (370 : Vertex) (499 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 94 = false ∨ valuation q 104 = false ∨ valuation q 113 = false := by
  rw [value94, value104, value113, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (434 : Vertex) (482 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 94 = false ∨ valuation q 104 = false ∨ valuation q 116 = false := by
  rw [value94, value104, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (434 : Vertex) (482 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 94 = false ∨ valuation q 104 = false ∨ valuation q 118 = false := by
  rw [value94, value104, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (434 : Vertex) (482 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 94 = false ∨ valuation q 113 = false ∨ valuation q 116 = false := by
  rw [value94, value113, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (434 : Vertex) (496 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 94 = false ∨ valuation q 113 = false ∨ valuation q 118 = false := by
  rw [value94, value113, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (434 : Vertex) (496 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 94 = false ∨ valuation q 116 = false ∨ valuation q 118 = false := by
  rw [value94, value115, value116, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (434 : Vertex) (499 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 104 = false ∨ valuation q 113 = false ∨ valuation q 116 = false := by
  rw [value104, value113, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (482 : Vertex) (496 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 104 = false ∨ valuation q 113 = false ∨ valuation q 118 = false := by
  rw [value104, value113, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (482 : Vertex) (496 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 104 = false ∨ valuation q 116 = false ∨ valuation q 118 = false := by
  rw [value104, value115, value116, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (482 : Vertex) (499 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 113 = false ∨ valuation q 116 = false ∨ valuation q 118 = false := by
  rw [value113, value115, value116, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (496 : Vertex) (499 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 239 = true ∨ valuation q 61 = true ∨ valuation q 94 = true ∨ valuation q 104 = true ∨ valuation q 113 = true ∨ valuation q 116 = true ∨ valuation q 118 = true := by
  rw [value61, value94, value104, value113, value115, value116, value118, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (498 : Vertex) w → w ∈ region → w ≠ (370 : Vertex) → w ∈ [(242 : Vertex), (434 : Vertex), (482 : Vertex), (496 : Vertex), (499 : Vertex), (502 : Vertex)] := by decide
  have hg := other_cover q (498 : Vertex) (370 : Vertex) [(242 : Vertex), (434 : Vertex), (482 : Vertex), (496 : Vertex), (499 : Vertex), (502 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 62 = false ∨ valuation q 79 = false ∨ valuation q 105 = false := by
  rw [value62, value79, value105, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (243 : Vertex) (371 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 62 = false ∨ valuation q 95 = false ∨ valuation q 105 = false := by
  rw [value62, value95, value105, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (243 : Vertex) (435 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 79 = false ∨ valuation q 95 = false ∨ valuation q 105 = false := by
  rw [value79, value95, value105, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (371 : Vertex) (435 : Vertex) (483 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 79 = false ∨ valuation q 95 = false ∨ valuation q 115 = false := by
  rw [value79, value95, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (371 : Vertex) (435 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 79 = false ∨ valuation q 115 = false ∨ valuation q 120 = false := by
  rw [value79, value115, value116, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (371 : Vertex) (498 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 95 = false ∨ valuation q 105 = false ∨ valuation q 114 = false := by
  rw [value95, value105, value114, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (435 : Vertex) (483 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 95 = false ∨ valuation q 105 = false ∨ valuation q 120 = false := by
  rw [value95, value105, value116, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (435 : Vertex) (483 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 240 = true ∨ valuation q 62 = true ∨ valuation q 95 = true ∨ valuation q 105 = true ∨ valuation q 114 = true ∨ valuation q 115 = true ∨ valuation q 120 = true := by
  rw [value62, value95, value105, value114, value115, value116, value120, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (499 : Vertex) w → w ∈ region → w ≠ (371 : Vertex) → w ∈ [(243 : Vertex), (435 : Vertex), (483 : Vertex), (497 : Vertex), (498 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (499 : Vertex) (371 : Vertex) [(243 : Vertex), (435 : Vertex), (483 : Vertex), (497 : Vertex), (498 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 240 = true ∨ valuation q 62 = true ∨ valuation q 79 = true ∨ valuation q 105 = true ∨ valuation q 114 = true ∨ valuation q 115 = true ∨ valuation q 120 = true := by
  rw [value62, value79, value105, value114, value115, value116, value120, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (499 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(243 : Vertex), (371 : Vertex), (483 : Vertex), (497 : Vertex), (498 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (499 : Vertex) (435 : Vertex) [(243 : Vertex), (371 : Vertex), (483 : Vertex), (497 : Vertex), (498 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 240 = true ∨ valuation q 62 = true ∨ valuation q 79 = true ∨ valuation q 95 = true ∨ valuation q 105 = true ∨ valuation q 114 = true ∨ valuation q 120 = true := by
  rw [value62, value79, value95, value105, value114, value116, value120, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (499 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(243 : Vertex), (371 : Vertex), (435 : Vertex), (483 : Vertex), (497 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (499 : Vertex) (498 : Vertex) [(243 : Vertex), (371 : Vertex), (435 : Vertex), (483 : Vertex), (497 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 80 = false ∨ valuation q 96 = false ∨ valuation q 113 = false := by
  rw [value80, value96, value113, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (500 : Vertex) (372 : Vertex) (436 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E020.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112020
