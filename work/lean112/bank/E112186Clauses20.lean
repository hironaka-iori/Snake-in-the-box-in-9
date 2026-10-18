import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 101 = false ∨ valuation q 113 = false ∨ valuation q 122 = false := by
  rw [value101, value113, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (474 : Vertex) (410 : Vertex) (458 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 120 = true ∨ valuation q 121 = true ∨ valuation q 124 = true := by
  rw [value120, value121, value122, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (475 : Vertex) w → w ∈ region → w ∈ [(473 : Vertex), (474 : Vertex), (479 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (475 : Vertex) [(473 : Vertex), (474 : Vertex), (479 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 120 = false ∨ valuation q 121 = false ∨ valuation q 124 = false := by
  rw [value120, value121, value122, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (475 : Vertex) (473 : Vertex) (474 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 246 = true ∨ valuation q 121 = true ∨ valuation q 124 = true := by
  rw [value121, value122, value124, value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (475 : Vertex) w → w ∈ region → w ≠ (473 : Vertex) → w ∈ [(474 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (475 : Vertex) (473 : Vertex) [(474 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 246 = true ∨ valuation q 120 = true ∨ valuation q 124 = true := by
  rw [value120, value122, value124, value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (475 : Vertex) w → w ∈ region → w ≠ (474 : Vertex) → w ∈ [(473 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (475 : Vertex) (474 : Vertex) [(473 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 246 = true ∨ valuation q 120 = true ∨ valuation q 121 = true := by
  rw [value120, value121, value122, value246]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (475 : Vertex) w → w ∈ region → w ≠ (479 : Vertex) → w ∈ [(473 : Vertex), (474 : Vertex)] := by decide
  have hg := other_cover q (475 : Vertex) (479 : Vertex) [(473 : Vertex), (474 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 45 = false ∨ valuation q 103 = false ∨ valuation q 120 = false := by
  rw [value45, value103, value120, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (477 : Vertex) (221 : Vertex) (413 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 45 = false ∨ valuation q 103 = false ∨ valuation q 124 = false := by
  rw [value45, value103, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (477 : Vertex) (221 : Vertex) (413 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 45 = false ∨ valuation q 118 = false ∨ valuation q 120 = false := by
  rw [value45, value118, value120, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (477 : Vertex) (221 : Vertex) (469 : Vertex) (473 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 45 = false ∨ valuation q 118 = false ∨ valuation q 124 = false := by
  rw [value45, value118, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (477 : Vertex) (221 : Vertex) (469 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 123 = false ∨ valuation q 103 = false ∨ valuation q 118 = false ∨ valuation q 124 = false := by
  rw [value103, value118, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (477 : Vertex) (413 : Vertex) (469 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 81 = false ∨ valuation q 119 = false ∨ valuation q 122 = false := by
  rw [value81, value119, value122, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (479 : Vertex) (351 : Vertex) (471 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 81 = false ∨ valuation q 122 = false ∨ valuation q 123 = false := by
  rw [value81, value122, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (479 : Vertex) (351 : Vertex) (475 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 124 = false ∨ valuation q 119 = false ∨ valuation q 122 = false ∨ valuation q 123 = false := by
  rw [value119, value122, value123, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (479 : Vertex) (471 : Vertex) (475 : Vertex) (477 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 125 = false := by
  rw [value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (69 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 127 = false := by
  rw [value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (74 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 129 = false := by
  rw [value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (76 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 132 = false := by
  rw [value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (87 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 134 = false := by
  rw [value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (91 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 137 = false := by
  rw [value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (131 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 139 = false := by
  rw [value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (133 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 140 = false := by
  rw [value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (137 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 141 = false := by
  rw [value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (138 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 143 = false := by
  rw [value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (140 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 146 = false := by
  rw [value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (148 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 149 = false := by
  rw [value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (151 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 150 = false := by
  rw [value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (152 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 152 = false := by
  rw [value152]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (155 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 155 = false := by
  rw [value155]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (193 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 157 = false := by
  rw [value157]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (199 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 158 = false := by
  rw [value158]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (200 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 160 = false := by
  rw [value160]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (203 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem block20 (q : Snake 81) (h : Conditions q) : B112E186.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112186
