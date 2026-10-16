import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 50 = false ∨ valuation q 113 = false ∨ valuation q 119 = false := by
  rw [value50, value113, value118, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (248 : Vertex) (496 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 98 = false ∨ valuation q 109 = false ∨ valuation q 113 = false := by
  rw [value98, value109, value113, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (440 : Vertex) (488 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 98 = false ∨ valuation q 109 = false ∨ valuation q 119 = false := by
  rw [value98, value109, value118, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (440 : Vertex) (488 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 98 = false ∨ valuation q 113 = false ∨ valuation q 119 = false := by
  rw [value98, value113, value118, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (440 : Vertex) (496 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 109 = false ∨ valuation q 113 = false ∨ valuation q 119 = false := by
  rw [value109, value113, value118, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (488 : Vertex) (496 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 240 = false ∨ valuation q 50 = false ∨ valuation q 113 = false := by
  rw [value50, value113, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (504 : Vertex) (248 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide)

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 118 = false ∨ valuation q 120 = false ∨ valuation q 121 = false := by
  rw [value118, value119, value120, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (508 : Vertex) (504 : Vertex) (509 : Vertex) (510 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 241 = true ∨ valuation q 120 = true ∨ valuation q 121 = true := by
  rw [value119, value120, value121, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (508 : Vertex) w → w ∈ region → w ≠ (504 : Vertex) → w ∈ [(509 : Vertex), (510 : Vertex)] := by decide
  have hg := other_cover q (508 : Vertex) (504 : Vertex) [(509 : Vertex), (510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 241 = true ∨ valuation q 118 = true ∨ valuation q 121 = true := by
  rw [value118, value119, value121, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (508 : Vertex) w → w ∈ region → w ≠ (509 : Vertex) → w ∈ [(504 : Vertex), (510 : Vertex)] := by decide
  have hg := other_cover q (508 : Vertex) (509 : Vertex) [(504 : Vertex), (510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 241 = true ∨ valuation q 118 = true ∨ valuation q 120 = true := by
  rw [value118, value119, value120, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (508 : Vertex) w → w ∈ region → w ≠ (510 : Vertex) → w ∈ [(504 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (508 : Vertex) (510 : Vertex) [(504 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 111 = false ∨ valuation q 119 = false ∨ valuation q 122 = false := by
  rw [value111, value119, value120, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (509 : Vertex) (493 : Vertex) (508 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 242 = false ∨ valuation q 111 = false ∨ valuation q 122 = false := by
  rw [value111, value122, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (509 : Vertex) (493 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide)

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 242 = true ∨ valuation q 119 = true ∨ valuation q 122 = true := by
  rw [value119, value120, value122, value242]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (509 : Vertex) w → w ∈ region → w ≠ (493 : Vertex) → w ∈ [(508 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (509 : Vertex) (493 : Vertex) [(508 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 117 = false ∨ valuation q 119 = false ∨ valuation q 122 = false := by
  rw [value117, value119, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (510 : Vertex) (502 : Vertex) (508 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 243 = true ∨ valuation q 119 = true ∨ valuation q 122 = true := by
  rw [value119, value121, value122, value243]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (510 : Vertex) w → w ∈ region → w ≠ (502 : Vertex) → w ∈ [(508 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (510 : Vertex) (502 : Vertex) [(508 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 54 = false ∨ valuation q 112 = false ∨ valuation q 121 = false := by
  rw [value54, value112, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (255 : Vertex) (495 : Vertex) (510 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 54 = false ∨ valuation q 120 = false ∨ valuation q 121 = false := by
  rw [value54, value120, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (255 : Vertex) (509 : Vertex) (510 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 102 = false ∨ valuation q 112 = false ∨ valuation q 121 = false := by
  rw [value102, value112, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (447 : Vertex) (495 : Vertex) (510 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 102 = false ∨ valuation q 120 = false ∨ valuation q 121 = false := by
  rw [value102, value120, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (447 : Vertex) (509 : Vertex) (510 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 122 = false ∨ valuation q 112 = false ∨ valuation q 120 = false ∨ valuation q 121 = false := by
  rw [value112, value120, value121, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (511 : Vertex) (495 : Vertex) (509 : Vertex) (510 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 124 = false := by
  rw [value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (35 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 126 = false := by
  rw [value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (37 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 128 = false := by
  rw [value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (42 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 130 = false := by
  rw [value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (44 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 132 = false := by
  rw [value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (52 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 134 = false := by
  rw [value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (55 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 135 = false := by
  rw [value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (56 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 137 = false := by
  rw [value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (59 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 140 = false := by
  rw [value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (100 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 141 = false := by
  rw [value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (103 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 143 = false := by
  rw [value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (161 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 145 = false := by
  rw [value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (167 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem block20 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.First112
