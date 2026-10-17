import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 47 = false ∨ valuation q 80 = false ∨ valuation q 113 = false := by
  rw [value47, value80, value112, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (296 : Vertex) (425 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 47 = false ∨ valuation q 80 = false ∨ valuation q 115 = false := by
  rw [value47, value80, value112, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (168 : Vertex) (296 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 80 = false ∨ valuation q 113 = false ∨ valuation q 115 = false := by
  rw [value80, value112, value113, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (424 : Vertex) (296 : Vertex) (425 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 232 = false ∨ valuation q 113 = false ∨ valuation q 115 = false := by
  rw [value113, value115, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (424 : Vertex) (425 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide)

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 232 = true ∨ valuation q 80 = true ∨ valuation q 113 = true ∨ valuation q 115 = true := by
  rw [value80, value112, value113, value115, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (424 : Vertex) w → w ∈ region → w ≠ (168 : Vertex) → w ∈ [(296 : Vertex), (425 : Vertex), (440 : Vertex)] := by decide
  have hg := other_cover q (424 : Vertex) (168 : Vertex) [(296 : Vertex), (425 : Vertex), (440 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 232 = true ∨ valuation q 47 = true ∨ valuation q 113 = true ∨ valuation q 115 = true := by
  rw [value47, value112, value113, value115, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (424 : Vertex) w → w ∈ region → w ≠ (296 : Vertex) → w ∈ [(168 : Vertex), (425 : Vertex), (440 : Vertex)] := by decide
  have hg := other_cover q (424 : Vertex) (296 : Vertex) [(168 : Vertex), (425 : Vertex), (440 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 232 = true ∨ valuation q 47 = true ∨ valuation q 80 = true ∨ valuation q 115 = true := by
  rw [value47, value80, value112, value115, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (424 : Vertex) w → w ∈ region → w ≠ (425 : Vertex) → w ∈ [(168 : Vertex), (296 : Vertex), (440 : Vertex)] := by decide
  have hg := other_cover q (424 : Vertex) (425 : Vertex) [(168 : Vertex), (296 : Vertex), (440 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 232 = true ∨ valuation q 47 = true ∨ valuation q 80 = true ∨ valuation q 113 = true := by
  rw [value47, value80, value112, value113, value232]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (424 : Vertex) w → w ∈ region → w ≠ (440 : Vertex) → w ∈ [(168 : Vertex), (296 : Vertex), (425 : Vertex)] := by decide
  have hg := other_cover q (424 : Vertex) (440 : Vertex) [(168 : Vertex), (296 : Vertex), (425 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 233 = true ∨ valuation q 114 = true := by
  rw [value113, value114, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (425 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(427 : Vertex)] := by decide
  have hg := other_cover q (425 : Vertex) (424 : Vertex) [(427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 233 = true ∨ valuation q 112 = true := by
  rw [value112, value113, value233]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (425 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(424 : Vertex)] := by decide
  have hg := other_cover q (425 : Vertex) (427 : Vertex) [(424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 234 = false ∨ valuation q 113 = false ∨ valuation q 116 = false := by
  rw [value113, value116, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (427 : Vertex) (425 : Vertex) (443 : Vertex) (by decide) (by decide) (by decide)

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 234 = true ∨ valuation q 116 = true := by
  rw [value114, value116, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (427 : Vertex) w → w ∈ region → w ≠ (425 : Vertex) → w ∈ [(443 : Vertex)] := by decide
  have hg := other_cover q (427 : Vertex) (425 : Vertex) [(443 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 234 = true ∨ valuation q 113 = true := by
  rw [value113, value114, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (427 : Vertex) w → w ∈ region → w ≠ (443 : Vertex) → w ∈ [(425 : Vertex)] := by decide
  have hg := other_cover q (427 : Vertex) (443 : Vertex) [(425 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 235 = true ∨ valuation q 112 = true := by
  rw [value112, value115, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (184 : Vertex) → w ∈ [(424 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (184 : Vertex) [(424 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 235 = true ∨ valuation q 55 = true := by
  rw [value55, value115, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (440 : Vertex) w → w ∈ region → w ≠ (424 : Vertex) → w ∈ [(184 : Vertex)] := by decide
  have hg := other_cover q (440 : Vertex) (424 : Vertex) [(184 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 57 = false ∨ valuation q 89 = false ∨ valuation q 114 = false := by
  rw [value57, value89, value114, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (187 : Vertex) (315 : Vertex) (427 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 57 = false ∨ valuation q 89 = false ∨ valuation q 119 = false := by
  rw [value57, value89, value116, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (187 : Vertex) (315 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 57 = false ∨ valuation q 114 = false ∨ valuation q 119 = false := by
  rw [value57, value114, value116, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (187 : Vertex) (427 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 89 = false ∨ valuation q 114 = false ∨ valuation q 119 = false := by
  rw [value89, value114, value116, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (443 : Vertex) (315 : Vertex) (427 : Vertex) (507 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 236 = true ∨ valuation q 89 = true ∨ valuation q 114 = true ∨ valuation q 119 = true := by
  rw [value89, value114, value116, value119, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (443 : Vertex) w → w ∈ region → w ≠ (187 : Vertex) → w ∈ [(315 : Vertex), (427 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (443 : Vertex) (187 : Vertex) [(315 : Vertex), (427 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 118 = true := by
  rw [value117, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (493 : Vertex) w → w ∈ region → w ∈ [(495 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (493 : Vertex) [(495 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 117 = true := by
  rw [value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 238 = true ∨ valuation q 120 = true := by
  rw [value118, value120, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (495 : Vertex) w → w ∈ region → w ≠ (493 : Vertex) → w ∈ [(511 : Vertex)] := by decide
  have hg := other_cover q (495 : Vertex) (493 : Vertex) [(511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 109 = false ∨ valuation q 116 = false ∨ valuation q 120 = false := by
  rw [value109, value116, value119, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (507 : Vertex) (379 : Vertex) (443 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 240 = true ∨ valuation q 74 = true ∨ valuation q 119 = true := by
  rw [value74, value119, value120, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (511 : Vertex) w → w ∈ region → w ≠ (495 : Vertex) → w ∈ [(255 : Vertex), (507 : Vertex)] := by decide
  have hg := other_cover q (511 : Vertex) (495 : Vertex) [(255 : Vertex), (507 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 123 = false := by
  rw [value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (37 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 124 = false := by
  rw [value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (38 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 126 = false := by
  rw [value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (41 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 127 = false := by
  rw [value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (42 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 129 = false := by
  rw [value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (44 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 132 = false := by
  rw [value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (49 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 135 = false := by
  rw [value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (55 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem block20 (q : Snake 81) (h : Conditions q) : B112E040.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112040
