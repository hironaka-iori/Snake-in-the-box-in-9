import E112026Semantics
import B112E026Inputs
namespace Snake9.Regrowth.E112026
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 41 = false ∨ valuation q 96 = false ∨ valuation q 119 = false := by
  rw [value41, value96, value116, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (500 : Vertex) (244 : Vertex) (436 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 41 = false ∨ valuation q 117 = false ∨ valuation q 119 = false := by
  rw [value41, value116, value117, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (500 : Vertex) (244 : Vertex) (502 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 74 = false ∨ valuation q 96 = false ∨ valuation q 117 = false := by
  rw [value74, value96, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (500 : Vertex) (372 : Vertex) (436 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 74 = false ∨ valuation q 96 = false ∨ valuation q 119 = false := by
  rw [value74, value96, value116, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (500 : Vertex) (372 : Vertex) (436 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 74 = false ∨ valuation q 117 = false ∨ valuation q 119 = false := by
  rw [value74, value116, value117, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (500 : Vertex) (372 : Vertex) (502 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 96 = false ∨ valuation q 117 = false ∨ valuation q 119 = false := by
  rw [value96, value116, value117, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (500 : Vertex) (436 : Vertex) (502 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 106 = false ∨ valuation q 114 = false ∨ valuation q 116 = false := by
  rw [value106, value114, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (502 : Vertex) (486 : Vertex) (498 : Vertex) (500 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 106 = false ∨ valuation q 114 = false ∨ valuation q 121 = false := by
  rw [value106, value114, value117, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (502 : Vertex) (486 : Vertex) (498 : Vertex) (510 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 106 = false ∨ valuation q 116 = false ∨ valuation q 121 = false := by
  rw [value106, value116, value117, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (502 : Vertex) (486 : Vertex) (500 : Vertex) (510 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 238 = true ∨ valuation q 106 = true ∨ valuation q 114 = true ∨ valuation q 121 = true := by
  rw [value106, value114, value117, value121, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (502 : Vertex) w → w ∈ region → w ≠ (500 : Vertex) → w ∈ [(486 : Vertex), (498 : Vertex), (510 : Vertex)] := by decide
  have hg := other_cover q (502 : Vertex) (500 : Vertex) [(486 : Vertex), (498 : Vertex), (510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 101 = false ∨ valuation q 114 = false ∨ valuation q 121 = false := by
  rw [value101, value114, value118, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (506 : Vertex) (442 : Vertex) (498 : Vertex) (510 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 239 = true ∨ valuation q 101 = true ∨ valuation q 114 = true ∨ valuation q 121 = true := by
  rw [value101, value114, value118, value121, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (506 : Vertex) w → w ∈ region → w ≠ (250 : Vertex) → w ∈ [(442 : Vertex), (498 : Vertex), (510 : Vertex)] := by decide
  have hg := other_cover q (506 : Vertex) (250 : Vertex) [(442 : Vertex), (498 : Vertex), (510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 239 = true ∨ valuation q 46 = true ∨ valuation q 114 = true ∨ valuation q 121 = true := by
  rw [value46, value114, value118, value121, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (506 : Vertex) w → w ∈ region → w ≠ (442 : Vertex) → w ∈ [(250 : Vertex), (498 : Vertex), (510 : Vertex)] := by decide
  have hg := other_cover q (506 : Vertex) (442 : Vertex) [(250 : Vertex), (498 : Vertex), (510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 239 = true ∨ valuation q 46 = true ∨ valuation q 101 = true ∨ valuation q 121 = true := by
  rw [value46, value101, value118, value121, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (506 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(250 : Vertex), (442 : Vertex), (510 : Vertex)] := by decide
  have hg := other_cover q (506 : Vertex) (498 : Vertex) [(250 : Vertex), (442 : Vertex), (510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 116 = false ∨ valuation q 120 = false ∨ valuation q 121 = false := by
  rw [value116, value119, value120, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (508 : Vertex) (500 : Vertex) (509 : Vertex) (510 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 240 = true ∨ valuation q 120 = true ∨ valuation q 121 = true := by
  rw [value119, value120, value121, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (508 : Vertex) w → w ∈ region → w ≠ (500 : Vertex) → w ∈ [(509 : Vertex), (510 : Vertex)] := by decide
  have hg := other_cover q (508 : Vertex) (500 : Vertex) [(509 : Vertex), (510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 240 = true ∨ valuation q 116 = true ∨ valuation q 121 = true := by
  rw [value116, value119, value121, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (508 : Vertex) w → w ∈ region → w ≠ (509 : Vertex) → w ∈ [(500 : Vertex), (510 : Vertex)] := by decide
  have hg := other_cover q (508 : Vertex) (509 : Vertex) [(500 : Vertex), (510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 119 = false ∨ valuation q 240 = true ∨ valuation q 116 = true ∨ valuation q 120 = true := by
  rw [value116, value119, value120, value240]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (508 : Vertex) w → w ∈ region → w ≠ (510 : Vertex) → w ∈ [(500 : Vertex), (509 : Vertex)] := by decide
  have hg := other_cover q (508 : Vertex) (510 : Vertex) [(500 : Vertex), (509 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 241 = true ∨ valuation q 119 = true := by
  rw [value119, value120, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (509 : Vertex) w → w ∈ region → w ≠ (493 : Vertex) → w ∈ [(508 : Vertex)] := by decide
  have hg := other_cover q (509 : Vertex) (493 : Vertex) [(508 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 120 = false ∨ valuation q 241 = true ∨ valuation q 111 = true := by
  rw [value111, value120, value241]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (509 : Vertex) w → w ∈ region → w ≠ (508 : Vertex) → w ∈ [(493 : Vertex)] := by decide
  have hg := other_cover q (509 : Vertex) (508 : Vertex) [(493 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 121 = false ∨ valuation q 117 = false ∨ valuation q 118 = false ∨ valuation q 119 = false := by
  rw [value117, value118, value119, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (510 : Vertex) (502 : Vertex) (506 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 122 = false := by
  rw [value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (35 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 127 = false := by
  rw [value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (52 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 129 = false := by
  rw [value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (55 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 132 = false := by
  rw [value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (103 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 134 = false := by
  rw [value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (161 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 135 = false := by
  rw [value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (162 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 139 = false := by
  rw [value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (168 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 140 = false := by
  rw [value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (171 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 141 = false := by
  rw [value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (173 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 143 = false := by
  rw [value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (176 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 146 = false := by
  rw [value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  apply endpoint_parity_exclude q (179 : Vertex)
  · rw [h.head_fixed]; decide
  · rw [h.head_fixed]; decide

theorem block19 (q : Snake 81) (h : Conditions q) : B112E026.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112026
