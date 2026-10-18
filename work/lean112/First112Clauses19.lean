import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 110 = false ∨ valuation q 111 = false ∨ valuation q 122 = false := by
  rw [value110, value111, value112, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (495 : Vertex) (491 : Vertex) (493 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 234 = true ∨ valuation q 92 = true ∨ valuation q 110 = true ∨ valuation q 122 = true := by
  rw [value92, value110, value112, value122, value234]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (495 : Vertex) w → w ∈ region → w ≠ (493 : Vertex) → w ∈ [(431 : Vertex), (491 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (495 : Vertex) (493 : Vertex) [(431 : Vertex), (491 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 114 = false ∨ valuation q 115 = false ∨ valuation q 118 = false := by
  rw [value113, value114, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (496 : Vertex) (497 : Vertex) (498 : Vertex) (504 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 235 = true ∨ valuation q 114 = true ∨ valuation q 115 = true ∨ valuation q 118 = true := by
  rw [value113, value114, value115, value118, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (496 : Vertex) w → w ∈ region → w ≠ (480 : Vertex) → w ∈ [(497 : Vertex), (498 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (496 : Vertex) (480 : Vertex) [(497 : Vertex), (498 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 235 = true ∨ valuation q 103 = true ∨ valuation q 115 = true ∨ valuation q 118 = true := by
  rw [value103, value113, value115, value118, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (496 : Vertex) w → w ∈ region → w ≠ (497 : Vertex) → w ∈ [(480 : Vertex), (498 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (496 : Vertex) (497 : Vertex) [(480 : Vertex), (498 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 235 = true ∨ valuation q 103 = true ∨ valuation q 114 = true ∨ valuation q 118 = true := by
  rw [value103, value113, value114, value118, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (496 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(480 : Vertex), (497 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (496 : Vertex) (498 : Vertex) [(480 : Vertex), (497 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 235 = true ∨ valuation q 103 = true ∨ valuation q 114 = true ∨ valuation q 115 = true := by
  rw [value103, value113, value114, value115, value235]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (496 : Vertex) w → w ∈ region → w ≠ (504 : Vertex) → w ∈ [(480 : Vertex), (497 : Vertex), (498 : Vertex)] := by decide
  have hg := other_cover q (496 : Vertex) (504 : Vertex) [(480 : Vertex), (497 : Vertex), (498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 93 = false ∨ valuation q 104 = false ∨ valuation q 113 = false := by
  rw [value93, value104, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (433 : Vertex) (481 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 93 = false ∨ valuation q 104 = false ∨ valuation q 116 = false := by
  rw [value93, value104, value114, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (433 : Vertex) (481 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 93 = false ∨ valuation q 113 = false ∨ valuation q 116 = false := by
  rw [value93, value113, value114, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (433 : Vertex) (496 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 104 = false ∨ valuation q 113 = false ∨ valuation q 116 = false := by
  rw [value104, value113, value114, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (481 : Vertex) (496 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 236 = true ∨ valuation q 93 = true ∨ valuation q 104 = true ∨ valuation q 116 = true := by
  rw [value93, value104, value114, value116, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (497 : Vertex) w → w ∈ region → w ≠ (496 : Vertex) → w ∈ [(433 : Vertex), (481 : Vertex), (499 : Vertex)] := by decide
  have hg := other_cover q (497 : Vertex) (496 : Vertex) [(433 : Vertex), (481 : Vertex), (499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 236 = true ∨ valuation q 93 = true ∨ valuation q 104 = true ∨ valuation q 113 = true := by
  rw [value93, value104, value113, value114, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (497 : Vertex) w → w ∈ region → w ≠ (499 : Vertex) → w ∈ [(433 : Vertex), (481 : Vertex), (496 : Vertex)] := by decide
  have hg := other_cover q (497 : Vertex) (499 : Vertex) [(433 : Vertex), (481 : Vertex), (496 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 105 = false ∨ valuation q 113 = false ∨ valuation q 116 = false := by
  rw [value105, value113, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (482 : Vertex) (496 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 105 = false ∨ valuation q 113 = false ∨ valuation q 117 = false := by
  rw [value105, value113, value115, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (482 : Vertex) (496 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 105 = false ∨ valuation q 116 = false ∨ valuation q 117 = false := by
  rw [value105, value115, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (482 : Vertex) (499 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 113 = false ∨ valuation q 116 = false ∨ valuation q 117 = false := by
  rw [value113, value115, value116, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (496 : Vertex) (499 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 94 = false ∨ valuation q 106 = false ∨ valuation q 114 = false := by
  rw [value94, value106, value114, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (435 : Vertex) (483 : Vertex) (497 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 94 = false ∨ valuation q 106 = false ∨ valuation q 115 = false := by
  rw [value94, value106, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (499 : Vertex) (435 : Vertex) (483 : Vertex) (498 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 238 = true ∨ valuation q 106 = true ∨ valuation q 114 = true ∨ valuation q 115 = true := by
  rw [value106, value114, value115, value116, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (499 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(483 : Vertex), (497 : Vertex), (498 : Vertex)] := by decide
  have hg := other_cover q (499 : Vertex) (435 : Vertex) [(483 : Vertex), (497 : Vertex), (498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 238 = true ∨ valuation q 94 = true ∨ valuation q 114 = true ∨ valuation q 115 = true := by
  rw [value94, value114, value115, value116, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (499 : Vertex) w → w ∈ region → w ≠ (483 : Vertex) → w ∈ [(435 : Vertex), (497 : Vertex), (498 : Vertex)] := by decide
  have hg := other_cover q (499 : Vertex) (483 : Vertex) [(435 : Vertex), (497 : Vertex), (498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 238 = true ∨ valuation q 94 = true ∨ valuation q 106 = true ∨ valuation q 115 = true := by
  rw [value94, value106, value115, value116, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (499 : Vertex) w → w ∈ region → w ≠ (497 : Vertex) → w ∈ [(435 : Vertex), (483 : Vertex), (498 : Vertex)] := by decide
  have hg := other_cover q (499 : Vertex) (497 : Vertex) [(435 : Vertex), (483 : Vertex), (498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 116 = false ∨ valuation q 238 = true ∨ valuation q 94 = true ∨ valuation q 106 = true ∨ valuation q 114 = true := by
  rw [value94, value106, value114, value116, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (499 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(435 : Vertex), (483 : Vertex), (497 : Vertex)] := by decide
  have hg := other_cover q (499 : Vertex) (498 : Vertex) [(435 : Vertex), (483 : Vertex), (497 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 108 = false ∨ valuation q 115 = false ∨ valuation q 121 = false := by
  rw [value108, value115, value117, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (502 : Vertex) (486 : Vertex) (498 : Vertex) (510 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 239 = true ∨ valuation q 115 = true ∨ valuation q 121 = true := by
  rw [value115, value117, value121, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (502 : Vertex) w → w ∈ region → w ≠ (486 : Vertex) → w ∈ [(498 : Vertex), (510 : Vertex)] := by decide
  have hg := other_cover q (502 : Vertex) (486 : Vertex) [(498 : Vertex), (510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 239 = true ∨ valuation q 108 = true ∨ valuation q 121 = true := by
  rw [value108, value117, value121, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (502 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(486 : Vertex), (510 : Vertex)] := by decide
  have hg := other_cover q (502 : Vertex) (498 : Vertex) [(486 : Vertex), (510 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 117 = false ∨ valuation q 239 = true ∨ valuation q 108 = true ∨ valuation q 115 = true := by
  rw [value108, value115, value117, value239]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (502 : Vertex) w → w ∈ region → w ≠ (510 : Vertex) → w ∈ [(486 : Vertex), (498 : Vertex)] := by decide
  have hg := other_cover q (502 : Vertex) (510 : Vertex) [(486 : Vertex), (498 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left] using hg

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 50 = false ∨ valuation q 98 = false ∨ valuation q 109 = false := by
  rw [value50, value98, value109, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (248 : Vertex) (440 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 50 = false ∨ valuation q 98 = false ∨ valuation q 113 = false := by
  rw [value50, value98, value113, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (248 : Vertex) (440 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 50 = false ∨ valuation q 98 = false ∨ valuation q 119 = false := by
  rw [value50, value98, value118, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (248 : Vertex) (440 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 50 = false ∨ valuation q 109 = false ∨ valuation q 113 = false := by
  rw [value50, value109, value113, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (248 : Vertex) (488 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 118 = false ∨ valuation q 50 = false ∨ valuation q 109 = false ∨ valuation q 119 = false := by
  rw [value50, value109, value118, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (504 : Vertex) (248 : Vertex) (488 : Vertex) (508 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block19 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.First112
