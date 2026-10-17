import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 106 = false ∨ valuation q 109 = false ∨ valuation q 111 = false := by
  rw [value106, value109, value111, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (495 : Vertex) (487 : Vertex) (491 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 106 = false ∨ valuation q 109 = false ∨ valuation q 124 = false := by
  rw [value106, value109, value112, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (495 : Vertex) (487 : Vertex) (491 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 106 = false ∨ valuation q 111 = false ∨ valuation q 124 = false := by
  rw [value106, value111, value112, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (495 : Vertex) (487 : Vertex) (493 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 109 = false ∨ valuation q 111 = false ∨ valuation q 124 = false := by
  rw [value109, value111, value112, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (495 : Vertex) (491 : Vertex) (493 : Vertex) (511 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 236 = false ∨ valuation q 106 = false ∨ valuation q 109 = false := by
  rw [value106, value109, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (495 : Vertex) (487 : Vertex) (491 : Vertex) (by decide) (by decide) (by decide)

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 236 = false ∨ valuation q 106 = false ∨ valuation q 111 = false := by
  rw [value106, value111, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (495 : Vertex) (487 : Vertex) (493 : Vertex) (by decide) (by decide) (by decide)

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 112 = false ∨ valuation q 236 = true ∨ valuation q 109 = true ∨ valuation q 111 = true ∨ valuation q 124 = true := by
  rw [value109, value111, value112, value124, value236]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (495 : Vertex) w → w ∈ region → w ≠ (487 : Vertex) → w ∈ [(491 : Vertex), (493 : Vertex), (511 : Vertex)] := by decide
  have hg := other_cover q (495 : Vertex) (487 : Vertex) [(491 : Vertex), (493 : Vertex), (511 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 237 = true ∨ valuation q 114 = true ∨ valuation q 115 = true ∨ valuation q 117 = true ∨ valuation q 119 = true := by
  rw [value113, value114, value115, value117, value119, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (496 : Vertex) w → w ∈ region → w ≠ (480 : Vertex) → w ∈ [(497 : Vertex), (498 : Vertex), (500 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (496 : Vertex) (480 : Vertex) [(497 : Vertex), (498 : Vertex), (500 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 237 = true ∨ valuation q 102 = true ∨ valuation q 115 = true ∨ valuation q 117 = true ∨ valuation q 119 = true := by
  rw [value102, value113, value115, value117, value119, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (496 : Vertex) w → w ∈ region → w ≠ (497 : Vertex) → w ∈ [(480 : Vertex), (498 : Vertex), (500 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (496 : Vertex) (497 : Vertex) [(480 : Vertex), (498 : Vertex), (500 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 237 = true ∨ valuation q 102 = true ∨ valuation q 114 = true ∨ valuation q 117 = true ∨ valuation q 119 = true := by
  rw [value102, value113, value114, value117, value119, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (496 : Vertex) w → w ∈ region → w ≠ (498 : Vertex) → w ∈ [(480 : Vertex), (497 : Vertex), (500 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (496 : Vertex) (498 : Vertex) [(480 : Vertex), (497 : Vertex), (500 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 237 = true ∨ valuation q 102 = true ∨ valuation q 114 = true ∨ valuation q 115 = true ∨ valuation q 119 = true := by
  rw [value102, value113, value114, value115, value119, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (496 : Vertex) w → w ∈ region → w ≠ (500 : Vertex) → w ∈ [(480 : Vertex), (497 : Vertex), (498 : Vertex), (504 : Vertex)] := by decide
  have hg := other_cover q (496 : Vertex) (500 : Vertex) [(480 : Vertex), (497 : Vertex), (498 : Vertex), (504 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 113 = false ∨ valuation q 237 = true ∨ valuation q 102 = true ∨ valuation q 114 = true ∨ valuation q 115 = true ∨ valuation q 117 = true := by
  rw [value102, value113, value114, value115, value117, value237]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (496 : Vertex) w → w ∈ region → w ≠ (504 : Vertex) → w ∈ [(480 : Vertex), (497 : Vertex), (498 : Vertex), (500 : Vertex)] := by decide
  have hg := other_cover q (496 : Vertex) (504 : Vertex) [(480 : Vertex), (497 : Vertex), (498 : Vertex), (500 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 60 = false ∨ valuation q 103 = false ∨ valuation q 113 = false := by
  rw [value60, value103, value113, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (241 : Vertex) (481 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 60 = false ∨ valuation q 103 = false ∨ valuation q 116 = false := by
  rw [value60, value103, value114, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (241 : Vertex) (481 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 60 = false ∨ valuation q 113 = false ∨ valuation q 116 = false := by
  rw [value60, value113, value114, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (241 : Vertex) (496 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 103 = false ∨ valuation q 113 = false ∨ valuation q 116 = false := by
  rw [value103, value113, value114, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (497 : Vertex) (481 : Vertex) (496 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 114 = false ∨ valuation q 238 = true ∨ valuation q 60 = true ∨ valuation q 103 = true ∨ valuation q 116 = true := by
  rw [value60, value103, value114, value116, value238]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (497 : Vertex) w → w ∈ region → w ≠ (496 : Vertex) → w ∈ [(241 : Vertex), (481 : Vertex), (499 : Vertex)] := by decide
  have hg := other_cover q (497 : Vertex) (496 : Vertex) [(241 : Vertex), (481 : Vertex), (499 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 61 = false ∨ valuation q 78 = false ∨ valuation q 94 = false := by
  rw [value61, value78, value94, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (242 : Vertex) (370 : Vertex) (434 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 61 = false ∨ valuation q 78 = false ∨ valuation q 104 = false := by
  rw [value61, value78, value104, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (242 : Vertex) (370 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 61 = false ∨ valuation q 78 = false ∨ valuation q 113 = false := by
  rw [value61, value78, value113, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (242 : Vertex) (370 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 61 = false ∨ valuation q 78 = false ∨ valuation q 116 = false := by
  rw [value61, value78, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (242 : Vertex) (370 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 61 = false ∨ valuation q 78 = false ∨ valuation q 118 = false := by
  rw [value61, value78, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (242 : Vertex) (370 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 61 = false ∨ valuation q 94 = false ∨ valuation q 104 = false := by
  rw [value61, value94, value104, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (242 : Vertex) (434 : Vertex) (482 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 61 = false ∨ valuation q 94 = false ∨ valuation q 113 = false := by
  rw [value61, value94, value113, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (242 : Vertex) (434 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 61 = false ∨ valuation q 94 = false ∨ valuation q 116 = false := by
  rw [value61, value94, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (242 : Vertex) (434 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 61 = false ∨ valuation q 94 = false ∨ valuation q 118 = false := by
  rw [value61, value94, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (242 : Vertex) (434 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 61 = false ∨ valuation q 104 = false ∨ valuation q 113 = false := by
  rw [value61, value104, value113, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (242 : Vertex) (482 : Vertex) (496 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 61 = false ∨ valuation q 104 = false ∨ valuation q 116 = false := by
  rw [value61, value104, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (242 : Vertex) (482 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 61 = false ∨ valuation q 104 = false ∨ valuation q 118 = false := by
  rw [value61, value104, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (242 : Vertex) (482 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 61 = false ∨ valuation q 113 = false ∨ valuation q 116 = false := by
  rw [value61, value113, value115, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (242 : Vertex) (496 : Vertex) (499 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 61 = false ∨ valuation q 113 = false ∨ valuation q 118 = false := by
  rw [value61, value113, value115, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (242 : Vertex) (496 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 115 = false ∨ valuation q 61 = false ∨ valuation q 116 = false ∨ valuation q 118 = false := by
  rw [value61, value115, value116, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (498 : Vertex) (242 : Vertex) (499 : Vertex) (502 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E020.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112020
