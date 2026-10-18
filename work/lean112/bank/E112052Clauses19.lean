import E112052Semantics
import B112E052Inputs
namespace Snake9.Regrowth.E112052
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 57 = false ∨ valuation q 92 = false ∨ valuation q 105 = false := by
  rw [value57, value92, value95, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (269 : Vertex) (393 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 57 = false ∨ valuation q 92 = false ∨ valuation q 116 = false := by
  rw [value57, value92, value95, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (269 : Vertex) (393 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 88 = false ∨ valuation q 92 = false ∨ valuation q 105 = false := by
  rw [value88, value92, value95, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (389 : Vertex) (393 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 88 = false ∨ valuation q 92 = false ∨ valuation q 116 = false := by
  rw [value88, value92, value95, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (389 : Vertex) (393 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 222 = true ∨ valuation q 57 = true ∨ valuation q 88 = true ∨ valuation q 92 = true ∨ valuation q 105 = true ∨ valuation q 116 = true := by
  rw [value57, value88, value92, value95, value105, value116, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (141 : Vertex) → w ∈ [(269 : Vertex), (389 : Vertex), (393 : Vertex), (413 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (141 : Vertex) [(269 : Vertex), (389 : Vertex), (393 : Vertex), (413 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 222 = true ∨ valuation q 21 = true ∨ valuation q 88 = true ∨ valuation q 92 = true ∨ valuation q 105 = true ∨ valuation q 116 = true := by
  rw [value21, value88, value92, value95, value105, value116, value222]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (269 : Vertex) → w ∈ [(141 : Vertex), (389 : Vertex), (393 : Vertex), (413 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (269 : Vertex) [(141 : Vertex), (389 : Vertex), (393 : Vertex), (413 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 22 = false ∨ valuation q 89 = false ∨ valuation q 93 = false := by
  rw [value22, value89, value93, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (142 : Vertex) (390 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 22 = false ∨ valuation q 89 = false ∨ valuation q 106 = false := by
  rw [value22, value89, value96, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (142 : Vertex) (390 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 22 = false ∨ valuation q 89 = false ∨ valuation q 117 = false := by
  rw [value22, value89, value96, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (142 : Vertex) (390 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 22 = false ∨ valuation q 93 = false ∨ valuation q 117 = false := by
  rw [value22, value93, value96, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (142 : Vertex) (394 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 58 = false ∨ valuation q 89 = false ∨ valuation q 93 = false := by
  rw [value58, value89, value93, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (270 : Vertex) (390 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 58 = false ∨ valuation q 89 = false ∨ valuation q 117 = false := by
  rw [value58, value89, value96, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (270 : Vertex) (390 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 58 = false ∨ valuation q 93 = false ∨ valuation q 117 = false := by
  rw [value58, value93, value96, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (270 : Vertex) (394 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 89 = false ∨ valuation q 93 = false ∨ valuation q 106 = false := by
  rw [value89, value93, value96, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (390 : Vertex) (394 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 89 = false ∨ valuation q 93 = false ∨ valuation q 117 = false := by
  rw [value89, value93, value96, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (390 : Vertex) (394 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 89 = false ∨ valuation q 106 = false ∨ valuation q 117 = false := by
  rw [value89, value96, value106, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (390 : Vertex) (414 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 93 = false ∨ valuation q 106 = false ∨ valuation q 117 = false := by
  rw [value93, value96, value106, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (394 : Vertex) (414 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 223 = true ∨ valuation q 22 = true ∨ valuation q 89 = true ∨ valuation q 93 = true ∨ valuation q 106 = true ∨ valuation q 117 = true := by
  rw [value22, value89, value93, value96, value106, value117, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (398 : Vertex) w → w ∈ region → w ≠ (270 : Vertex) → w ∈ [(142 : Vertex), (390 : Vertex), (394 : Vertex), (414 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (398 : Vertex) (270 : Vertex) [(142 : Vertex), (390 : Vertex), (394 : Vertex), (414 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 223 = true ∨ valuation q 22 = true ∨ valuation q 58 = true ∨ valuation q 89 = true ∨ valuation q 93 = true ∨ valuation q 106 = true := by
  rw [value22, value58, value89, value93, value96, value106, value223]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (398 : Vertex) w → w ∈ region → w ≠ (462 : Vertex) → w ∈ [(142 : Vertex), (270 : Vertex), (390 : Vertex), (394 : Vertex), (414 : Vertex)] := by decide
  have hg := other_cover q (398 : Vertex) (462 : Vertex) [(142 : Vertex), (270 : Vertex), (390 : Vertex), (394 : Vertex), (414 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 24 = false ∨ valuation q 99 = false ∨ valuation q 102 = false := by
  rw [value24, value97, value99, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (401 : Vertex) (145 : Vertex) (405 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 224 = true ∨ valuation q 99 = true ∨ valuation q 102 = true := by
  rw [value97, value99, value102, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ≠ (145 : Vertex) → w ∈ [(405 : Vertex), (409 : Vertex)] := by decide
  have hg := other_cover q (401 : Vertex) (145 : Vertex) [(405 : Vertex), (409 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 224 = true ∨ valuation q 24 = true ∨ valuation q 102 = true := by
  rw [value24, value97, value102, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ≠ (405 : Vertex) → w ∈ [(145 : Vertex), (409 : Vertex)] := by decide
  have hg := other_cover q (401 : Vertex) (405 : Vertex) [(145 : Vertex), (409 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 224 = true ∨ valuation q 24 = true ∨ valuation q 99 = true := by
  rw [value24, value97, value99, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ≠ (409 : Vertex) → w ∈ [(145 : Vertex), (405 : Vertex)] := by decide
  have hg := other_cover q (401 : Vertex) (409 : Vertex) [(145 : Vertex), (405 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 225 = false ∨ valuation q 98 = true := by
  rw [value98, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (404 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 87 = true ∨ valuation q 99 = true ∨ valuation q 100 = true := by
  rw [value87, value98, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (404 : Vertex) w → w ∈ region → w ∈ [(388 : Vertex), (405 : Vertex), (406 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (404 : Vertex) [(388 : Vertex), (405 : Vertex), (406 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 87 = false ∨ valuation q 99 = false ∨ valuation q 100 = false := by
  rw [value87, value98, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (404 : Vertex) (388 : Vertex) (405 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 225 = false ∨ valuation q 99 = false ∨ valuation q 100 = false := by
  rw [value99, value100, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (404 : Vertex) (405 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide)

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 225 = true ∨ valuation q 99 = true ∨ valuation q 100 = true := by
  rw [value98, value99, value100, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (404 : Vertex) w → w ∈ region → w ≠ (388 : Vertex) → w ∈ [(405 : Vertex), (406 : Vertex)] := by decide
  have hg := other_cover q (404 : Vertex) (388 : Vertex) [(405 : Vertex), (406 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 225 = true ∨ valuation q 87 = true ∨ valuation q 100 = true := by
  rw [value87, value98, value100, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (404 : Vertex) w → w ∈ region → w ≠ (405 : Vertex) → w ∈ [(388 : Vertex), (406 : Vertex)] := by decide
  have hg := other_cover q (404 : Vertex) (405 : Vertex) [(388 : Vertex), (406 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 225 = true ∨ valuation q 87 = true ∨ valuation q 99 = true := by
  rw [value87, value98, value99, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (404 : Vertex) w → w ∈ region → w ≠ (406 : Vertex) → w ∈ [(388 : Vertex), (405 : Vertex)] := by decide
  have hg := other_cover q (404 : Vertex) (406 : Vertex) [(388 : Vertex), (405 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 88 = false ∨ valuation q 97 = false ∨ valuation q 98 = false := by
  rw [value88, value97, value98, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (405 : Vertex) (389 : Vertex) (401 : Vertex) (404 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 88 = false ∨ valuation q 97 = false ∨ valuation q 101 = false := by
  rw [value88, value97, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (405 : Vertex) (389 : Vertex) (401 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E052.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112052
