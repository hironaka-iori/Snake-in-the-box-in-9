import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 22 = false ∨ valuation q 106 = false ∨ valuation q 117 = false := by
  rw [value22, value96, value106, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (141 : Vertex) (413 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 57 = false ∨ valuation q 89 = false ∨ valuation q 93 = false := by
  rw [value57, value89, value93, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (269 : Vertex) (389 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 57 = false ∨ valuation q 89 = false ∨ valuation q 106 = false := by
  rw [value57, value89, value96, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (269 : Vertex) (389 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 57 = false ∨ valuation q 89 = false ∨ valuation q 117 = false := by
  rw [value57, value89, value96, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (269 : Vertex) (389 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 57 = false ∨ valuation q 93 = false ∨ valuation q 106 = false := by
  rw [value57, value93, value96, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (269 : Vertex) (393 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 57 = false ∨ valuation q 93 = false ∨ valuation q 117 = false := by
  rw [value57, value93, value96, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (269 : Vertex) (393 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 89 = false ∨ valuation q 93 = false ∨ valuation q 106 = false := by
  rw [value89, value93, value96, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (389 : Vertex) (393 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 89 = false ∨ valuation q 93 = false ∨ valuation q 117 = false := by
  rw [value89, value93, value96, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (397 : Vertex) (389 : Vertex) (393 : Vertex) (461 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 224 = true ∨ valuation q 57 = true ∨ valuation q 89 = true ∨ valuation q 93 = true ∨ valuation q 106 = true ∨ valuation q 117 = true := by
  rw [value57, value89, value93, value96, value106, value117, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (141 : Vertex) → w ∈ [(269 : Vertex), (389 : Vertex), (393 : Vertex), (413 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (141 : Vertex) [(269 : Vertex), (389 : Vertex), (393 : Vertex), (413 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 224 = true ∨ valuation q 22 = true ∨ valuation q 89 = true ∨ valuation q 93 = true ∨ valuation q 106 = true ∨ valuation q 117 = true := by
  rw [value22, value89, value93, value96, value106, value117, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (269 : Vertex) → w ∈ [(141 : Vertex), (389 : Vertex), (393 : Vertex), (413 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (269 : Vertex) [(141 : Vertex), (389 : Vertex), (393 : Vertex), (413 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 224 = true ∨ valuation q 22 = true ∨ valuation q 57 = true ∨ valuation q 93 = true ∨ valuation q 106 = true ∨ valuation q 117 = true := by
  rw [value22, value57, value93, value96, value106, value117, value224]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (397 : Vertex) w → w ∈ region → w ≠ (389 : Vertex) → w ∈ [(141 : Vertex), (269 : Vertex), (393 : Vertex), (413 : Vertex), (461 : Vertex)] := by decide
  have hg := other_cover q (397 : Vertex) (389 : Vertex) [(141 : Vertex), (269 : Vertex), (393 : Vertex), (413 : Vertex), (461 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 23 = false ∨ valuation q 58 = false ∨ valuation q 94 = false := by
  rw [value23, value58, value94, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (142 : Vertex) (270 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 23 = false ∨ valuation q 58 = false ∨ valuation q 118 = false := by
  rw [value23, value58, value97, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (142 : Vertex) (270 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 23 = false ∨ valuation q 90 = false ∨ valuation q 94 = false := by
  rw [value23, value90, value94, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (142 : Vertex) (390 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 23 = false ∨ valuation q 90 = false ∨ valuation q 118 = false := by
  rw [value23, value90, value97, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (142 : Vertex) (390 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 23 = false ∨ valuation q 94 = false ∨ valuation q 118 = false := by
  rw [value23, value94, value97, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (142 : Vertex) (394 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 58 = false ∨ valuation q 90 = false ∨ valuation q 94 = false := by
  rw [value58, value90, value94, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (270 : Vertex) (390 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 58 = false ∨ valuation q 90 = false ∨ valuation q 118 = false := by
  rw [value58, value90, value97, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (270 : Vertex) (390 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 58 = false ∨ valuation q 94 = false ∨ valuation q 118 = false := by
  rw [value58, value94, value97, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (270 : Vertex) (394 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 90 = false ∨ valuation q 94 = false ∨ valuation q 107 = false := by
  rw [value90, value94, value97, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (390 : Vertex) (394 : Vertex) (414 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 90 = false ∨ valuation q 94 = false ∨ valuation q 118 = false := by
  rw [value90, value94, value97, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (390 : Vertex) (394 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 90 = false ∨ valuation q 107 = false ∨ valuation q 118 = false := by
  rw [value90, value97, value107, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (390 : Vertex) (414 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 94 = false ∨ valuation q 107 = false ∨ valuation q 118 = false := by
  rw [value94, value97, value107, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (398 : Vertex) (394 : Vertex) (414 : Vertex) (462 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 225 = true ∨ valuation q 23 = true ∨ valuation q 90 = true ∨ valuation q 94 = true ∨ valuation q 107 = true ∨ valuation q 118 = true := by
  rw [value23, value90, value94, value97, value107, value118, value225]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (398 : Vertex) w → w ∈ region → w ≠ (270 : Vertex) → w ∈ [(142 : Vertex), (390 : Vertex), (394 : Vertex), (414 : Vertex), (462 : Vertex)] := by decide
  have hg := other_cover q (398 : Vertex) (270 : Vertex) [(142 : Vertex), (390 : Vertex), (394 : Vertex), (414 : Vertex), (462 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 226 = false ∨ valuation q 98 = true := by
  rw [value98, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (401 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 100 = true ∨ valuation q 103 = true := by
  rw [value98, value100, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ∈ [(405 : Vertex), (409 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (401 : Vertex) [(405 : Vertex), (409 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 226 = false ∨ valuation q 100 = false ∨ valuation q 103 = false := by
  rw [value100, value103, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (401 : Vertex) (405 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide)

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 226 = true ∨ valuation q 103 = true := by
  rw [value98, value103, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ≠ (405 : Vertex) → w ∈ [(409 : Vertex)] := by decide
  have hg := other_cover q (401 : Vertex) (405 : Vertex) [(409 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 226 = true ∨ valuation q 100 = true := by
  rw [value98, value100, value226]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (401 : Vertex) w → w ∈ region → w ≠ (409 : Vertex) → w ∈ [(405 : Vertex)] := by decide
  have hg := other_cover q (401 : Vertex) (409 : Vertex) [(405 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 99 = true := by
  rw [value99, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (404 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 88 = false ∨ valuation q 100 = false ∨ valuation q 101 = false := by
  rw [value88, value99, value100, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (404 : Vertex) (388 : Vertex) (405 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 227 = false ∨ valuation q 88 = false ∨ valuation q 101 = false := by
  rw [value88, value101, value227]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (404 : Vertex) (388 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E050.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112050
