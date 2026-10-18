import E112019Semantics
import B112E019Inputs
namespace Snake9.Regrowth.E112019
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 216 = false ∨ valuation q 95 = true := by
  rw [value95, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (409 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 94 = true ∨ valuation q 96 = true ∨ valuation q 97 = true := by
  rw [value94, value95, value96, value97]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ∈ [(408 : Vertex), (411 : Vertex), (413 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (409 : Vertex) [(408 : Vertex), (411 : Vertex), (413 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 216 = true ∨ valuation q 96 = true ∨ valuation q 97 = true := by
  rw [value95, value96, value97, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (408 : Vertex) → w ∈ [(411 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (408 : Vertex) [(411 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 216 = true ∨ valuation q 94 = true ∨ valuation q 97 = true := by
  rw [value94, value95, value97, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (411 : Vertex) → w ∈ [(408 : Vertex), (413 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (411 : Vertex) [(408 : Vertex), (413 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 95 = false ∨ valuation q 216 = true ∨ valuation q 94 = true ∨ valuation q 96 = true := by
  rw [value94, value95, value96, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (409 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(408 : Vertex), (411 : Vertex)] := by decide
  have hg := other_cover q (409 : Vertex) (413 : Vertex) [(408 : Vertex), (411 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 87 = false ∨ valuation q 95 = false ∨ valuation q 98 = false := by
  rw [value87, value95, value96, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (411 : Vertex) (395 : Vertex) (409 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 87 = false ∨ valuation q 95 = false ∨ valuation q 118 = false := by
  rw [value87, value95, value96, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (411 : Vertex) (395 : Vertex) (409 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 87 = false ∨ valuation q 98 = false ∨ valuation q 118 = false := by
  rw [value87, value96, value98, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (411 : Vertex) (395 : Vertex) (415 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 95 = false ∨ valuation q 98 = false ∨ valuation q 118 = false := by
  rw [value95, value96, value98, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (411 : Vertex) (409 : Vertex) (415 : Vertex) (475 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 217 = true ∨ valuation q 95 = true ∨ valuation q 98 = true ∨ valuation q 118 = true := by
  rw [value95, value96, value98, value118, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (411 : Vertex) w → w ∈ region → w ≠ (395 : Vertex) → w ∈ [(409 : Vertex), (415 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (411 : Vertex) (395 : Vertex) [(409 : Vertex), (415 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 217 = true ∨ valuation q 87 = true ∨ valuation q 98 = true ∨ valuation q 118 = true := by
  rw [value87, value96, value98, value118, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (411 : Vertex) w → w ∈ region → w ≠ (409 : Vertex) → w ∈ [(395 : Vertex), (415 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (411 : Vertex) (409 : Vertex) [(395 : Vertex), (415 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 217 = true ∨ valuation q 87 = true ∨ valuation q 95 = true ∨ valuation q 118 = true := by
  rw [value87, value95, value96, value118, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (411 : Vertex) w → w ∈ region → w ≠ (415 : Vertex) → w ∈ [(395 : Vertex), (409 : Vertex), (475 : Vertex)] := by decide
  have hg := other_cover q (411 : Vertex) (415 : Vertex) [(395 : Vertex), (409 : Vertex), (475 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 96 = false ∨ valuation q 217 = true ∨ valuation q 87 = true ∨ valuation q 95 = true ∨ valuation q 98 = true := by
  rw [value87, value95, value96, value98, value217]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (411 : Vertex) w → w ∈ region → w ≠ (475 : Vertex) → w ∈ [(395 : Vertex), (409 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (411 : Vertex) (475 : Vertex) [(395 : Vertex), (409 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 91 = false ∨ valuation q 95 = false ∨ valuation q 98 = false := by
  rw [value91, value95, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (413 : Vertex) (405 : Vertex) (409 : Vertex) (415 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 218 = true ∨ valuation q 95 = true ∨ valuation q 98 = true := by
  rw [value95, value97, value98, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (413 : Vertex) w → w ∈ region → w ≠ (405 : Vertex) → w ∈ [(409 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (413 : Vertex) (405 : Vertex) [(409 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 218 = true ∨ valuation q 91 = true ∨ valuation q 98 = true := by
  rw [value91, value97, value98, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (413 : Vertex) w → w ∈ region → w ≠ (409 : Vertex) → w ∈ [(405 : Vertex), (415 : Vertex)] := by decide
  have hg := other_cover q (413 : Vertex) (409 : Vertex) [(405 : Vertex), (415 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 97 = false ∨ valuation q 218 = true ∨ valuation q 91 = true ∨ valuation q 95 = true := by
  rw [value91, value95, value97, value218]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (413 : Vertex) w → w ∈ region → w ≠ (415 : Vertex) → w ∈ [(405 : Vertex), (409 : Vertex)] := by decide
  have hg := other_cover q (413 : Vertex) (415 : Vertex) [(405 : Vertex), (409 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 39 = false ∨ valuation q 93 = false ∨ valuation q 96 = false := by
  rw [value39, value93, value96, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (159 : Vertex) (407 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 39 = false ∨ valuation q 93 = false ∨ valuation q 97 = false := by
  rw [value39, value93, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (159 : Vertex) (407 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 39 = false ∨ valuation q 93 = false ∨ valuation q 121 = false := by
  rw [value39, value93, value98, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (159 : Vertex) (407 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 39 = false ∨ valuation q 96 = false ∨ valuation q 97 = false := by
  rw [value39, value96, value97, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (159 : Vertex) (411 : Vertex) (413 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 39 = false ∨ valuation q 96 = false ∨ valuation q 121 = false := by
  rw [value39, value96, value98, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (159 : Vertex) (411 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 39 = false ∨ valuation q 97 = false ∨ valuation q 121 = false := by
  rw [value39, value97, value98, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (159 : Vertex) (413 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 93 = false ∨ valuation q 96 = false ∨ valuation q 121 = false := by
  rw [value93, value96, value98, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (415 : Vertex) (407 : Vertex) (411 : Vertex) (479 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 219 = true ∨ valuation q 93 = true ∨ valuation q 96 = true ∨ valuation q 97 = true ∨ valuation q 121 = true := by
  rw [value93, value96, value97, value98, value121, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (415 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(407 : Vertex), (411 : Vertex), (413 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (415 : Vertex) (159 : Vertex) [(407 : Vertex), (411 : Vertex), (413 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 219 = true ∨ valuation q 39 = true ∨ valuation q 96 = true ∨ valuation q 97 = true ∨ valuation q 121 = true := by
  rw [value39, value96, value97, value98, value121, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (415 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(159 : Vertex), (411 : Vertex), (413 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (415 : Vertex) (407 : Vertex) [(159 : Vertex), (411 : Vertex), (413 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 98 = false ∨ valuation q 219 = true ∨ valuation q 39 = true ∨ valuation q 93 = true ∨ valuation q 96 = true ∨ valuation q 121 = true := by
  rw [value39, value93, value96, value98, value121, value219]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (415 : Vertex) w → w ∈ region → w ≠ (413 : Vertex) → w ∈ [(159 : Vertex), (407 : Vertex), (411 : Vertex), (479 : Vertex)] := by decide
  have hg := other_cover q (415 : Vertex) (413 : Vertex) [(159 : Vertex), (407 : Vertex), (411 : Vertex), (479 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 220 = false ∨ valuation q 99 = true := by
  rw [value99, value220]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (448 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 40 = true ∨ valuation q 62 = true ∨ valuation q 79 = true ∨ valuation q 100 = true ∨ valuation q 101 = true ∨ valuation q 105 = true ∨ valuation q 111 = true := by
  rw [value40, value62, value79, value99, value100, value101, value105, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (448 : Vertex) w → w ∈ region → w ∈ [(192 : Vertex), (320 : Vertex), (384 : Vertex), (449 : Vertex), (450 : Vertex), (456 : Vertex), (464 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (448 : Vertex) [(192 : Vertex), (320 : Vertex), (384 : Vertex), (449 : Vertex), (450 : Vertex), (456 : Vertex), (464 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 40 = false ∨ valuation q 62 = false ∨ valuation q 79 = false := by
  rw [value40, value62, value79, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (192 : Vertex) (320 : Vertex) (384 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 40 = false ∨ valuation q 62 = false ∨ valuation q 100 = false := by
  rw [value40, value62, value99, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (192 : Vertex) (320 : Vertex) (449 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 99 = false ∨ valuation q 40 = false ∨ valuation q 62 = false ∨ valuation q 101 = false := by
  rw [value40, value62, value99, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (448 : Vertex) (192 : Vertex) (320 : Vertex) (450 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E019.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112019
