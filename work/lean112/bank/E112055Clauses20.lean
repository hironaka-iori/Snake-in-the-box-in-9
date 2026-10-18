import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 86 = false ∨ valuation q 104 = false ∨ valuation q 123 = false := by
  rw [value86, value87, value104, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (280 : Vertex) (345 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 89 = false ∨ valuation q 104 = false ∨ valuation q 123 = false := by
  rw [value87, value89, value104, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (283 : Vertex) (345 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 215 = true ∨ valuation q 75 = true ∨ valuation q 86 = true ∨ valuation q 89 = true ∨ valuation q 104 = true ∨ valuation q 123 = true := by
  rw [value75, value86, value87, value89, value104, value123, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (281 : Vertex) w → w ∈ region → w ≠ (25 : Vertex) → w ∈ [(265 : Vertex), (280 : Vertex), (283 : Vertex), (345 : Vertex), (409 : Vertex)] := by decide
  have hg := other_cover q (281 : Vertex) (25 : Vertex) [(265 : Vertex), (280 : Vertex), (283 : Vertex), (345 : Vertex), (409 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 215 = true ∨ valuation q 16 = true ∨ valuation q 86 = true ∨ valuation q 89 = true ∨ valuation q 104 = true ∨ valuation q 123 = true := by
  rw [value16, value86, value87, value89, value104, value123, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (281 : Vertex) w → w ∈ region → w ≠ (265 : Vertex) → w ∈ [(25 : Vertex), (280 : Vertex), (283 : Vertex), (345 : Vertex), (409 : Vertex)] := by decide
  have hg := other_cover q (281 : Vertex) (265 : Vertex) [(25 : Vertex), (280 : Vertex), (283 : Vertex), (345 : Vertex), (409 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 215 = true ∨ valuation q 16 = true ∨ valuation q 75 = true ∨ valuation q 89 = true ∨ valuation q 104 = true ∨ valuation q 123 = true := by
  rw [value16, value75, value87, value89, value104, value123, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (281 : Vertex) w → w ∈ region → w ≠ (280 : Vertex) → w ∈ [(25 : Vertex), (265 : Vertex), (283 : Vertex), (345 : Vertex), (409 : Vertex)] := by decide
  have hg := other_cover q (281 : Vertex) (280 : Vertex) [(25 : Vertex), (265 : Vertex), (283 : Vertex), (345 : Vertex), (409 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 215 = true ∨ valuation q 16 = true ∨ valuation q 75 = true ∨ valuation q 86 = true ∨ valuation q 104 = true ∨ valuation q 123 = true := by
  rw [value16, value75, value86, value87, value104, value123, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (281 : Vertex) w → w ∈ region → w ≠ (283 : Vertex) → w ∈ [(25 : Vertex), (265 : Vertex), (280 : Vertex), (345 : Vertex), (409 : Vertex)] := by decide
  have hg := other_cover q (281 : Vertex) (283 : Vertex) [(25 : Vertex), (265 : Vertex), (280 : Vertex), (345 : Vertex), (409 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 215 = true ∨ valuation q 16 = true ∨ valuation q 75 = true ∨ valuation q 86 = true ∨ valuation q 89 = true ∨ valuation q 123 = true := by
  rw [value16, value75, value86, value87, value89, value123, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (281 : Vertex) w → w ∈ region → w ≠ (345 : Vertex) → w ∈ [(25 : Vertex), (265 : Vertex), (280 : Vertex), (283 : Vertex), (409 : Vertex)] := by decide
  have hg := other_cover q (281 : Vertex) (345 : Vertex) [(25 : Vertex), (265 : Vertex), (280 : Vertex), (283 : Vertex), (409 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 215 = true ∨ valuation q 16 = true ∨ valuation q 75 = true ∨ valuation q 86 = true ∨ valuation q 89 = true ∨ valuation q 104 = true := by
  rw [value16, value75, value86, value87, value89, value104, value215]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (281 : Vertex) w → w ∈ region → w ≠ (409 : Vertex) → w ∈ [(25 : Vertex), (265 : Vertex), (280 : Vertex), (283 : Vertex), (345 : Vertex)] := by decide
  have hg := other_cover q (281 : Vertex) (409 : Vertex) [(25 : Vertex), (265 : Vertex), (280 : Vertex), (283 : Vertex), (345 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 81 = false ∨ valuation q 86 = false ∨ valuation q 89 = false := by
  rw [value81, value86, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (282 : Vertex) (274 : Vertex) (280 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 216 = true ∨ valuation q 86 = true ∨ valuation q 89 = true := by
  rw [value86, value88, value89, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (282 : Vertex) w → w ∈ region → w ≠ (274 : Vertex) → w ∈ [(280 : Vertex), (283 : Vertex)] := by decide
  have hg := other_cover q (282 : Vertex) (274 : Vertex) [(280 : Vertex), (283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 216 = true ∨ valuation q 81 = true ∨ valuation q 89 = true := by
  rw [value81, value88, value89, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (282 : Vertex) w → w ∈ region → w ≠ (280 : Vertex) → w ∈ [(274 : Vertex), (283 : Vertex)] := by decide
  have hg := other_cover q (282 : Vertex) (280 : Vertex) [(274 : Vertex), (283 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 88 = false ∨ valuation q 216 = true ∨ valuation q 81 = true ∨ valuation q 86 = true := by
  rw [value81, value86, value88, value216]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (282 : Vertex) w → w ∈ region → w ≠ (283 : Vertex) → w ∈ [(274 : Vertex), (280 : Vertex)] := by decide
  have hg := other_cover q (282 : Vertex) (283 : Vertex) [(274 : Vertex), (280 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 17 = false ∨ valuation q 76 = false ∨ valuation q 87 = false := by
  rw [value17, value76, value87, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (27 : Vertex) (267 : Vertex) (281 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 17 = false ∨ valuation q 76 = false ∨ valuation q 88 = false := by
  rw [value17, value76, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (27 : Vertex) (267 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 17 = false ∨ valuation q 76 = false ∨ valuation q 91 = false := by
  rw [value17, value76, value89, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (27 : Vertex) (267 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 17 = false ∨ valuation q 76 = false ∨ valuation q 105 = false := by
  rw [value17, value76, value89, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (27 : Vertex) (267 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 17 = false ∨ valuation q 87 = false ∨ valuation q 88 = false := by
  rw [value17, value87, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (27 : Vertex) (281 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 17 = false ∨ valuation q 87 = false ∨ valuation q 91 = false := by
  rw [value17, value87, value89, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (27 : Vertex) (281 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 17 = false ∨ valuation q 87 = false ∨ valuation q 105 = false := by
  rw [value17, value87, value89, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (27 : Vertex) (281 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 17 = false ∨ valuation q 87 = false ∨ valuation q 124 = false := by
  rw [value17, value87, value89, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (27 : Vertex) (281 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 17 = false ∨ valuation q 88 = false ∨ valuation q 91 = false := by
  rw [value17, value88, value89, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (27 : Vertex) (282 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 17 = false ∨ valuation q 88 = false ∨ valuation q 105 = false := by
  rw [value17, value88, value89, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (27 : Vertex) (282 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 17 = false ∨ valuation q 88 = false ∨ valuation q 124 = false := by
  rw [value17, value88, value89, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (27 : Vertex) (282 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 17 = false ∨ valuation q 91 = false ∨ valuation q 124 = false := by
  rw [value17, value89, value91, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (27 : Vertex) (287 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 17 = false ∨ valuation q 105 = false ∨ valuation q 124 = false := by
  rw [value17, value89, value105, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (27 : Vertex) (347 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 76 = false ∨ valuation q 87 = false ∨ valuation q 88 = false := by
  rw [value76, value87, value88, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (267 : Vertex) (281 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 76 = false ∨ valuation q 87 = false ∨ valuation q 91 = false := by
  rw [value76, value87, value89, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (267 : Vertex) (281 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 76 = false ∨ valuation q 87 = false ∨ valuation q 105 = false := by
  rw [value76, value87, value89, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (267 : Vertex) (281 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 76 = false ∨ valuation q 87 = false ∨ valuation q 124 = false := by
  rw [value76, value87, value89, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (267 : Vertex) (281 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 76 = false ∨ valuation q 88 = false ∨ valuation q 91 = false := by
  rw [value76, value88, value89, value91]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (267 : Vertex) (282 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 76 = false ∨ valuation q 88 = false ∨ valuation q 105 = false := by
  rw [value76, value88, value89, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (267 : Vertex) (282 : Vertex) (347 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 89 = false ∨ valuation q 76 = false ∨ valuation q 88 = false ∨ valuation q 124 = false := by
  rw [value76, value88, value89, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (283 : Vertex) (267 : Vertex) (282 : Vertex) (411 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E055.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112055
