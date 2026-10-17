import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 213 = true ∨ valuation q 15 = true ∨ valuation q 73 = true ∨ valuation q 83 = true ∨ valuation q 84 = true ∨ valuation q 91 = true ∨ valuation q 122 = true := by
  rw [value15, value73, value83, value84, value85, value91, value122, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (343 : Vertex) → w ∈ [(23 : Vertex), (263 : Vertex), (277 : Vertex), (278 : Vertex), (287 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (343 : Vertex) [(23 : Vertex), (263 : Vertex), (277 : Vertex), (278 : Vertex), (287 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 213 = true ∨ valuation q 15 = true ∨ valuation q 73 = true ∨ valuation q 83 = true ∨ valuation q 84 = true ∨ valuation q 91 = true ∨ valuation q 103 = true := by
  rw [value15, value73, value83, value84, value85, value91, value103, value213]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (279 : Vertex) w → w ∈ region → w ≠ (407 : Vertex) → w ∈ [(23 : Vertex), (263 : Vertex), (277 : Vertex), (278 : Vertex), (287 : Vertex), (343 : Vertex)] := by decide
  have hg := other_cover q (279 : Vertex) (407 : Vertex) [(23 : Vertex), (263 : Vertex), (277 : Vertex), (278 : Vertex), (287 : Vertex), (343 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 214 = false ∨ valuation q 86 = true := by
  rw [value86, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (280 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 74 = true ∨ valuation q 80 = true ∨ valuation q 87 = true ∨ valuation q 88 = true ∨ valuation q 90 = true := by
  rw [value74, value80, value86, value87, value88, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ∈ [(264 : Vertex), (272 : Vertex), (281 : Vertex), (282 : Vertex), (284 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (280 : Vertex) [(264 : Vertex), (272 : Vertex), (281 : Vertex), (282 : Vertex), (284 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 74 = false ∨ valuation q 80 = false ∨ valuation q 90 = false := by
  rw [value74, value80, value86, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (280 : Vertex) (264 : Vertex) (272 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 74 = false ∨ valuation q 88 = false ∨ valuation q 90 = false := by
  rw [value74, value86, value88, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (280 : Vertex) (264 : Vertex) (282 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 80 = false ∨ valuation q 87 = false ∨ valuation q 88 = false := by
  rw [value80, value86, value87, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (280 : Vertex) (272 : Vertex) (281 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 80 = false ∨ valuation q 87 = false ∨ valuation q 90 = false := by
  rw [value80, value86, value87, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (280 : Vertex) (272 : Vertex) (281 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 88 = false ∨ valuation q 90 = false := by
  rw [value86, value87, value88, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (280 : Vertex) (281 : Vertex) (282 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 214 = true ∨ valuation q 80 = true ∨ valuation q 87 = true ∨ valuation q 88 = true ∨ valuation q 90 = true := by
  rw [value80, value86, value87, value88, value90, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (264 : Vertex) → w ∈ [(272 : Vertex), (281 : Vertex), (282 : Vertex), (284 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (264 : Vertex) [(272 : Vertex), (281 : Vertex), (282 : Vertex), (284 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 214 = true ∨ valuation q 74 = true ∨ valuation q 87 = true ∨ valuation q 88 = true ∨ valuation q 90 = true := by
  rw [value74, value86, value87, value88, value90, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (272 : Vertex) → w ∈ [(264 : Vertex), (281 : Vertex), (282 : Vertex), (284 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (272 : Vertex) [(264 : Vertex), (281 : Vertex), (282 : Vertex), (284 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 214 = true ∨ valuation q 74 = true ∨ valuation q 80 = true ∨ valuation q 88 = true ∨ valuation q 90 = true := by
  rw [value74, value80, value86, value88, value90, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (281 : Vertex) → w ∈ [(264 : Vertex), (272 : Vertex), (282 : Vertex), (284 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (281 : Vertex) [(264 : Vertex), (272 : Vertex), (282 : Vertex), (284 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 214 = true ∨ valuation q 74 = true ∨ valuation q 80 = true ∨ valuation q 87 = true ∨ valuation q 90 = true := by
  rw [value74, value80, value86, value87, value90, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (282 : Vertex) → w ∈ [(264 : Vertex), (272 : Vertex), (281 : Vertex), (284 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (282 : Vertex) [(264 : Vertex), (272 : Vertex), (281 : Vertex), (284 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 86 = false ∨ valuation q 214 = true ∨ valuation q 74 = true ∨ valuation q 80 = true ∨ valuation q 87 = true ∨ valuation q 88 = true := by
  rw [value74, value80, value86, value87, value88, value214]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (280 : Vertex) w → w ∈ region → w ≠ (284 : Vertex) → w ∈ [(264 : Vertex), (272 : Vertex), (281 : Vertex), (282 : Vertex)] := by decide
  have hg := other_cover q (280 : Vertex) (284 : Vertex) [(264 : Vertex), (272 : Vertex), (281 : Vertex), (282 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 16 = false ∨ valuation q 75 = false ∨ valuation q 86 = false := by
  rw [value16, value75, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (25 : Vertex) (265 : Vertex) (280 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 16 = false ∨ valuation q 75 = false ∨ valuation q 89 = false := by
  rw [value16, value75, value87, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (25 : Vertex) (265 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 16 = false ∨ valuation q 75 = false ∨ valuation q 104 = false := by
  rw [value16, value75, value87, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (25 : Vertex) (265 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 16 = false ∨ valuation q 75 = false ∨ valuation q 123 = false := by
  rw [value16, value75, value87, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (25 : Vertex) (265 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 16 = false ∨ valuation q 86 = false ∨ valuation q 89 = false := by
  rw [value16, value86, value87, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (25 : Vertex) (280 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 16 = false ∨ valuation q 86 = false ∨ valuation q 104 = false := by
  rw [value16, value86, value87, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (25 : Vertex) (280 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 16 = false ∨ valuation q 86 = false ∨ valuation q 123 = false := by
  rw [value16, value86, value87, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (25 : Vertex) (280 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 16 = false ∨ valuation q 89 = false ∨ valuation q 104 = false := by
  rw [value16, value87, value89, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (25 : Vertex) (283 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 16 = false ∨ valuation q 89 = false ∨ valuation q 123 = false := by
  rw [value16, value87, value89, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (25 : Vertex) (283 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 16 = false ∨ valuation q 104 = false ∨ valuation q 123 = false := by
  rw [value16, value87, value104, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (25 : Vertex) (345 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 75 = false ∨ valuation q 86 = false ∨ valuation q 89 = false := by
  rw [value75, value86, value87, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (265 : Vertex) (280 : Vertex) (283 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 75 = false ∨ valuation q 86 = false ∨ valuation q 104 = false := by
  rw [value75, value86, value87, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (265 : Vertex) (280 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 75 = false ∨ valuation q 86 = false ∨ valuation q 123 = false := by
  rw [value75, value86, value87, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (265 : Vertex) (280 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 75 = false ∨ valuation q 89 = false ∨ valuation q 104 = false := by
  rw [value75, value87, value89, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (265 : Vertex) (283 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 75 = false ∨ valuation q 89 = false ∨ valuation q 123 = false := by
  rw [value75, value87, value89, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (265 : Vertex) (283 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 75 = false ∨ valuation q 104 = false ∨ valuation q 123 = false := by
  rw [value75, value87, value104, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (265 : Vertex) (345 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 86 = false ∨ valuation q 89 = false ∨ valuation q 104 = false := by
  rw [value86, value87, value89, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (280 : Vertex) (283 : Vertex) (345 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 87 = false ∨ valuation q 86 = false ∨ valuation q 89 = false ∨ valuation q 123 = false := by
  rw [value86, value87, value89, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (281 : Vertex) (280 : Vertex) (283 : Vertex) (409 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E055.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112055
