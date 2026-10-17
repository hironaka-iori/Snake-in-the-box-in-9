import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 81 = false ∨ valuation q 100 = false ∨ valuation q 117 = false := by
  rw [value79, value81, value100, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (272 : Vertex) (276 : Vertex) (336 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 85 = false ∨ valuation q 100 = false ∨ valuation q 117 = false := by
  rw [value79, value85, value100, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (272 : Vertex) (280 : Vertex) (336 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 206 = true ∨ valuation q 81 = true ∨ valuation q 85 = true ∨ valuation q 100 = true ∨ valuation q 117 = true := by
  rw [value79, value81, value85, value100, value117, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ≠ (274 : Vertex) → w ∈ [(276 : Vertex), (280 : Vertex), (336 : Vertex), (400 : Vertex)] := by decide
  have hg := other_cover q (272 : Vertex) (274 : Vertex) [(276 : Vertex), (280 : Vertex), (336 : Vertex), (400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 206 = true ∨ valuation q 80 = true ∨ valuation q 85 = true ∨ valuation q 100 = true ∨ valuation q 117 = true := by
  rw [value79, value80, value85, value100, value117, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ≠ (276 : Vertex) → w ∈ [(274 : Vertex), (280 : Vertex), (336 : Vertex), (400 : Vertex)] := by decide
  have hg := other_cover q (272 : Vertex) (276 : Vertex) [(274 : Vertex), (280 : Vertex), (336 : Vertex), (400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 206 = true ∨ valuation q 80 = true ∨ valuation q 81 = true ∨ valuation q 100 = true ∨ valuation q 117 = true := by
  rw [value79, value80, value81, value100, value117, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ≠ (280 : Vertex) → w ∈ [(274 : Vertex), (276 : Vertex), (336 : Vertex), (400 : Vertex)] := by decide
  have hg := other_cover q (272 : Vertex) (280 : Vertex) [(274 : Vertex), (276 : Vertex), (336 : Vertex), (400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 206 = true ∨ valuation q 80 = true ∨ valuation q 81 = true ∨ valuation q 85 = true ∨ valuation q 117 = true := by
  rw [value79, value80, value81, value85, value117, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ≠ (336 : Vertex) → w ∈ [(274 : Vertex), (276 : Vertex), (280 : Vertex), (400 : Vertex)] := by decide
  have hg := other_cover q (272 : Vertex) (336 : Vertex) [(274 : Vertex), (276 : Vertex), (280 : Vertex), (400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 79 = false ∨ valuation q 206 = true ∨ valuation q 80 = true ∨ valuation q 81 = true ∨ valuation q 85 = true ∨ valuation q 100 = true := by
  rw [value79, value80, value81, value85, value100, value206]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (272 : Vertex) w → w ∈ region → w ≠ (400 : Vertex) → w ∈ [(274 : Vertex), (276 : Vertex), (280 : Vertex), (336 : Vertex)] := by decide
  have hg := other_cover q (272 : Vertex) (400 : Vertex) [(274 : Vertex), (276 : Vertex), (280 : Vertex), (336 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 11 = false ∨ valuation q 79 = false ∨ valuation q 83 = false := by
  rw [value11, value79, value80, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (274 : Vertex) (18 : Vertex) (272 : Vertex) (278 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 11 = false ∨ valuation q 79 = false ∨ valuation q 87 = false := by
  rw [value11, value79, value80, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (274 : Vertex) (18 : Vertex) (272 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 11 = false ∨ valuation q 83 = false ∨ valuation q 87 = false := by
  rw [value11, value80, value83, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (274 : Vertex) (18 : Vertex) (278 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 79 = false ∨ valuation q 83 = false ∨ valuation q 87 = false := by
  rw [value79, value80, value83, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (274 : Vertex) (272 : Vertex) (278 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 207 = false ∨ valuation q 11 = false ∨ valuation q 87 = false := by
  rw [value11, value87, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (274 : Vertex) (18 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide)

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 80 = false ∨ valuation q 207 = true ∨ valuation q 11 = true ∨ valuation q 79 = true ∨ valuation q 83 = true := by
  rw [value11, value79, value80, value83, value207]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (274 : Vertex) w → w ∈ region → w ≠ (282 : Vertex) → w ∈ [(18 : Vertex), (272 : Vertex), (278 : Vertex)] := by decide
  have hg := other_cover q (274 : Vertex) (282 : Vertex) [(18 : Vertex), (272 : Vertex), (278 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 69 = false ∨ valuation q 79 = false ∨ valuation q 82 = false := by
  rw [value69, value79, value81, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (276 : Vertex) (260 : Vertex) (272 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 69 = false ∨ valuation q 79 = false ∨ valuation q 83 = false := by
  rw [value69, value79, value81, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (276 : Vertex) (260 : Vertex) (272 : Vertex) (278 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 69 = false ∨ valuation q 79 = false ∨ valuation q 89 = false := by
  rw [value69, value79, value81, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (276 : Vertex) (260 : Vertex) (272 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 69 = false ∨ valuation q 82 = false ∨ valuation q 83 = false := by
  rw [value69, value81, value82, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (276 : Vertex) (260 : Vertex) (277 : Vertex) (278 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 69 = false ∨ valuation q 82 = false ∨ valuation q 89 = false := by
  rw [value69, value81, value82, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (276 : Vertex) (260 : Vertex) (277 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 69 = false ∨ valuation q 83 = false ∨ valuation q 89 = false := by
  rw [value69, value81, value83, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (276 : Vertex) (260 : Vertex) (278 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 79 = false ∨ valuation q 82 = false ∨ valuation q 83 = false := by
  rw [value79, value81, value82, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (276 : Vertex) (272 : Vertex) (277 : Vertex) (278 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 79 = false ∨ valuation q 82 = false ∨ valuation q 89 = false := by
  rw [value79, value81, value82, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (276 : Vertex) (272 : Vertex) (277 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 79 = false ∨ valuation q 83 = false ∨ valuation q 89 = false := by
  rw [value79, value81, value83, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (276 : Vertex) (272 : Vertex) (278 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 82 = false ∨ valuation q 83 = false ∨ valuation q 89 = false := by
  rw [value81, value82, value83, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (276 : Vertex) (277 : Vertex) (278 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 208 = false ∨ valuation q 69 = false ∨ valuation q 79 = false := by
  rw [value69, value79, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (276 : Vertex) (260 : Vertex) (272 : Vertex) (by decide) (by decide) (by decide)

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 208 = false ∨ valuation q 69 = false ∨ valuation q 82 = false := by
  rw [value69, value82, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (276 : Vertex) (260 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide)

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 208 = true ∨ valuation q 79 = true ∨ valuation q 82 = true ∨ valuation q 83 = true ∨ valuation q 89 = true := by
  rw [value79, value81, value82, value83, value89, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (260 : Vertex) → w ∈ [(272 : Vertex), (277 : Vertex), (278 : Vertex), (284 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (260 : Vertex) [(272 : Vertex), (277 : Vertex), (278 : Vertex), (284 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 81 = false ∨ valuation q 208 = true ∨ valuation q 69 = true ∨ valuation q 79 = true ∨ valuation q 83 = true ∨ valuation q 89 = true := by
  rw [value69, value79, value81, value83, value89, value208]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (276 : Vertex) w → w ∈ region → w ≠ (277 : Vertex) → w ∈ [(260 : Vertex), (272 : Vertex), (278 : Vertex), (284 : Vertex)] := by decide
  have hg := other_cover q (276 : Vertex) (277 : Vertex) [(260 : Vertex), (272 : Vertex), (278 : Vertex), (284 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 13 = false ∨ valuation q 70 = false ∨ valuation q 84 = false := by
  rw [value13, value70, value82, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (277 : Vertex) (21 : Vertex) (261 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 13 = false ∨ valuation q 81 = false ∨ valuation q 84 = false := by
  rw [value13, value81, value82, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (277 : Vertex) (21 : Vertex) (276 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 209 = true ∨ valuation q 70 = true ∨ valuation q 81 = true ∨ valuation q 84 = true := by
  rw [value70, value81, value82, value84, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (277 : Vertex) w → w ∈ region → w ≠ (21 : Vertex) → w ∈ [(261 : Vertex), (276 : Vertex), (279 : Vertex)] := by decide
  have hg := other_cover q (277 : Vertex) (21 : Vertex) [(261 : Vertex), (276 : Vertex), (279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 209 = true ∨ valuation q 13 = true ∨ valuation q 81 = true ∨ valuation q 84 = true := by
  rw [value13, value81, value82, value84, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (277 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(21 : Vertex), (276 : Vertex), (279 : Vertex)] := by decide
  have hg := other_cover q (277 : Vertex) (261 : Vertex) [(21 : Vertex), (276 : Vertex), (279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 209 = true ∨ valuation q 13 = true ∨ valuation q 70 = true ∨ valuation q 84 = true := by
  rw [value13, value70, value82, value84, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (277 : Vertex) w → w ∈ region → w ≠ (276 : Vertex) → w ∈ [(21 : Vertex), (261 : Vertex), (279 : Vertex)] := by decide
  have hg := other_cover q (277 : Vertex) (276 : Vertex) [(21 : Vertex), (261 : Vertex), (279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block19 (q : Snake 81) (h : Conditions q) : B112E057.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112057
