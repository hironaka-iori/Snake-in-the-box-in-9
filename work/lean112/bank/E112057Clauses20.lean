import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 82 = false ∨ valuation q 209 = true ∨ valuation q 13 = true ∨ valuation q 70 = true ∨ valuation q 81 = true := by
  rw [value13, value70, value81, value82, value209]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (277 : Vertex) w → w ∈ region → w ≠ (279 : Vertex) → w ∈ [(21 : Vertex), (261 : Vertex), (276 : Vertex)] := by decide
  have hg := other_cover q (277 : Vertex) (279 : Vertex) [(21 : Vertex), (261 : Vertex), (276 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 14 = false ∨ valuation q 71 = false ∨ valuation q 102 = false := by
  rw [value14, value71, value83, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (22 : Vertex) (262 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 14 = false ∨ valuation q 71 = false ∨ valuation q 120 = false := by
  rw [value14, value71, value83, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (22 : Vertex) (262 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 14 = false ∨ valuation q 80 = false ∨ valuation q 81 = false := by
  rw [value14, value80, value81, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (22 : Vertex) (274 : Vertex) (276 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 14 = false ∨ valuation q 102 = false ∨ valuation q 120 = false := by
  rw [value14, value83, value102, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (22 : Vertex) (342 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 71 = false ∨ valuation q 80 = false ∨ valuation q 81 = false := by
  rw [value71, value80, value81, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (262 : Vertex) (274 : Vertex) (276 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 71 = false ∨ valuation q 80 = false ∨ valuation q 84 = false := by
  rw [value71, value80, value83, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (262 : Vertex) (274 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 71 = false ∨ valuation q 80 = false ∨ valuation q 102 = false := by
  rw [value71, value80, value83, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (262 : Vertex) (274 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 71 = false ∨ valuation q 80 = false ∨ valuation q 120 = false := by
  rw [value71, value80, value83, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (262 : Vertex) (274 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 71 = false ∨ valuation q 81 = false ∨ valuation q 102 = false := by
  rw [value71, value81, value83, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (262 : Vertex) (276 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 71 = false ∨ valuation q 81 = false ∨ valuation q 120 = false := by
  rw [value71, value81, value83, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (262 : Vertex) (276 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 71 = false ∨ valuation q 102 = false ∨ valuation q 120 = false := by
  rw [value71, value83, value102, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (262 : Vertex) (342 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 80 = false ∨ valuation q 81 = false ∨ valuation q 84 = false := by
  rw [value80, value81, value83, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (274 : Vertex) (276 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 80 = false ∨ valuation q 81 = false ∨ valuation q 102 = false := by
  rw [value80, value81, value83, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (274 : Vertex) (276 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 80 = false ∨ valuation q 81 = false ∨ valuation q 120 = false := by
  rw [value80, value81, value83, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (274 : Vertex) (276 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 80 = false ∨ valuation q 102 = false ∨ valuation q 120 = false := by
  rw [value80, value83, value102, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (274 : Vertex) (342 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 81 = false ∨ valuation q 102 = false ∨ valuation q 120 = false := by
  rw [value81, value83, value102, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (276 : Vertex) (342 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 210 = true ∨ valuation q 14 = true ∨ valuation q 71 = true ∨ valuation q 80 = true ∨ valuation q 81 = true ∨ valuation q 84 = true ∨ valuation q 120 = true := by
  rw [value14, value71, value80, value81, value83, value84, value120, value210]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (278 : Vertex) w → w ∈ region → w ≠ (342 : Vertex) → w ∈ [(22 : Vertex), (262 : Vertex), (274 : Vertex), (276 : Vertex), (279 : Vertex), (406 : Vertex)] := by decide
  have hg := other_cover q (278 : Vertex) (342 : Vertex) [(22 : Vertex), (262 : Vertex), (274 : Vertex), (276 : Vertex), (279 : Vertex), (406 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 211 = false ∨ valuation q 84 = true := by
  rw [value84, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (279 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 15 = false ∨ valuation q 72 = false ∨ valuation q 82 = false := by
  rw [value15, value72, value82, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (23 : Vertex) (263 : Vertex) (277 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 15 = false ∨ valuation q 72 = false ∨ valuation q 90 = false := by
  rw [value15, value72, value84, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (23 : Vertex) (263 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 15 = false ∨ valuation q 72 = false ∨ valuation q 103 = false := by
  rw [value15, value72, value84, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (23 : Vertex) (263 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 15 = false ∨ valuation q 72 = false ∨ valuation q 121 = false := by
  rw [value15, value72, value84, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (23 : Vertex) (263 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 15 = false ∨ valuation q 82 = false ∨ valuation q 83 = false := by
  rw [value15, value82, value83, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (23 : Vertex) (277 : Vertex) (278 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 15 = false ∨ valuation q 82 = false ∨ valuation q 90 = false := by
  rw [value15, value82, value84, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (23 : Vertex) (277 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 15 = false ∨ valuation q 82 = false ∨ valuation q 103 = false := by
  rw [value15, value82, value84, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (23 : Vertex) (277 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 15 = false ∨ valuation q 82 = false ∨ valuation q 121 = false := by
  rw [value15, value82, value84, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (23 : Vertex) (277 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 15 = false ∨ valuation q 83 = false ∨ valuation q 90 = false := by
  rw [value15, value83, value84, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (23 : Vertex) (278 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 15 = false ∨ valuation q 83 = false ∨ valuation q 103 = false := by
  rw [value15, value83, value84, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (23 : Vertex) (278 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 15 = false ∨ valuation q 83 = false ∨ valuation q 121 = false := by
  rw [value15, value83, value84, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (23 : Vertex) (278 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 15 = false ∨ valuation q 90 = false ∨ valuation q 103 = false := by
  rw [value15, value84, value90, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (23 : Vertex) (287 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 15 = false ∨ valuation q 90 = false ∨ valuation q 121 = false := by
  rw [value15, value84, value90, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (23 : Vertex) (287 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E057.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112057
