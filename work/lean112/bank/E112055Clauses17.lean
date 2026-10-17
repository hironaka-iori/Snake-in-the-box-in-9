import E112055Semantics
import B112E055Inputs
namespace Snake9.Regrowth.E112055
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 13 = false ∨ valuation q 71 = false ∨ valuation q 82 = false := by
  rw [value13, value71, value82, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (277 : Vertex) (21 : Vertex) (261 : Vertex) (276 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 13 = false ∨ valuation q 71 = false ∨ valuation q 85 = false := by
  rw [value13, value71, value83, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (277 : Vertex) (21 : Vertex) (261 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 13 = false ∨ valuation q 82 = false ∨ valuation q 85 = false := by
  rw [value13, value82, value83, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (277 : Vertex) (21 : Vertex) (276 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 71 = false ∨ valuation q 82 = false ∨ valuation q 85 = false := by
  rw [value71, value82, value83, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (277 : Vertex) (261 : Vertex) (276 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 83 = false ∨ valuation q 211 = true ∨ valuation q 13 = true ∨ valuation q 71 = true ∨ valuation q 85 = true := by
  rw [value13, value71, value83, value85, value211]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (277 : Vertex) w → w ∈ region → w ≠ (276 : Vertex) → w ∈ [(21 : Vertex), (261 : Vertex), (279 : Vertex)] := by decide
  have hg := other_cover q (277 : Vertex) (276 : Vertex) [(21 : Vertex), (261 : Vertex), (279 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 14 = false ∨ valuation q 72 = false ∨ valuation q 81 = false := by
  rw [value14, value72, value81, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (22 : Vertex) (262 : Vertex) (274 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 14 = false ∨ valuation q 72 = false ∨ valuation q 82 = false := by
  rw [value14, value72, value82, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (22 : Vertex) (262 : Vertex) (276 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 14 = false ∨ valuation q 72 = false ∨ valuation q 85 = false := by
  rw [value14, value72, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (22 : Vertex) (262 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 14 = false ∨ valuation q 72 = false ∨ valuation q 102 = false := by
  rw [value14, value72, value84, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (22 : Vertex) (262 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 14 = false ∨ valuation q 72 = false ∨ valuation q 121 = false := by
  rw [value14, value72, value84, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (22 : Vertex) (262 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 14 = false ∨ valuation q 81 = false ∨ valuation q 82 = false := by
  rw [value14, value81, value82, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (22 : Vertex) (274 : Vertex) (276 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 14 = false ∨ valuation q 81 = false ∨ valuation q 85 = false := by
  rw [value14, value81, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (22 : Vertex) (274 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 14 = false ∨ valuation q 81 = false ∨ valuation q 102 = false := by
  rw [value14, value81, value84, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (22 : Vertex) (274 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 14 = false ∨ valuation q 81 = false ∨ valuation q 121 = false := by
  rw [value14, value81, value84, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (22 : Vertex) (274 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 14 = false ∨ valuation q 82 = false ∨ valuation q 85 = false := by
  rw [value14, value82, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (22 : Vertex) (276 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 14 = false ∨ valuation q 82 = false ∨ valuation q 102 = false := by
  rw [value14, value82, value84, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (22 : Vertex) (276 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 14 = false ∨ valuation q 82 = false ∨ valuation q 121 = false := by
  rw [value14, value82, value84, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (22 : Vertex) (276 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 14 = false ∨ valuation q 85 = false ∨ valuation q 102 = false := by
  rw [value14, value84, value85, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (22 : Vertex) (279 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 14 = false ∨ valuation q 85 = false ∨ valuation q 121 = false := by
  rw [value14, value84, value85, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (22 : Vertex) (279 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 14 = false ∨ valuation q 102 = false ∨ valuation q 121 = false := by
  rw [value14, value84, value102, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (22 : Vertex) (342 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 72 = false ∨ valuation q 81 = false ∨ valuation q 82 = false := by
  rw [value72, value81, value82, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (262 : Vertex) (274 : Vertex) (276 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 72 = false ∨ valuation q 81 = false ∨ valuation q 85 = false := by
  rw [value72, value81, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (262 : Vertex) (274 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 72 = false ∨ valuation q 81 = false ∨ valuation q 102 = false := by
  rw [value72, value81, value84, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (262 : Vertex) (274 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 72 = false ∨ valuation q 81 = false ∨ valuation q 121 = false := by
  rw [value72, value81, value84, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (262 : Vertex) (274 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 72 = false ∨ valuation q 82 = false ∨ valuation q 85 = false := by
  rw [value72, value82, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (262 : Vertex) (276 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 72 = false ∨ valuation q 82 = false ∨ valuation q 102 = false := by
  rw [value72, value82, value84, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (262 : Vertex) (276 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 72 = false ∨ valuation q 82 = false ∨ valuation q 121 = false := by
  rw [value72, value82, value84, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (262 : Vertex) (276 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 72 = false ∨ valuation q 85 = false ∨ valuation q 102 = false := by
  rw [value72, value84, value85, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (262 : Vertex) (279 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 72 = false ∨ valuation q 85 = false ∨ valuation q 121 = false := by
  rw [value72, value84, value85, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (262 : Vertex) (279 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 72 = false ∨ valuation q 102 = false ∨ valuation q 121 = false := by
  rw [value72, value84, value102, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (262 : Vertex) (342 : Vertex) (406 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 81 = false ∨ valuation q 82 = false ∨ valuation q 85 = false := by
  rw [value81, value82, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (274 : Vertex) (276 : Vertex) (279 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 81 = false ∨ valuation q 82 = false ∨ valuation q 102 = false := by
  rw [value81, value82, value84, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (278 : Vertex) (274 : Vertex) (276 : Vertex) (342 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E055.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112055
