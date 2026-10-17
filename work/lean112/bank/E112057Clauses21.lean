import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 15 = false ∨ valuation q 103 = false ∨ valuation q 121 = false := by
  rw [value15, value84, value103, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (23 : Vertex) (343 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 72 = false ∨ valuation q 82 = false ∨ valuation q 83 = false := by
  rw [value72, value82, value83, value84]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (263 : Vertex) (277 : Vertex) (278 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 72 = false ∨ valuation q 82 = false ∨ valuation q 90 = false := by
  rw [value72, value82, value84, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (263 : Vertex) (277 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 72 = false ∨ valuation q 82 = false ∨ valuation q 103 = false := by
  rw [value72, value82, value84, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (263 : Vertex) (277 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 72 = false ∨ valuation q 82 = false ∨ valuation q 121 = false := by
  rw [value72, value82, value84, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (263 : Vertex) (277 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 72 = false ∨ valuation q 83 = false ∨ valuation q 90 = false := by
  rw [value72, value83, value84, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (263 : Vertex) (278 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 72 = false ∨ valuation q 83 = false ∨ valuation q 103 = false := by
  rw [value72, value83, value84, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (263 : Vertex) (278 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 72 = false ∨ valuation q 83 = false ∨ valuation q 121 = false := by
  rw [value72, value83, value84, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (263 : Vertex) (278 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 72 = false ∨ valuation q 90 = false ∨ valuation q 103 = false := by
  rw [value72, value84, value90, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (263 : Vertex) (287 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 72 = false ∨ valuation q 90 = false ∨ valuation q 121 = false := by
  rw [value72, value84, value90, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (263 : Vertex) (287 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 72 = false ∨ valuation q 103 = false ∨ valuation q 121 = false := by
  rw [value72, value84, value103, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (263 : Vertex) (343 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 82 = false ∨ valuation q 83 = false ∨ valuation q 90 = false := by
  rw [value82, value83, value84, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (277 : Vertex) (278 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 82 = false ∨ valuation q 83 = false ∨ valuation q 103 = false := by
  rw [value82, value83, value84, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (277 : Vertex) (278 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 82 = false ∨ valuation q 83 = false ∨ valuation q 121 = false := by
  rw [value82, value83, value84, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (277 : Vertex) (278 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 82 = false ∨ valuation q 90 = false ∨ valuation q 103 = false := by
  rw [value82, value84, value90, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (277 : Vertex) (287 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 82 = false ∨ valuation q 90 = false ∨ valuation q 121 = false := by
  rw [value82, value84, value90, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (277 : Vertex) (287 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 82 = false ∨ valuation q 103 = false ∨ valuation q 121 = false := by
  rw [value82, value84, value103, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (277 : Vertex) (343 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 83 = false ∨ valuation q 90 = false ∨ valuation q 103 = false := by
  rw [value83, value84, value90, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (278 : Vertex) (287 : Vertex) (343 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 83 = false ∨ valuation q 90 = false ∨ valuation q 121 = false := by
  rw [value83, value84, value90, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (278 : Vertex) (287 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 83 = false ∨ valuation q 103 = false ∨ valuation q 121 = false := by
  rw [value83, value84, value103, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (278 : Vertex) (343 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 84 = false ∨ valuation q 90 = false ∨ valuation q 103 = false ∨ valuation q 121 = false := by
  rw [value84, value90, value103, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (279 : Vertex) (287 : Vertex) (343 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 73 = false ∨ valuation q 79 = false ∨ valuation q 86 = false := by
  rw [value73, value79, value85, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (280 : Vertex) (264 : Vertex) (272 : Vertex) (281 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 73 = false ∨ valuation q 79 = false ∨ valuation q 87 = false := by
  rw [value73, value79, value85, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (280 : Vertex) (264 : Vertex) (272 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 73 = false ∨ valuation q 79 = false ∨ valuation q 89 = false := by
  rw [value73, value79, value85, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (280 : Vertex) (264 : Vertex) (272 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 73 = false ∨ valuation q 86 = false ∨ valuation q 87 = false := by
  rw [value73, value85, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (280 : Vertex) (264 : Vertex) (281 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 73 = false ∨ valuation q 86 = false ∨ valuation q 89 = false := by
  rw [value73, value85, value86, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (280 : Vertex) (264 : Vertex) (281 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 73 = false ∨ valuation q 87 = false ∨ valuation q 89 = false := by
  rw [value73, value85, value87, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (280 : Vertex) (264 : Vertex) (282 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 79 = false ∨ valuation q 86 = false ∨ valuation q 87 = false := by
  rw [value79, value85, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (280 : Vertex) (272 : Vertex) (281 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 79 = false ∨ valuation q 86 = false ∨ valuation q 89 = false := by
  rw [value79, value85, value86, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (280 : Vertex) (272 : Vertex) (281 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 79 = false ∨ valuation q 87 = false ∨ valuation q 89 = false := by
  rw [value79, value85, value87, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (280 : Vertex) (272 : Vertex) (282 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 85 = false ∨ valuation q 86 = false ∨ valuation q 87 = false ∨ valuation q 89 = false := by
  rw [value85, value86, value87, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (280 : Vertex) (281 : Vertex) (282 : Vertex) (284 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 212 = false ∨ valuation q 73 = false ∨ valuation q 87 = false := by
  rw [value73, value87, value212]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (280 : Vertex) (264 : Vertex) (282 : Vertex) (by decide) (by decide) (by decide)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E057.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112057
