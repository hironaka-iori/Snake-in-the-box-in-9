import E112081Semantics
import B112E081Inputs
namespace Snake9.Regrowth.E112081
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 3 = false ∨ valuation q 17 = false ∨ valuation q 34 = false := by
  rw [value3, value17, value19, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (6 : Vertex) (130 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 3 = false ∨ valuation q 17 = false ∨ valuation q 89 = false := by
  rw [value3, value17, value19, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (6 : Vertex) (130 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 3 = false ∨ valuation q 18 = false ∨ valuation q 20 = false := by
  rw [value3, value18, value19, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (6 : Vertex) (132 : Vertex) (135 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 3 = false ∨ valuation q 18 = false ∨ valuation q 25 = false := by
  rw [value3, value18, value19, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (6 : Vertex) (132 : Vertex) (142 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 3 = false ∨ valuation q 18 = false ∨ valuation q 34 = false := by
  rw [value3, value18, value19, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (6 : Vertex) (132 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 3 = false ∨ valuation q 18 = false ∨ valuation q 89 = false := by
  rw [value3, value18, value19, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (6 : Vertex) (132 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 3 = false ∨ valuation q 20 = false ∨ valuation q 25 = false := by
  rw [value3, value19, value20, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (6 : Vertex) (135 : Vertex) (142 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 3 = false ∨ valuation q 20 = false ∨ valuation q 34 = false := by
  rw [value3, value19, value20, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (6 : Vertex) (135 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 3 = false ∨ valuation q 20 = false ∨ valuation q 89 = false := by
  rw [value3, value19, value20, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (6 : Vertex) (135 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 3 = false ∨ valuation q 25 = false ∨ valuation q 34 = false := by
  rw [value3, value19, value25, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (6 : Vertex) (142 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 3 = false ∨ valuation q 25 = false ∨ valuation q 89 = false := by
  rw [value3, value19, value25, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (6 : Vertex) (142 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 3 = false ∨ valuation q 34 = false ∨ valuation q 89 = false := by
  rw [value3, value19, value34, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (6 : Vertex) (198 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 20 = false := by
  rw [value17, value18, value19, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (130 : Vertex) (132 : Vertex) (135 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 25 = false := by
  rw [value17, value18, value19, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (130 : Vertex) (132 : Vertex) (142 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 34 = false := by
  rw [value17, value18, value19, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (130 : Vertex) (132 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 89 = false := by
  rw [value17, value18, value19, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (130 : Vertex) (132 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 17 = false ∨ valuation q 20 = false ∨ valuation q 25 = false := by
  rw [value17, value19, value20, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (130 : Vertex) (135 : Vertex) (142 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 17 = false ∨ valuation q 20 = false ∨ valuation q 34 = false := by
  rw [value17, value19, value20, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (130 : Vertex) (135 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 17 = false ∨ valuation q 20 = false ∨ valuation q 89 = false := by
  rw [value17, value19, value20, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (130 : Vertex) (135 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 17 = false ∨ valuation q 25 = false ∨ valuation q 34 = false := by
  rw [value17, value19, value25, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (130 : Vertex) (142 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 17 = false ∨ valuation q 25 = false ∨ valuation q 89 = false := by
  rw [value17, value19, value25, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (130 : Vertex) (142 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 17 = false ∨ valuation q 34 = false ∨ valuation q 89 = false := by
  rw [value17, value19, value34, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (130 : Vertex) (198 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 18 = false ∨ valuation q 20 = false ∨ valuation q 25 = false := by
  rw [value18, value19, value20, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (132 : Vertex) (135 : Vertex) (142 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 18 = false ∨ valuation q 20 = false ∨ valuation q 34 = false := by
  rw [value18, value19, value20, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (132 : Vertex) (135 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 18 = false ∨ valuation q 20 = false ∨ valuation q 89 = false := by
  rw [value18, value19, value20, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (132 : Vertex) (135 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 18 = false ∨ valuation q 25 = false ∨ valuation q 34 = false := by
  rw [value18, value19, value25, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (132 : Vertex) (142 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 18 = false ∨ valuation q 25 = false ∨ valuation q 89 = false := by
  rw [value18, value19, value25, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (132 : Vertex) (142 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 18 = false ∨ valuation q 34 = false ∨ valuation q 89 = false := by
  rw [value18, value19, value34, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (132 : Vertex) (198 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 20 = false ∨ valuation q 25 = false ∨ valuation q 34 = false := by
  rw [value19, value20, value25, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (135 : Vertex) (142 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 20 = false ∨ valuation q 25 = false ∨ valuation q 89 = false := by
  rw [value19, value20, value25, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (135 : Vertex) (142 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 20 = false ∨ valuation q 34 = false ∨ valuation q 89 = false := by
  rw [value19, value20, value34, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (135 : Vertex) (198 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 25 = false ∨ valuation q 34 = false ∨ valuation q 89 = false := by
  rw [value19, value25, value34, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (142 : Vertex) (198 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block2 (q : Snake 81) (h : Conditions q) : B112E081.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112081
