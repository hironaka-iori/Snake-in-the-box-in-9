import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 6 = false ∨ valuation q 28 = false ∨ valuation q 37 = false := by
  rw [value6, value25, value28, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (41 : Vertex) (109 : Vertex) (121 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 6 = false ∨ valuation q 28 = false ∨ valuation q 63 = false := by
  rw [value6, value25, value28, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (41 : Vertex) (109 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 6 = false ∨ valuation q 28 = false ∨ valuation q 98 = false := by
  rw [value6, value25, value28, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (41 : Vertex) (109 : Vertex) (361 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 6 = false ∨ valuation q 37 = false ∨ valuation q 63 = false := by
  rw [value6, value25, value37, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (41 : Vertex) (121 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 6 = false ∨ valuation q 37 = false ∨ valuation q 98 = false := by
  rw [value6, value25, value37, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (41 : Vertex) (121 : Vertex) (361 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 6 = false ∨ valuation q 63 = false ∨ valuation q 98 = false := by
  rw [value6, value25, value63, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (41 : Vertex) (233 : Vertex) (361 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 21 = false ∨ valuation q 26 = false ∨ valuation q 28 = false := by
  rw [value21, value25, value26, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (97 : Vertex) (107 : Vertex) (109 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 21 = false ∨ valuation q 26 = false ∨ valuation q 37 = false := by
  rw [value21, value25, value26, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (97 : Vertex) (107 : Vertex) (121 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 21 = false ∨ valuation q 26 = false ∨ valuation q 63 = false := by
  rw [value21, value25, value26, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (97 : Vertex) (107 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 21 = false ∨ valuation q 26 = false ∨ valuation q 98 = false := by
  rw [value21, value25, value26, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (97 : Vertex) (107 : Vertex) (361 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 21 = false ∨ valuation q 28 = false ∨ valuation q 37 = false := by
  rw [value21, value25, value28, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (97 : Vertex) (109 : Vertex) (121 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 21 = false ∨ valuation q 28 = false ∨ valuation q 63 = false := by
  rw [value21, value25, value28, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (97 : Vertex) (109 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 21 = false ∨ valuation q 28 = false ∨ valuation q 98 = false := by
  rw [value21, value25, value28, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (97 : Vertex) (109 : Vertex) (361 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 21 = false ∨ valuation q 37 = false ∨ valuation q 63 = false := by
  rw [value21, value25, value37, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (97 : Vertex) (121 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 21 = false ∨ valuation q 37 = false ∨ valuation q 98 = false := by
  rw [value21, value25, value37, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (97 : Vertex) (121 : Vertex) (361 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 21 = false ∨ valuation q 63 = false ∨ valuation q 98 = false := by
  rw [value21, value25, value63, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (97 : Vertex) (233 : Vertex) (361 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 26 = false ∨ valuation q 28 = false ∨ valuation q 37 = false := by
  rw [value25, value26, value28, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (107 : Vertex) (109 : Vertex) (121 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 26 = false ∨ valuation q 28 = false ∨ valuation q 63 = false := by
  rw [value25, value26, value28, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (107 : Vertex) (109 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 26 = false ∨ valuation q 28 = false ∨ valuation q 98 = false := by
  rw [value25, value26, value28, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (107 : Vertex) (109 : Vertex) (361 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 26 = false ∨ valuation q 37 = false ∨ valuation q 63 = false := by
  rw [value25, value26, value37, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (107 : Vertex) (121 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 26 = false ∨ valuation q 37 = false ∨ valuation q 98 = false := by
  rw [value25, value26, value37, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (107 : Vertex) (121 : Vertex) (361 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 26 = false ∨ valuation q 63 = false ∨ valuation q 98 = false := by
  rw [value25, value26, value63, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (107 : Vertex) (233 : Vertex) (361 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 28 = false ∨ valuation q 37 = false ∨ valuation q 63 = false := by
  rw [value25, value28, value37, value63]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (109 : Vertex) (121 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 28 = false ∨ valuation q 37 = false ∨ valuation q 98 = false := by
  rw [value25, value28, value37, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (109 : Vertex) (121 : Vertex) (361 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 28 = false ∨ valuation q 63 = false ∨ valuation q 98 = false := by
  rw [value25, value28, value63, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (109 : Vertex) (233 : Vertex) (361 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 37 = false ∨ valuation q 63 = false ∨ valuation q 98 = false := by
  rw [value25, value37, value63, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (105 : Vertex) (121 : Vertex) (233 : Vertex) (361 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 8 = false ∨ valuation q 23 = false ∨ valuation q 25 = false := by
  rw [value8, value23, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (107 : Vertex) (43 : Vertex) (99 : Vertex) (105 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 8 = false ∨ valuation q 23 = false ∨ valuation q 29 = false := by
  rw [value8, value23, value26, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (107 : Vertex) (43 : Vertex) (99 : Vertex) (111 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 8 = false ∨ valuation q 23 = false ∨ valuation q 65 = false := by
  rw [value8, value23, value26, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (107 : Vertex) (43 : Vertex) (99 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 8 = false ∨ valuation q 23 = false ∨ valuation q 100 = false := by
  rw [value8, value23, value26, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (107 : Vertex) (43 : Vertex) (99 : Vertex) (363 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 8 = false ∨ valuation q 25 = false ∨ valuation q 29 = false := by
  rw [value8, value25, value26, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (107 : Vertex) (43 : Vertex) (105 : Vertex) (111 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 8 = false ∨ valuation q 25 = false ∨ valuation q 65 = false := by
  rw [value8, value25, value26, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (107 : Vertex) (43 : Vertex) (105 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block4 (q : Snake 81) (h : Conditions q) : B112E040.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112040
