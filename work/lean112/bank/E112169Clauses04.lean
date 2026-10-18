import E112169Semantics
import B112E169Inputs
namespace Snake9.Regrowth.E112169
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 28 = false ∨ valuation q 29 = false ∨ valuation q 98 = false := by
  rw [value28, value29, value30, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (189 : Vertex) (190 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 28 = false ∨ valuation q 50 = false ∨ valuation q 98 = false := by
  rw [value28, value30, value50, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (191 : Vertex) (189 : Vertex) (255 : Vertex) (447 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 7 = false ∨ valuation q 11 = false ∨ valuation q 37 = false := by
  rw [value7, value11, value31, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (224 : Vertex) (96 : Vertex) (160 : Vertex) (232 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 7 = false ∨ valuation q 11 = false ∨ valuation q 99 = false := by
  rw [value7, value11, value31, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (224 : Vertex) (96 : Vertex) (160 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 7 = false ∨ valuation q 33 = false ∨ valuation q 34 = false := by
  rw [value7, value31, value33, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (224 : Vertex) (96 : Vertex) (226 : Vertex) (228 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 7 = false ∨ valuation q 34 = false ∨ valuation q 37 = false := by
  rw [value7, value31, value34, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (224 : Vertex) (96 : Vertex) (228 : Vertex) (232 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 7 = false ∨ valuation q 34 = false ∨ valuation q 99 = false := by
  rw [value7, value31, value34, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (224 : Vertex) (96 : Vertex) (228 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 7 = false ∨ valuation q 37 = false ∨ valuation q 99 = false := by
  rw [value7, value31, value37, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (224 : Vertex) (96 : Vertex) (232 : Vertex) (480 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 8 = false ∨ valuation q 12 = false ∨ valuation q 31 = false := by
  rw [value8, value12, value31, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (225 : Vertex) (97 : Vertex) (161 : Vertex) (224 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 8 = false ∨ valuation q 12 = false ∨ valuation q 35 = false := by
  rw [value8, value12, value32, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (225 : Vertex) (97 : Vertex) (161 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 8 = false ∨ valuation q 12 = false ∨ valuation q 100 = false := by
  rw [value8, value12, value32, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (225 : Vertex) (97 : Vertex) (161 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 8 = false ∨ valuation q 31 = false ∨ valuation q 35 = false := by
  rw [value8, value31, value32, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (225 : Vertex) (97 : Vertex) (224 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 8 = false ∨ valuation q 31 = false ∨ valuation q 100 = false := by
  rw [value8, value31, value32, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (225 : Vertex) (97 : Vertex) (224 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 8 = false ∨ valuation q 35 = false ∨ valuation q 100 = false := by
  rw [value8, value32, value35, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (225 : Vertex) (97 : Vertex) (229 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 12 = false ∨ valuation q 31 = false ∨ valuation q 35 = false := by
  rw [value12, value31, value32, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (225 : Vertex) (161 : Vertex) (224 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 12 = false ∨ valuation q 31 = false ∨ valuation q 42 = false := by
  rw [value12, value31, value32, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (225 : Vertex) (161 : Vertex) (224 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 12 = false ∨ valuation q 35 = false ∨ valuation q 42 = false := by
  rw [value12, value32, value35, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (225 : Vertex) (161 : Vertex) (229 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 12 = false ∨ valuation q 42 = false ∨ valuation q 100 = false := by
  rw [value12, value32, value42, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (225 : Vertex) (161 : Vertex) (241 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 31 = false ∨ valuation q 35 = false ∨ valuation q 42 = false := by
  rw [value31, value32, value35, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (225 : Vertex) (224 : Vertex) (229 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 35 = false ∨ valuation q 42 = false ∨ valuation q 100 = false := by
  rw [value32, value35, value42, value100]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (225 : Vertex) (229 : Vertex) (241 : Vertex) (481 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 148 = true ∨ valuation q 12 = true ∨ valuation q 31 = true ∨ valuation q 35 = true ∨ valuation q 42 = true ∨ valuation q 100 = true := by
  rw [value12, value31, value32, value35, value42, value100, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (225 : Vertex) w → w ∈ region → w ≠ (97 : Vertex) → w ∈ [(161 : Vertex), (224 : Vertex), (229 : Vertex), (241 : Vertex), (481 : Vertex)] := by decide
  have hg := other_cover q (225 : Vertex) (97 : Vertex) [(161 : Vertex), (224 : Vertex), (229 : Vertex), (241 : Vertex), (481 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 13 = false ∨ valuation q 31 = false ∨ valuation q 36 = false := by
  rw [value13, value31, value33, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (162 : Vertex) (224 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 13 = false ∨ valuation q 31 = false ∨ valuation q 38 = false := by
  rw [value13, value31, value33, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (162 : Vertex) (224 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 13 = false ∨ valuation q 36 = false ∨ valuation q 38 = false := by
  rw [value13, value33, value36, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (162 : Vertex) (230 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 31 = false ∨ valuation q 36 = false ∨ valuation q 38 = false := by
  rw [value31, value33, value36, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (226 : Vertex) (224 : Vertex) (230 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 31 = false ∨ valuation q 35 = false ∨ valuation q 36 = false := by
  rw [value31, value34, value35, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (224 : Vertex) (229 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 31 = false ∨ valuation q 35 = false ∨ valuation q 40 = false := by
  rw [value31, value34, value35, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (224 : Vertex) (229 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 31 = false ∨ valuation q 35 = false ∨ valuation q 43 = false := by
  rw [value31, value34, value35, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (224 : Vertex) (229 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 31 = false ∨ valuation q 36 = false ∨ valuation q 40 = false := by
  rw [value31, value34, value36, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (224 : Vertex) (230 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 31 = false ∨ valuation q 36 = false ∨ valuation q 43 = false := by
  rw [value31, value34, value36, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (224 : Vertex) (230 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 31 = false ∨ valuation q 40 = false ∨ valuation q 43 = false := by
  rw [value31, value34, value40, value43]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (224 : Vertex) (236 : Vertex) (244 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 36 = false ∨ valuation q 40 = false := by
  rw [value34, value35, value36, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (228 : Vertex) (229 : Vertex) (230 : Vertex) (236 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block4 (q : Snake 81) (h : Conditions q) : B112E169.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112169
