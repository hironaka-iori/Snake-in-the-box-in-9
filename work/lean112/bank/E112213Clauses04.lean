import E112213Semantics
import B112E213Inputs
namespace Snake9.Regrowth.E112213
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 25 = false ∨ valuation q 35 = false := by
  rw [value23, value24, value25, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (76 : Vertex) (77 : Vertex) (78 : Vertex) (92 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 25 = false ∨ valuation q 64 = false := by
  rw [value23, value24, value25, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (76 : Vertex) (77 : Vertex) (78 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 35 = false ∨ valuation q 64 = false := by
  rw [value23, value24, value35, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (76 : Vertex) (77 : Vertex) (92 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 35 = false ∨ valuation q 81 = false := by
  rw [value23, value24, value35, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (76 : Vertex) (77 : Vertex) (92 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 64 = false ∨ valuation q 81 = false := by
  rw [value23, value24, value64, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (76 : Vertex) (77 : Vertex) (204 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 25 = false ∨ valuation q 35 = false ∨ valuation q 64 = false := by
  rw [value23, value25, value35, value64]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (76 : Vertex) (78 : Vertex) (92 : Vertex) (204 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 25 = false ∨ valuation q 35 = false ∨ valuation q 81 = false := by
  rw [value23, value25, value35, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (76 : Vertex) (78 : Vertex) (92 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 25 = false ∨ valuation q 64 = false ∨ valuation q 81 = false := by
  rw [value23, value25, value64, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (76 : Vertex) (78 : Vertex) (204 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 35 = false ∨ valuation q 64 = false ∨ valuation q 81 = false := by
  rw [value23, value35, value64, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (76 : Vertex) (92 : Vertex) (204 : Vertex) (332 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 141 = true ∨ valuation q 23 = true ∨ valuation q 26 = true := by
  rw [value23, value24, value26, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (77 : Vertex) w → w ∈ region → w ≠ (69 : Vertex) → w ∈ [(76 : Vertex), (79 : Vertex)] := by decide
  have hg := other_cover q (77 : Vertex) (69 : Vertex) [(76 : Vertex), (79 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 141 = true ∨ valuation q 19 = true ∨ valuation q 26 = true := by
  rw [value19, value24, value26, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (77 : Vertex) w → w ∈ region → w ≠ (76 : Vertex) → w ∈ [(69 : Vertex), (79 : Vertex)] := by decide
  have hg := other_cover q (77 : Vertex) (76 : Vertex) [(69 : Vertex), (79 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 141 = true ∨ valuation q 19 = true ∨ valuation q 23 = true := by
  rw [value19, value23, value24, value141]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (77 : Vertex) w → w ∈ region → w ≠ (79 : Vertex) → w ∈ [(69 : Vertex), (76 : Vertex)] := by decide
  have hg := other_cover q (77 : Vertex) (79 : Vertex) [(69 : Vertex), (76 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 7 = false ∨ valuation q 23 = false ∨ valuation q 26 = false := by
  rw [value7, value23, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (78 : Vertex) (14 : Vertex) (76 : Vertex) (79 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 7 = false ∨ valuation q 23 = false ∨ valuation q 36 = false := by
  rw [value7, value23, value25, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (78 : Vertex) (14 : Vertex) (76 : Vertex) (94 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 7 = false ∨ valuation q 26 = false ∨ valuation q 65 = false := by
  rw [value7, value25, value26, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (78 : Vertex) (14 : Vertex) (79 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 7 = false ∨ valuation q 26 = false ∨ valuation q 82 = false := by
  rw [value7, value25, value26, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (78 : Vertex) (14 : Vertex) (79 : Vertex) (334 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 7 = false ∨ valuation q 36 = false ∨ valuation q 65 = false := by
  rw [value7, value25, value36, value65]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (78 : Vertex) (14 : Vertex) (94 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 7 = false ∨ valuation q 65 = false ∨ valuation q 82 = false := by
  rw [value7, value25, value65, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (78 : Vertex) (14 : Vertex) (206 : Vertex) (334 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 24 = false := by
  rw [value20, value22, value24, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (79 : Vertex) (71 : Vertex) (75 : Vertex) (77 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 25 = false := by
  rw [value20, value22, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (79 : Vertex) (71 : Vertex) (75 : Vertex) (78 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 37 = false := by
  rw [value20, value22, value26, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (79 : Vertex) (71 : Vertex) (75 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 20 = false ∨ valuation q 24 = false ∨ valuation q 25 = false := by
  rw [value20, value24, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (79 : Vertex) (71 : Vertex) (77 : Vertex) (78 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 20 = false ∨ valuation q 24 = false ∨ valuation q 37 = false := by
  rw [value20, value24, value26, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (79 : Vertex) (71 : Vertex) (77 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 20 = false ∨ valuation q 25 = false ∨ valuation q 37 = false := by
  rw [value20, value25, value26, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (79 : Vertex) (71 : Vertex) (78 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 22 = false ∨ valuation q 24 = false ∨ valuation q 25 = false := by
  rw [value22, value24, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (79 : Vertex) (75 : Vertex) (77 : Vertex) (78 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 22 = false ∨ valuation q 24 = false ∨ valuation q 37 = false := by
  rw [value22, value24, value26, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (79 : Vertex) (75 : Vertex) (77 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 22 = false ∨ valuation q 25 = false ∨ valuation q 37 = false := by
  rw [value22, value25, value26, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (79 : Vertex) (75 : Vertex) (78 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 24 = false ∨ valuation q 25 = false ∨ valuation q 37 = false := by
  rw [value24, value25, value26, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (79 : Vertex) (77 : Vertex) (78 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 143 = true ∨ valuation q 20 = true ∨ valuation q 22 = true ∨ valuation q 24 = true ∨ valuation q 25 = true := by
  rw [value20, value22, value24, value25, value26, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (79 : Vertex) w → w ∈ region → w ≠ (95 : Vertex) → w ∈ [(71 : Vertex), (75 : Vertex), (77 : Vertex), (78 : Vertex)] := by decide
  have hg := other_cover q (79 : Vertex) (95 : Vertex) [(71 : Vertex), (75 : Vertex), (77 : Vertex), (78 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 15 = false ∨ valuation q 28 = false ∨ valuation q 31 = false := by
  rw [value15, value27, value28, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (80 : Vertex) (64 : Vertex) (81 : Vertex) (84 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 15 = false ∨ valuation q 28 = false ∨ valuation q 32 = false := by
  rw [value15, value27, value28, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (80 : Vertex) (64 : Vertex) (81 : Vertex) (88 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 15 = false ∨ valuation q 29 = false ∨ valuation q 31 = false := by
  rw [value15, value27, value29, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (80 : Vertex) (64 : Vertex) (82 : Vertex) (84 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block4 (q : Snake 81) (h : Conditions q) : B112E213.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112213
