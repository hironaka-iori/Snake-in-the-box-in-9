import E112024Semantics
import B112E024Inputs
namespace Snake9.Regrowth.E112024
noncomputable section
local instance blockDec4 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause129 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 144 = true ∨ valuation q 13 = true ∨ valuation q 22 = true ∨ valuation q 94 = true := by
  rw [value13, value22, value23, value94, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (177 : Vertex) w → w ∈ region → w ≠ (179 : Vertex) → w ∈ [(161 : Vertex), (176 : Vertex), (433 : Vertex)] := by decide
  have hg := other_cover q (177 : Vertex) (179 : Vertex) [(161 : Vertex), (176 : Vertex), (433 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause130 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 14 = false ∨ valuation q 22 = false ∨ valuation q 25 = false := by
  rw [value14, value22, value24, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (162 : Vertex) (176 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause131 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 14 = false ∨ valuation q 22 = false ∨ valuation q 26 = false := by
  rw [value14, value22, value24, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (162 : Vertex) (176 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause132 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 14 = false ∨ valuation q 25 = false ∨ valuation q 26 = false := by
  rw [value14, value24, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (162 : Vertex) (179 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause133 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 22 = false ∨ valuation q 25 = false ∨ valuation q 26 = false := by
  rw [value22, value24, value25, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (176 : Vertex) (179 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause134 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 145 = true ∨ valuation q 14 = true ∨ valuation q 22 = true ∨ valuation q 25 = true := by
  rw [value14, value22, value24, value25, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (178 : Vertex) w → w ∈ region → w ≠ (182 : Vertex) → w ∈ [(162 : Vertex), (176 : Vertex), (179 : Vertex)] := by decide
  have hg := other_cover q (178 : Vertex) (182 : Vertex) [(162 : Vertex), (176 : Vertex), (179 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause135 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 15 = false ∨ valuation q 23 = false ∨ valuation q 95 = false := by
  rw [value15, value23, value25, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (179 : Vertex) (163 : Vertex) (177 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause136 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 15 = false ∨ valuation q 24 = false ∨ valuation q 95 = false := by
  rw [value15, value24, value25, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (179 : Vertex) (163 : Vertex) (178 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause137 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 95 = false := by
  rw [value23, value24, value25, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (179 : Vertex) (177 : Vertex) (178 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause138 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 146 = true ∨ valuation q 15 = true ∨ valuation q 24 = true ∨ valuation q 95 = true := by
  rw [value15, value24, value25, value95, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (179 : Vertex) w → w ∈ region → w ≠ (177 : Vertex) → w ∈ [(163 : Vertex), (178 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (179 : Vertex) (177 : Vertex) [(163 : Vertex), (178 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause139 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 146 = true ∨ valuation q 15 = true ∨ valuation q 23 = true ∨ valuation q 95 = true := by
  rw [value15, value23, value25, value95, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (179 : Vertex) w → w ∈ region → w ≠ (178 : Vertex) → w ∈ [(163 : Vertex), (177 : Vertex), (435 : Vertex)] := by decide
  have hg := other_cover q (179 : Vertex) (178 : Vertex) [(163 : Vertex), (177 : Vertex), (435 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause140 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 146 = true ∨ valuation q 15 = true ∨ valuation q 23 = true ∨ valuation q 24 = true := by
  rw [value15, value23, value24, value25, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (179 : Vertex) w → w ∈ region → w ≠ (435 : Vertex) → w ∈ [(163 : Vertex), (177 : Vertex), (178 : Vertex)] := by decide
  have hg := other_cover q (179 : Vertex) (435 : Vertex) [(163 : Vertex), (177 : Vertex), (178 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause141 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 17 = false ∨ valuation q 24 = false ∨ valuation q 30 = false := by
  rw [value17, value24, value26, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (182 : Vertex) (166 : Vertex) (178 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause142 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 147 = true ∨ valuation q 24 = true ∨ valuation q 30 = true := by
  rw [value24, value26, value30, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ≠ (166 : Vertex) → w ∈ [(178 : Vertex), (190 : Vertex)] := by decide
  have hg := other_cover q (182 : Vertex) (166 : Vertex) [(178 : Vertex), (190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause143 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 147 = true ∨ valuation q 17 = true ∨ valuation q 30 = true := by
  rw [value17, value26, value30, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ≠ (178 : Vertex) → w ∈ [(166 : Vertex), (190 : Vertex)] := by decide
  have hg := other_cover q (182 : Vertex) (178 : Vertex) [(166 : Vertex), (190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause144 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 147 = true ∨ valuation q 17 = true ∨ valuation q 24 = true := by
  rw [value17, value24, value26, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ≠ (190 : Vertex) → w ∈ [(166 : Vertex), (178 : Vertex)] := by decide
  have hg := other_cover q (182 : Vertex) (190 : Vertex) [(166 : Vertex), (178 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause145 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 18 = false ∨ valuation q 22 = false ∨ valuation q 28 = false := by
  rw [value18, value22, value27, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (168 : Vertex) (176 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause146 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 18 = false ∨ valuation q 22 = false ∨ valuation q 44 = false := by
  rw [value18, value22, value27, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (168 : Vertex) (176 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause147 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 18 = false ∨ valuation q 22 = false ∨ valuation q 99 = false := by
  rw [value18, value22, value27, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (168 : Vertex) (176 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause148 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 18 = false ∨ valuation q 28 = false ∨ valuation q 44 = false := by
  rw [value18, value27, value28, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (168 : Vertex) (188 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause149 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 18 = false ∨ valuation q 28 = false ∨ valuation q 99 = false := by
  rw [value18, value27, value28, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (168 : Vertex) (188 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause150 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 18 = false ∨ valuation q 44 = false ∨ valuation q 99 = false := by
  rw [value18, value27, value44, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (168 : Vertex) (248 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause151 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 22 = false ∨ valuation q 28 = false ∨ valuation q 44 = false := by
  rw [value22, value27, value28, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (176 : Vertex) (188 : Vertex) (248 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause152 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 22 = false ∨ valuation q 28 = false ∨ valuation q 99 = false := by
  rw [value22, value27, value28, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (176 : Vertex) (188 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause153 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 22 = false ∨ valuation q 44 = false ∨ valuation q 99 = false := by
  rw [value22, value27, value44, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (176 : Vertex) (248 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause154 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 28 = false ∨ valuation q 44 = false ∨ valuation q 99 = false := by
  rw [value27, value28, value44, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (184 : Vertex) (188 : Vertex) (248 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause155 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 27 = false ∨ valuation q 29 = false ∨ valuation q 30 = false := by
  rw [value27, value28, value29, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (188 : Vertex) (184 : Vertex) (189 : Vertex) (190 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause156 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 149 = true ∨ valuation q 29 = true ∨ valuation q 30 = true := by
  rw [value28, value29, value30, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (188 : Vertex) w → w ∈ region → w ≠ (184 : Vertex) → w ∈ [(189 : Vertex), (190 : Vertex)] := by decide
  have hg := other_cover q (188 : Vertex) (184 : Vertex) [(189 : Vertex), (190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause157 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 149 = true ∨ valuation q 27 = true ∨ valuation q 30 = true := by
  rw [value27, value28, value30, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (188 : Vertex) w → w ∈ region → w ≠ (189 : Vertex) → w ∈ [(184 : Vertex), (190 : Vertex)] := by decide
  have hg := other_cover q (188 : Vertex) (189 : Vertex) [(184 : Vertex), (190 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause158 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 149 = true ∨ valuation q 27 = true ∨ valuation q 29 = true := by
  rw [value27, value28, value29, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (188 : Vertex) w → w ∈ region → w ≠ (190 : Vertex) → w ∈ [(184 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (188 : Vertex) (190 : Vertex) [(184 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause159 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 20 = false ∨ valuation q 28 = false ∨ valuation q 31 = false := by
  rw [value20, value28, value29, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (189 : Vertex) (173 : Vertex) (188 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause160 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 150 = true ∨ valuation q 28 = true ∨ valuation q 31 = true := by
  rw [value28, value29, value31, value150]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (189 : Vertex) w → w ∈ region → w ≠ (173 : Vertex) → w ∈ [(188 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (189 : Vertex) (173 : Vertex) [(188 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block4 (q : Snake 81) (h : Conditions q) : B112E024.Block4 (valuation q) :=
  ⟨clause129 q h, clause130 q h, clause131 q h, clause132 q h, clause133 q h, clause134 q h, clause135 q h, clause136 q h, clause137 q h, clause138 q h, clause139 q h, clause140 q h, clause141 q h, clause142 q h, clause143 q h, clause144 q h, clause145 q h, clause146 q h, clause147 q h, clause148 q h, clause149 q h, clause150 q h, clause151 q h, clause152 q h, clause153 q h, clause154 q h, clause155 q h, clause156 q h, clause157 q h, clause158 q h, clause159 q h, clause160 q h⟩

end
end Snake9.Regrowth.E112024
