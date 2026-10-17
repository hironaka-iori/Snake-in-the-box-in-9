import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 12 = false ∨ valuation q 20 = false ∨ valuation q 23 = false := by
  rw [value12, value15, value20, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (129 : Vertex) (141 : Vertex) (149 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 14 = false ∨ valuation q 20 = false ∨ valuation q 23 = false := by
  rw [value14, value15, value20, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (133 : Vertex) (132 : Vertex) (141 : Vertex) (149 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 139 = true ∨ valuation q 3 = true ∨ valuation q 14 = true ∨ valuation q 20 = true ∨ valuation q 23 = true := by
  rw [value3, value14, value15, value20, value23, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (133 : Vertex) w → w ∈ region → w ≠ (129 : Vertex) → w ∈ [(5 : Vertex), (132 : Vertex), (141 : Vertex), (149 : Vertex)] := by decide
  have hg := other_cover q (133 : Vertex) (129 : Vertex) [(5 : Vertex), (132 : Vertex), (141 : Vertex), (149 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 4 = false ∨ valuation q 14 = false ∨ valuation q 24 = false := by
  rw [value4, value14, value16, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (6 : Vertex) (132 : Vertex) (150 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 4 = false ∨ valuation q 14 = false ∨ valuation q 32 = false := by
  rw [value4, value14, value16, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (6 : Vertex) (132 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 4 = false ∨ valuation q 24 = false ∨ valuation q 32 = false := by
  rw [value4, value16, value24, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (6 : Vertex) (150 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 14 = false ∨ valuation q 24 = false ∨ valuation q 32 = false := by
  rw [value14, value16, value24, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (132 : Vertex) (150 : Vertex) (198 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 27 = false ∨ valuation q 87 = false := by
  rw [value17, value18, value27, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (138 : Vertex) (139 : Vertex) (154 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 142 = true ∨ valuation q 13 = true ∨ valuation q 28 = true := by
  rw [value13, value18, value28, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (139 : Vertex) w → w ∈ region → w ≠ (138 : Vertex) → w ∈ [(131 : Vertex), (155 : Vertex)] := by decide
  have hg := other_cover q (139 : Vertex) (138 : Vertex) [(131 : Vertex), (155 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 142 = true ∨ valuation q 13 = true ∨ valuation q 17 = true := by
  rw [value13, value17, value18, value142]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (139 : Vertex) w → w ∈ region → w ≠ (155 : Vertex) → w ∈ [(131 : Vertex), (138 : Vertex)] := by decide
  have hg := other_cover q (139 : Vertex) (155 : Vertex) [(131 : Vertex), (138 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 5 = false ∨ valuation q 14 = false ∨ valuation q 20 = false := by
  rw [value5, value14, value19, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (140 : Vertex) (12 : Vertex) (132 : Vertex) (141 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 5 = false ∨ valuation q 20 = false ∨ valuation q 88 = false := by
  rw [value5, value19, value20, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (140 : Vertex) (12 : Vertex) (141 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 14 = false ∨ valuation q 20 = false ∨ valuation q 88 = false := by
  rw [value14, value19, value20, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (140 : Vertex) (132 : Vertex) (141 : Vertex) (396 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 143 = true ∨ valuation q 5 = true ∨ valuation q 14 = true ∨ valuation q 88 = true := by
  rw [value5, value14, value19, value88, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (140 : Vertex) w → w ∈ region → w ≠ (141 : Vertex) → w ∈ [(12 : Vertex), (132 : Vertex), (396 : Vertex)] := by decide
  have hg := other_cover q (140 : Vertex) (141 : Vertex) [(12 : Vertex), (132 : Vertex), (396 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 15 = false ∨ valuation q 19 = false ∨ valuation q 89 = false := by
  rw [value15, value19, value20, value89]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (141 : Vertex) (133 : Vertex) (140 : Vertex) (397 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 144 = true ∨ valuation q 19 = true ∨ valuation q 89 = true := by
  rw [value19, value20, value89, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (141 : Vertex) w → w ∈ region → w ≠ (133 : Vertex) → w ∈ [(140 : Vertex), (397 : Vertex)] := by decide
  have hg := other_cover q (141 : Vertex) (133 : Vertex) [(140 : Vertex), (397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 144 = true ∨ valuation q 15 = true ∨ valuation q 89 = true := by
  rw [value15, value20, value89, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (141 : Vertex) w → w ∈ region → w ≠ (140 : Vertex) → w ∈ [(133 : Vertex), (397 : Vertex)] := by decide
  have hg := other_cover q (141 : Vertex) (140 : Vertex) [(133 : Vertex), (397 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 144 = true ∨ valuation q 15 = true ∨ valuation q 19 = true := by
  rw [value15, value19, value20, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (141 : Vertex) w → w ∈ region → w ≠ (397 : Vertex) → w ∈ [(133 : Vertex), (140 : Vertex)] := by decide
  have hg := other_cover q (141 : Vertex) (397 : Vertex) [(133 : Vertex), (140 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 26 = false ∨ valuation q 92 = false := by
  rw [value21, value22, value26, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (148 : Vertex) (152 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 145 = true ∨ valuation q 26 = true ∨ valuation q 92 = true := by
  rw [value21, value26, value92, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (144 : Vertex) w → w ∈ region → w ≠ (148 : Vertex) → w ∈ [(152 : Vertex), (400 : Vertex)] := by decide
  have hg := other_cover q (144 : Vertex) (148 : Vertex) [(152 : Vertex), (400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 145 = true ∨ valuation q 22 = true ∨ valuation q 92 = true := by
  rw [value21, value22, value92, value145]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (144 : Vertex) w → w ∈ region → w ≠ (152 : Vertex) → w ∈ [(148 : Vertex), (400 : Vertex)] := by decide
  have hg := other_cover q (144 : Vertex) (152 : Vertex) [(148 : Vertex), (400 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 14 = false ∨ valuation q 21 = false ∨ valuation q 23 = false := by
  rw [value14, value21, value22, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (148 : Vertex) (132 : Vertex) (144 : Vertex) (149 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 14 = false ∨ valuation q 21 = false ∨ valuation q 24 = false := by
  rw [value14, value21, value22, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (148 : Vertex) (132 : Vertex) (144 : Vertex) (150 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 14 = false ∨ valuation q 23 = false ∨ valuation q 24 = false := by
  rw [value14, value22, value23, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (148 : Vertex) (132 : Vertex) (149 : Vertex) (150 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 21 = false ∨ valuation q 23 = false ∨ valuation q 24 = false := by
  rw [value21, value22, value23, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (148 : Vertex) (144 : Vertex) (149 : Vertex) (150 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 15 = false ∨ valuation q 25 = false ∨ valuation q 41 = false := by
  rw [value15, value23, value25, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (149 : Vertex) (133 : Vertex) (151 : Vertex) (213 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 16 = false ∨ valuation q 22 = false ∨ valuation q 25 = false := by
  rw [value16, value22, value24, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (150 : Vertex) (134 : Vertex) (148 : Vertex) (151 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 148 = true ∨ valuation q 22 = true ∨ valuation q 25 = true := by
  rw [value22, value24, value25, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (150 : Vertex) w → w ∈ region → w ≠ (134 : Vertex) → w ∈ [(148 : Vertex), (151 : Vertex)] := by decide
  have hg := other_cover q (150 : Vertex) (134 : Vertex) [(148 : Vertex), (151 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 148 = true ∨ valuation q 16 = true ∨ valuation q 25 = true := by
  rw [value16, value24, value25, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (150 : Vertex) w → w ∈ region → w ≠ (148 : Vertex) → w ∈ [(134 : Vertex), (151 : Vertex)] := by decide
  have hg := other_cover q (150 : Vertex) (148 : Vertex) [(134 : Vertex), (151 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 148 = true ∨ valuation q 16 = true ∨ valuation q 22 = true := by
  rw [value16, value22, value24, value148]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (150 : Vertex) w → w ∈ region → w ≠ (151 : Vertex) → w ∈ [(134 : Vertex), (148 : Vertex)] := by decide
  have hg := other_cover q (150 : Vertex) (151 : Vertex) [(134 : Vertex), (148 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 96 = false := by
  rw [value23, value24, value25, value96]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (151 : Vertex) (149 : Vertex) (150 : Vertex) (407 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 149 = true ∨ valuation q 23 = true ∨ valuation q 96 = true := by
  rw [value23, value25, value96, value149]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (151 : Vertex) w → w ∈ region → w ≠ (150 : Vertex) → w ∈ [(149 : Vertex), (407 : Vertex)] := by decide
  have hg := other_cover q (151 : Vertex) (150 : Vertex) [(149 : Vertex), (407 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block1 (q : Snake 81) (h : Conditions q) : B112E153.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112153
