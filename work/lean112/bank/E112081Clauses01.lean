import E112081Semantics
import B112E081Inputs
namespace Snake9.Regrowth.E112081
noncomputable section
local instance blockDec1 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause33 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 126 = true ∨ valuation q 2 = true ∨ valuation q 11 = true ∨ valuation q 59 = true := by
  rw [value2, value9, value11, value59, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (17 : Vertex) w → w ∈ region → w ≠ (16 : Vertex) → w ∈ [(1 : Vertex), (19 : Vertex), (273 : Vertex)] := by decide
  have hg := other_cover q (17 : Vertex) (16 : Vertex) [(1 : Vertex), (19 : Vertex), (273 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause34 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 126 = true ∨ valuation q 2 = true ∨ valuation q 8 = true ∨ valuation q 59 = true := by
  rw [value2, value8, value9, value59, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (17 : Vertex) w → w ∈ region → w ≠ (19 : Vertex) → w ∈ [(1 : Vertex), (16 : Vertex), (273 : Vertex)] := by decide
  have hg := other_cover q (17 : Vertex) (19 : Vertex) [(1 : Vertex), (16 : Vertex), (273 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause35 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 127 = true ∨ valuation q 8 = true ∨ valuation q 12 = true := by
  rw [value8, value10, value12, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (18 : Vertex) w → w ∈ region → w ≠ (19 : Vertex) → w ∈ [(16 : Vertex), (22 : Vertex)] := by decide
  have hg := other_cover q (18 : Vertex) (19 : Vertex) [(16 : Vertex), (22 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause36 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 127 = true ∨ valuation q 8 = true ∨ valuation q 11 = true := by
  rw [value8, value10, value11, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (18 : Vertex) w → w ∈ region → w ≠ (22 : Vertex) → w ∈ [(16 : Vertex), (19 : Vertex)] := by decide
  have hg := other_cover q (18 : Vertex) (22 : Vertex) [(16 : Vertex), (19 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause37 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 9 = false ∨ valuation q 10 = false ∨ valuation q 60 = false := by
  rw [value9, value10, value11, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (19 : Vertex) (17 : Vertex) (18 : Vertex) (275 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause38 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 128 = true ∨ valuation q 10 = true ∨ valuation q 60 = true := by
  rw [value10, value11, value60, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (19 : Vertex) w → w ∈ region → w ≠ (17 : Vertex) → w ∈ [(18 : Vertex), (275 : Vertex)] := by decide
  have hg := other_cover q (19 : Vertex) (17 : Vertex) [(18 : Vertex), (275 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause39 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 3 = false ∨ valuation q 10 = false ∨ valuation q 15 = false := by
  rw [value3, value10, value12, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (22 : Vertex) (6 : Vertex) (18 : Vertex) (30 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause40 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 129 = true ∨ valuation q 10 = true ∨ valuation q 15 = true := by
  rw [value10, value12, value15, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (6 : Vertex) → w ∈ [(18 : Vertex), (30 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (6 : Vertex) [(18 : Vertex), (30 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause41 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 14 = true ∨ valuation q 15 = true := by
  rw [value13, value14, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (28 : Vertex) w → w ∈ region → w ∈ [(29 : Vertex), (30 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (28 : Vertex) [(29 : Vertex), (30 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause42 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 130 = true ∨ valuation q 15 = true := by
  rw [value13, value15, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (28 : Vertex) w → w ∈ region → w ≠ (29 : Vertex) → w ∈ [(30 : Vertex)] := by decide
  have hg := other_cover q (28 : Vertex) (29 : Vertex) [(30 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause43 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 130 = true ∨ valuation q 14 = true := by
  rw [value13, value14, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (28 : Vertex) w → w ∈ region → w ≠ (30 : Vertex) → w ∈ [(29 : Vertex)] := by decide
  have hg := other_cover q (28 : Vertex) (30 : Vertex) [(29 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause44 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 6 = false ∨ valuation q 13 = false ∨ valuation q 32 = false := by
  rw [value6, value13, value14, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (29 : Vertex) (13 : Vertex) (28 : Vertex) (157 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause45 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 131 = true ∨ valuation q 13 = true ∨ valuation q 32 = true := by
  rw [value13, value14, value32, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (29 : Vertex) w → w ∈ region → w ≠ (13 : Vertex) → w ∈ [(28 : Vertex), (157 : Vertex)] := by decide
  have hg := other_cover q (29 : Vertex) (13 : Vertex) [(28 : Vertex), (157 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause46 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 131 = true ∨ valuation q 6 = true ∨ valuation q 13 = true := by
  rw [value6, value13, value14, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (29 : Vertex) w → w ∈ region → w ≠ (157 : Vertex) → w ∈ [(13 : Vertex), (28 : Vertex)] := by decide
  have hg := other_cover q (29 : Vertex) (157 : Vertex) [(13 : Vertex), (28 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause47 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 132 = true ∨ valuation q 13 = true := by
  rw [value13, value15, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (30 : Vertex) w → w ∈ region → w ≠ (22 : Vertex) → w ∈ [(28 : Vertex)] := by decide
  have hg := other_cover q (30 : Vertex) (22 : Vertex) [(28 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause48 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 132 = true ∨ valuation q 12 = true := by
  rw [value12, value15, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (30 : Vertex) w → w ∈ region → w ≠ (28 : Vertex) → w ∈ [(22 : Vertex)] := by decide
  have hg := other_cover q (30 : Vertex) (28 : Vertex) [(22 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause49 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 1 = false ∨ valuation q 17 = false ∨ valuation q 18 = false := by
  rw [value1, value16, value17, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (128 : Vertex) (0 : Vertex) (130 : Vertex) (132 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause50 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 1 = false ∨ valuation q 17 = false ∨ valuation q 21 = false := by
  rw [value1, value16, value17, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (128 : Vertex) (0 : Vertex) (130 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause51 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 1 = false ∨ valuation q 17 = false ∨ valuation q 87 = false := by
  rw [value1, value16, value17, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (128 : Vertex) (0 : Vertex) (130 : Vertex) (384 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause52 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 1 = false ∨ valuation q 18 = false ∨ valuation q 21 = false := by
  rw [value1, value16, value18, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (128 : Vertex) (0 : Vertex) (132 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause53 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 1 = false ∨ valuation q 18 = false ∨ valuation q 87 = false := by
  rw [value1, value16, value18, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (128 : Vertex) (0 : Vertex) (132 : Vertex) (384 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause54 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 1 = false ∨ valuation q 21 = false ∨ valuation q 87 = false := by
  rw [value1, value16, value21, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (128 : Vertex) (0 : Vertex) (136 : Vertex) (384 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause55 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 21 = false := by
  rw [value16, value17, value18, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (128 : Vertex) (130 : Vertex) (132 : Vertex) (136 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause56 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 87 = false := by
  rw [value16, value17, value18, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (128 : Vertex) (130 : Vertex) (132 : Vertex) (384 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause57 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 134 = true ∨ valuation q 19 = true ∨ valuation q 23 = true := by
  rw [value17, value19, value23, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (130 : Vertex) w → w ∈ region → w ≠ (128 : Vertex) → w ∈ [(134 : Vertex), (138 : Vertex)] := by decide
  have hg := other_cover q (130 : Vertex) (128 : Vertex) [(134 : Vertex), (138 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause58 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 134 = true ∨ valuation q 16 = true ∨ valuation q 23 = true := by
  rw [value16, value17, value23, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (130 : Vertex) w → w ∈ region → w ≠ (134 : Vertex) → w ∈ [(128 : Vertex), (138 : Vertex)] := by decide
  have hg := other_cover q (130 : Vertex) (134 : Vertex) [(128 : Vertex), (138 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause59 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 134 = true ∨ valuation q 16 = true ∨ valuation q 19 = true := by
  rw [value16, value17, value19, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (130 : Vertex) w → w ∈ region → w ≠ (138 : Vertex) → w ∈ [(128 : Vertex), (134 : Vertex)] := by decide
  have hg := other_cover q (130 : Vertex) (138 : Vertex) [(128 : Vertex), (134 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause60 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 16 = false ∨ valuation q 24 = false ∨ valuation q 26 = false := by
  rw [value16, value18, value24, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (128 : Vertex) (140 : Vertex) (148 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause61 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 135 = true ∨ valuation q 16 = true ∨ valuation q 19 = true ∨ valuation q 24 = true := by
  rw [value16, value18, value19, value24, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (132 : Vertex) w → w ∈ region → w ≠ (148 : Vertex) → w ∈ [(128 : Vertex), (134 : Vertex), (140 : Vertex)] := by decide
  have hg := other_cover q (132 : Vertex) (148 : Vertex) [(128 : Vertex), (134 : Vertex), (140 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause62 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 3 = false ∨ valuation q 17 = false ∨ valuation q 18 = false := by
  rw [value3, value17, value18, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (6 : Vertex) (130 : Vertex) (132 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause63 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 3 = false ∨ valuation q 17 = false ∨ valuation q 20 = false := by
  rw [value3, value17, value19, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (6 : Vertex) (130 : Vertex) (135 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause64 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 3 = false ∨ valuation q 17 = false ∨ valuation q 25 = false := by
  rw [value3, value17, value19, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (134 : Vertex) (6 : Vertex) (130 : Vertex) (142 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block1 (q : Snake 81) (h : Conditions q) : B112E081.Block1 (valuation q) :=
  ⟨clause33 q h, clause34 q h, clause35 q h, clause36 q h, clause37 q h, clause38 q h, clause39 q h, clause40 q h, clause41 q h, clause42 q h, clause43 q h, clause44 q h, clause45 q h, clause46 q h, clause47 q h, clause48 q h, clause49 q h, clause50 q h, clause51 q h, clause52 q h, clause53 q h, clause54 q h, clause55 q h, clause56 q h, clause57 q h, clause58 q h, clause59 q h, clause60 q h, clause61 q h, clause62 q h, clause63 q h, clause64 q h⟩

end
end Snake9.Regrowth.E112081
