import E112169Semantics
import B112E169Inputs
namespace Snake9.Regrowth.E112169
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 17 = true := by
  rw [value17, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (168 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 11 = true ∨ valuation q 26 = true ∨ valuation q 37 = true := by
  rw [value11, value17, value26, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (168 : Vertex) w → w ∈ region → w ∈ [(160 : Vertex), (184 : Vertex), (232 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (168 : Vertex) [(160 : Vertex), (184 : Vertex), (232 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 26 = false ∨ valuation q 37 = false := by
  rw [value26, value37, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (168 : Vertex) (184 : Vertex) (232 : Vertex) (by decide) (by decide) (by decide)

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 133 = true ∨ valuation q 26 = true ∨ valuation q 37 = true := by
  rw [value17, value26, value37, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (168 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(184 : Vertex), (232 : Vertex)] := by decide
  have hg := other_cover q (168 : Vertex) (160 : Vertex) [(184 : Vertex), (232 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 133 = true ∨ valuation q 11 = true ∨ valuation q 37 = true := by
  rw [value11, value17, value37, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (168 : Vertex) w → w ∈ region → w ≠ (184 : Vertex) → w ∈ [(160 : Vertex), (232 : Vertex)] := by decide
  have hg := other_cover q (168 : Vertex) (184 : Vertex) [(160 : Vertex), (232 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 133 = true ∨ valuation q 11 = true ∨ valuation q 26 = true := by
  rw [value11, value17, value26, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (168 : Vertex) w → w ∈ region → w ≠ (232 : Vertex) → w ∈ [(160 : Vertex), (184 : Vertex)] := by decide
  have hg := other_cover q (168 : Vertex) (232 : Vertex) [(160 : Vertex), (184 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 14 = true ∨ valuation q 20 = true ∨ valuation q 39 = true ∨ valuation q 87 = true := by
  rw [value14, value18, value20, value39, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (171 : Vertex) w → w ∈ region → w ∈ [(163 : Vertex), (175 : Vertex), (235 : Vertex), (427 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (171 : Vertex) [(163 : Vertex), (175 : Vertex), (235 : Vertex), (427 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 134 = true ∨ valuation q 20 = true ∨ valuation q 39 = true ∨ valuation q 87 = true := by
  rw [value18, value20, value39, value87, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (171 : Vertex) w → w ∈ region → w ≠ (163 : Vertex) → w ∈ [(175 : Vertex), (235 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (171 : Vertex) (163 : Vertex) [(175 : Vertex), (235 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 134 = true ∨ valuation q 14 = true ∨ valuation q 39 = true ∨ valuation q 87 = true := by
  rw [value14, value18, value39, value87, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (171 : Vertex) w → w ∈ region → w ≠ (175 : Vertex) → w ∈ [(163 : Vertex), (235 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (171 : Vertex) (175 : Vertex) [(163 : Vertex), (235 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 134 = true ∨ valuation q 14 = true ∨ valuation q 20 = true ∨ valuation q 87 = true := by
  rw [value14, value18, value20, value87, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (171 : Vertex) w → w ∈ region → w ≠ (235 : Vertex) → w ∈ [(163 : Vertex), (175 : Vertex), (427 : Vertex)] := by decide
  have hg := other_cover q (171 : Vertex) (235 : Vertex) [(163 : Vertex), (175 : Vertex), (427 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 134 = true ∨ valuation q 14 = true ∨ valuation q 20 = true ∨ valuation q 39 = true := by
  rw [value14, value18, value20, value39, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (171 : Vertex) w → w ∈ region → w ≠ (427 : Vertex) → w ∈ [(163 : Vertex), (175 : Vertex), (235 : Vertex)] := by decide
  have hg := other_cover q (171 : Vertex) (427 : Vertex) [(163 : Vertex), (175 : Vertex), (235 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 15 = true ∨ valuation q 20 = true ∨ valuation q 28 = true := by
  rw [value15, value19, value20, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (173 : Vertex) w → w ∈ region → w ∈ [(165 : Vertex), (175 : Vertex), (189 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (173 : Vertex) [(165 : Vertex), (175 : Vertex), (189 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 15 = false ∨ valuation q 20 = false ∨ valuation q 28 = false := by
  rw [value15, value19, value20, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (173 : Vertex) (165 : Vertex) (175 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 135 = true ∨ valuation q 20 = true ∨ valuation q 28 = true := by
  rw [value19, value20, value28, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (173 : Vertex) w → w ∈ region → w ≠ (165 : Vertex) → w ∈ [(175 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (173 : Vertex) (165 : Vertex) [(175 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 135 = true ∨ valuation q 15 = true ∨ valuation q 28 = true := by
  rw [value15, value19, value28, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (173 : Vertex) w → w ∈ region → w ≠ (175 : Vertex) → w ∈ [(165 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (173 : Vertex) (175 : Vertex) [(165 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 135 = true ∨ valuation q 15 = true ∨ valuation q 20 = true := by
  rw [value15, value19, value20, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (173 : Vertex) w → w ∈ region → w ≠ (189 : Vertex) → w ∈ [(165 : Vertex), (175 : Vertex)] := by decide
  have hg := other_cover q (173 : Vertex) (189 : Vertex) [(165 : Vertex), (175 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 18 = false ∨ valuation q 19 = false ∨ valuation q 30 = false := by
  rw [value18, value19, value20, value30]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (175 : Vertex) (171 : Vertex) (173 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 136 = true ∨ valuation q 18 = true ∨ valuation q 30 = true := by
  rw [value18, value20, value30, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (175 : Vertex) w → w ∈ region → w ≠ (173 : Vertex) → w ∈ [(171 : Vertex), (191 : Vertex)] := by decide
  have hg := other_cover q (175 : Vertex) (173 : Vertex) [(171 : Vertex), (191 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 11 = false ∨ valuation q 22 = false ∨ valuation q 90 = false := by
  rw [value11, value21, value22, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (176 : Vertex) (160 : Vertex) (177 : Vertex) (432 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 137 = true ∨ valuation q 11 = true ∨ valuation q 23 = true ∨ valuation q 26 = true ∨ valuation q 90 = true := by
  rw [value11, value21, value23, value26, value90, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (176 : Vertex) w → w ∈ region → w ≠ (177 : Vertex) → w ∈ [(160 : Vertex), (178 : Vertex), (184 : Vertex), (432 : Vertex)] := by decide
  have hg := other_cover q (176 : Vertex) (177 : Vertex) [(160 : Vertex), (178 : Vertex), (184 : Vertex), (432 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 137 = true ∨ valuation q 11 = true ∨ valuation q 22 = true ∨ valuation q 23 = true ∨ valuation q 26 = true := by
  rw [value11, value21, value22, value23, value26, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (176 : Vertex) w → w ∈ region → w ≠ (432 : Vertex) → w ∈ [(160 : Vertex), (177 : Vertex), (178 : Vertex), (184 : Vertex)] := by decide
  have hg := other_cover q (176 : Vertex) (432 : Vertex) [(160 : Vertex), (177 : Vertex), (178 : Vertex), (184 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 12 = false ∨ valuation q 21 = false ∨ valuation q 24 = false := by
  rw [value12, value21, value22, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (161 : Vertex) (176 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 12 = false ∨ valuation q 21 = false ∨ valuation q 42 = false := by
  rw [value12, value21, value22, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (161 : Vertex) (176 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 12 = false ∨ valuation q 24 = false ∨ valuation q 42 = false := by
  rw [value12, value22, value24, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (161 : Vertex) (179 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 21 = false ∨ valuation q 24 = false ∨ valuation q 42 = false := by
  rw [value21, value22, value24, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (176 : Vertex) (179 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 138 = true ∨ valuation q 21 = true ∨ valuation q 24 = true ∨ valuation q 42 = true := by
  rw [value21, value22, value24, value42, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (177 : Vertex) w → w ∈ region → w ≠ (161 : Vertex) → w ∈ [(176 : Vertex), (179 : Vertex), (241 : Vertex)] := by decide
  have hg := other_cover q (177 : Vertex) (161 : Vertex) [(176 : Vertex), (179 : Vertex), (241 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 138 = true ∨ valuation q 12 = true ∨ valuation q 21 = true ∨ valuation q 42 = true := by
  rw [value12, value21, value22, value42, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (177 : Vertex) w → w ∈ region → w ≠ (179 : Vertex) → w ∈ [(161 : Vertex), (176 : Vertex), (241 : Vertex)] := by decide
  have hg := other_cover q (177 : Vertex) (179 : Vertex) [(161 : Vertex), (176 : Vertex), (241 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 13 = false ∨ valuation q 21 = false ∨ valuation q 24 = false := by
  rw [value13, value21, value23, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (162 : Vertex) (176 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 13 = false ∨ valuation q 21 = false ∨ valuation q 25 = false := by
  rw [value13, value21, value23, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (162 : Vertex) (176 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 13 = false ∨ valuation q 24 = false ∨ valuation q 25 = false := by
  rw [value13, value23, value24, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (162 : Vertex) (179 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 21 = false ∨ valuation q 24 = false ∨ valuation q 25 = false := by
  rw [value21, value23, value24, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (176 : Vertex) (179 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 14 = true ∨ valuation q 22 = true ∨ valuation q 23 = true := by
  rw [value14, value22, value23, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (179 : Vertex) w → w ∈ region → w ∈ [(163 : Vertex), (177 : Vertex), (178 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (179 : Vertex) [(163 : Vertex), (177 : Vertex), (178 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block2 (q : Snake 81) (h : Conditions q) : B112E169.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112169
