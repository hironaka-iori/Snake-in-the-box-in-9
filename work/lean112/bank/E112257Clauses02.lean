import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause65 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 126 = true ∨ valuation q 1 = true ∨ valuation q 11 = true ∨ valuation q 15 = true ∨ valuation q 28 = true ∨ valuation q 46 = true := by
  rw [value1, value10, value11, value15, value28, value46, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (16 : Vertex) w → w ∈ region → w ≠ (18 : Vertex) → w ∈ [(0 : Vertex), (17 : Vertex), (24 : Vertex), (48 : Vertex), (144 : Vertex)] := by decide
  have hg := other_cover q (16 : Vertex) (18 : Vertex) [(0 : Vertex), (17 : Vertex), (24 : Vertex), (48 : Vertex), (144 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause66 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 127 = true ∨ valuation q 10 = true ∨ valuation q 47 = true := by
  rw [value10, value11, value47, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (17 : Vertex) w → w ∈ region → w ≠ (21 : Vertex) → w ∈ [(16 : Vertex), (145 : Vertex)] := by decide
  have hg := other_cover q (17 : Vertex) (21 : Vertex) [(16 : Vertex), (145 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause67 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 127 = true ∨ valuation q 10 = true ∨ valuation q 13 = true := by
  rw [value10, value11, value13, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (17 : Vertex) w → w ∈ region → w ≠ (145 : Vertex) → w ∈ [(16 : Vertex), (21 : Vertex)] := by decide
  have hg := other_cover q (17 : Vertex) (145 : Vertex) [(16 : Vertex), (21 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause68 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 128 = true ∨ valuation q 14 = true ∨ valuation q 29 = true := by
  rw [value12, value14, value29, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (18 : Vertex) w → w ∈ region → w ≠ (16 : Vertex) → w ∈ [(22 : Vertex), (50 : Vertex)] := by decide
  have hg := other_cover q (18 : Vertex) (16 : Vertex) [(22 : Vertex), (50 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause69 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 128 = true ∨ valuation q 10 = true ∨ valuation q 29 = true := by
  rw [value10, value12, value29, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (18 : Vertex) w → w ∈ region → w ≠ (22 : Vertex) → w ∈ [(16 : Vertex), (50 : Vertex)] := by decide
  have hg := other_cover q (18 : Vertex) (22 : Vertex) [(16 : Vertex), (50 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause70 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 128 = true ∨ valuation q 10 = true ∨ valuation q 14 = true := by
  rw [value10, value12, value14, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (18 : Vertex) w → w ∈ region → w ≠ (50 : Vertex) → w ∈ [(16 : Vertex), (22 : Vertex)] := by decide
  have hg := other_cover q (18 : Vertex) (50 : Vertex) [(16 : Vertex), (22 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause71 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 11 = false ∨ valuation q 30 = false ∨ valuation q 49 = false := by
  rw [value11, value13, value30, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (21 : Vertex) (17 : Vertex) (53 : Vertex) (149 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause72 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 129 = true ∨ valuation q 30 = true ∨ valuation q 49 = true := by
  rw [value13, value30, value49, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (21 : Vertex) w → w ∈ region → w ≠ (17 : Vertex) → w ∈ [(53 : Vertex), (149 : Vertex)] := by decide
  have hg := other_cover q (21 : Vertex) (17 : Vertex) [(53 : Vertex), (149 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause73 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 129 = true ∨ valuation q 11 = true ∨ valuation q 49 = true := by
  rw [value11, value13, value49, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (21 : Vertex) w → w ∈ region → w ≠ (53 : Vertex) → w ∈ [(17 : Vertex), (149 : Vertex)] := by decide
  have hg := other_cover q (21 : Vertex) (53 : Vertex) [(17 : Vertex), (149 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause74 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 129 = true ∨ valuation q 11 = true ∨ valuation q 30 = true := by
  rw [value11, value13, value30, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (21 : Vertex) w → w ∈ region → w ≠ (149 : Vertex) → w ∈ [(17 : Vertex), (53 : Vertex)] := by decide
  have hg := other_cover q (21 : Vertex) (149 : Vertex) [(17 : Vertex), (53 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause75 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 4 = false ∨ valuation q 12 = false ∨ valuation q 50 = false := by
  rw [value4, value12, value14, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (22 : Vertex) (6 : Vertex) (18 : Vertex) (150 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause76 (q : Snake 81) (h : Conditions q) : valuation q 130 = false ∨ valuation q 12 = false ∨ valuation q 50 = false := by
  rw [value12, value50, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.endpoint_degree_clause q (22 : Vertex) (18 : Vertex) (150 : Vertex) (by decide) (by decide) (by decide)

theorem clause77 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 130 = true ∨ valuation q 12 = true ∨ valuation q 50 = true := by
  rw [value12, value14, value50, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (6 : Vertex) → w ∈ [(18 : Vertex), (150 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (6 : Vertex) [(18 : Vertex), (150 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause78 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 130 = true ∨ valuation q 4 = true ∨ valuation q 50 = true := by
  rw [value4, value14, value50, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (18 : Vertex) → w ∈ [(6 : Vertex), (150 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (18 : Vertex) [(6 : Vertex), (150 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause79 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 130 = true ∨ valuation q 4 = true ∨ valuation q 12 = true := by
  rw [value4, value12, value14, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (150 : Vertex) → w ∈ [(6 : Vertex), (18 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (150 : Vertex) [(6 : Vertex), (18 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause80 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 10 = false ∨ valuation q 17 = false ∨ valuation q 51 = false := by
  rw [value10, value15, value17, value51]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (24 : Vertex) (16 : Vertex) (28 : Vertex) (152 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause81 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 131 = true ∨ valuation q 17 = true ∨ valuation q 51 = true := by
  rw [value15, value17, value51, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (24 : Vertex) w → w ∈ region → w ≠ (16 : Vertex) → w ∈ [(28 : Vertex), (152 : Vertex)] := by decide
  have hg := other_cover q (24 : Vertex) (16 : Vertex) [(28 : Vertex), (152 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause82 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 131 = true ∨ valuation q 10 = true ∨ valuation q 51 = true := by
  rw [value10, value15, value51, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (24 : Vertex) w → w ∈ region → w ≠ (28 : Vertex) → w ∈ [(16 : Vertex), (152 : Vertex)] := by decide
  have hg := other_cover q (24 : Vertex) (28 : Vertex) [(16 : Vertex), (152 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause83 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 131 = true ∨ valuation q 10 = true ∨ valuation q 17 = true := by
  rw [value10, value15, value17, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (24 : Vertex) w → w ∈ region → w ≠ (152 : Vertex) → w ∈ [(16 : Vertex), (28 : Vertex)] := by decide
  have hg := other_cover q (24 : Vertex) (152 : Vertex) [(16 : Vertex), (28 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause84 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 132 = true ∨ valuation q 33 = true ∨ valuation q 53 = true := by
  rw [value16, value33, value53, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (27 : Vertex) w → w ∈ region → w ≠ (31 : Vertex) → w ∈ [(59 : Vertex), (155 : Vertex)] := by decide
  have hg := other_cover q (27 : Vertex) (31 : Vertex) [(59 : Vertex), (155 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause85 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 132 = true ∨ valuation q 18 = true ∨ valuation q 53 = true := by
  rw [value16, value18, value53, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (27 : Vertex) w → w ∈ region → w ≠ (59 : Vertex) → w ∈ [(31 : Vertex), (155 : Vertex)] := by decide
  have hg := other_cover q (27 : Vertex) (59 : Vertex) [(31 : Vertex), (155 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause86 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 132 = true ∨ valuation q 18 = true ∨ valuation q 33 = true := by
  rw [value16, value18, value33, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (27 : Vertex) w → w ∈ region → w ≠ (155 : Vertex) → w ∈ [(31 : Vertex), (59 : Vertex)] := by decide
  have hg := other_cover q (27 : Vertex) (155 : Vertex) [(31 : Vertex), (59 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause87 (q : Snake 81) (h : Conditions q) : valuation q 133 = false ∨ valuation q 17 = true := by
  rw [value17, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  by_cases he : BallClauseLogic.Endpoint q (28 : Vertex)
  · exact Or.inr he.1
  · exact Or.inl he

theorem clause88 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 15 = false ∨ valuation q 34 = false ∨ valuation q 54 = false := by
  rw [value15, value17, value34, value54]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (28 : Vertex) (24 : Vertex) (60 : Vertex) (156 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause89 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 133 = true ∨ valuation q 34 = true ∨ valuation q 54 = true := by
  rw [value17, value34, value54, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (28 : Vertex) w → w ∈ region → w ≠ (24 : Vertex) → w ∈ [(60 : Vertex), (156 : Vertex)] := by decide
  have hg := other_cover q (28 : Vertex) (24 : Vertex) [(60 : Vertex), (156 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause90 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 133 = true ∨ valuation q 15 = true ∨ valuation q 54 = true := by
  rw [value15, value17, value54, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (28 : Vertex) w → w ∈ region → w ≠ (60 : Vertex) → w ∈ [(24 : Vertex), (156 : Vertex)] := by decide
  have hg := other_cover q (28 : Vertex) (60 : Vertex) [(24 : Vertex), (156 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause91 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 133 = true ∨ valuation q 15 = true ∨ valuation q 34 = true := by
  rw [value15, value17, value34, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (28 : Vertex) w → w ∈ region → w ≠ (156 : Vertex) → w ∈ [(24 : Vertex), (60 : Vertex)] := by decide
  have hg := other_cover q (28 : Vertex) (156 : Vertex) [(24 : Vertex), (60 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause92 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 16 = true := by
  rw [value16, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (31 : Vertex) w → w ∈ region → w ∈ [(27 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (31 : Vertex) [(27 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause93 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 134 = true := by
  rw [value18, value134]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (31 : Vertex) w → w ∈ region → w ≠ (27 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (31 : Vertex) (27 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause94 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 20 = false ∨ valuation q 24 = false ∨ valuation q 57 = false := by
  rw [value19, value20, value24, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (33 : Vertex) (35 : Vertex) (41 : Vertex) (161 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause95 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 135 = true ∨ valuation q 24 = true ∨ valuation q 57 = true := by
  rw [value19, value24, value57, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (33 : Vertex) w → w ∈ region → w ≠ (35 : Vertex) → w ∈ [(41 : Vertex), (161 : Vertex)] := by decide
  have hg := other_cover q (33 : Vertex) (35 : Vertex) [(41 : Vertex), (161 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause96 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 135 = true ∨ valuation q 20 = true ∨ valuation q 57 = true := by
  rw [value19, value20, value57, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (33 : Vertex) w → w ∈ region → w ≠ (41 : Vertex) → w ∈ [(35 : Vertex), (161 : Vertex)] := by decide
  have hg := other_cover q (33 : Vertex) (41 : Vertex) [(35 : Vertex), (161 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block2 (q : Snake 81) (h : Conditions q) : B112E257.Block2 (valuation q) :=
  ⟨clause65 q h, clause66 q h, clause67 q h, clause68 q h, clause69 q h, clause70 q h, clause71 q h, clause72 q h, clause73 q h, clause74 q h, clause75 q h, clause76 q h, clause77 q h, clause78 q h, clause79 q h, clause80 q h, clause81 q h, clause82 q h, clause83 q h, clause84 q h, clause85 q h, clause86 q h, clause87 q h, clause88 q h, clause89 q h, clause90 q h, clause91 q h, clause92 q h, clause93 q h, clause94 q h, clause95 q h, clause96 q h⟩

end
end Snake9.Regrowth.E112257
