import E112225Semantics
import B112E225Inputs
namespace Snake9.Regrowth.E112225
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 106 = true ∨ valuation q 3 = true := by
  rw [value2, value3, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (2 : Vertex) w → w ∈ region → w ≠ (0 : Vertex) → w ∈ [(6 : Vertex)] := by decide
  have hg := other_cover q (2 : Vertex) (0 : Vertex) [(6 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 2 = false ∨ valuation q 8 = false ∨ valuation q 24 = false := by
  rw [value2, value3, value8, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (6 : Vertex) (2 : Vertex) (70 : Vertex) (134 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 112 = true ∨ valuation q 3 = true ∨ valuation q 9 = true := by
  rw [value3, value8, value9, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (70 : Vertex) w → w ∈ region → w ≠ (78 : Vertex) → w ∈ [(6 : Vertex), (71 : Vertex)] := by decide
  have hg := other_cover q (70 : Vertex) (78 : Vertex) [(6 : Vertex), (71 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 7 = false ∨ valuation q 8 = false ∨ valuation q 13 = false := by
  rw [value7, value8, value9, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (71 : Vertex) (67 : Vertex) (70 : Vertex) (79 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 4 = false ∨ valuation q 11 = false ∨ valuation q 18 = false := by
  rw [value4, value10, value11, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (72 : Vertex) (8 : Vertex) (73 : Vertex) (88 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 115 = true ∨ valuation q 10 = true := by
  rw [value10, value11, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (73 : Vertex) w → w ∈ region → w ≠ (65 : Vertex) → w ∈ [(72 : Vertex)] := by decide
  have hg := other_cover q (73 : Vertex) (65 : Vertex) [(72 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 117 = true ∨ valuation q 9 = true ∨ valuation q 21 = true := by
  rw [value9, value13, value21, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (79 : Vertex) w → w ∈ region → w ≠ (78 : Vertex) → w ∈ [(71 : Vertex), (95 : Vertex)] := by decide
  have hg := other_cover q (79 : Vertex) (78 : Vertex) [(71 : Vertex), (95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 17 = false ∨ valuation q 18 = false := by
  rw [value14, value15, value17, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (80 : Vertex) (82 : Vertex) (84 : Vertex) (88 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 14 = true ∨ valuation q 19 = true := by
  rw [value14, value17, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ∈ [(80 : Vertex), (92 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (84 : Vertex) [(80 : Vertex), (92 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 20 = false := by
  rw [value17, value18, value19, value20]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (92 : Vertex) (84 : Vertex) (88 : Vertex) (93 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 124 = true ∨ valuation q 19 = true := by
  rw [value19, value20, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (93 : Vertex) w → w ∈ region → w ≠ (95 : Vertex) → w ∈ [(92 : Vertex)] := by decide
  have hg := other_cover q (93 : Vertex) (95 : Vertex) [(92 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 125 = true ∨ valuation q 20 = true := by
  rw [value20, value21, value125]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (95 : Vertex) w → w ∈ region → w ≠ (79 : Vertex) → w ∈ [(93 : Vertex)] := by decide
  have hg := other_cover q (95 : Vertex) (79 : Vertex) [(93 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 126 = true ∨ valuation q 23 = true := by
  rw [value22, value23, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (129 : Vertex) w → w ∈ region → w ≠ (137 : Vertex) → w ∈ [(131 : Vertex)] := by decide
  have hg := other_cover q (129 : Vertex) (137 : Vertex) [(131 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 4 = false ∨ valuation q 27 = false ∨ valuation q 34 = false := by
  rw [value4, value26, value27, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (136 : Vertex) (8 : Vertex) (137 : Vertex) (152 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 131 = true ∨ valuation q 22 = true ∨ valuation q 78 = true := by
  rw [value22, value27, value78, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (136 : Vertex) → w ∈ [(129 : Vertex), (393 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (136 : Vertex) [(129 : Vertex), (393 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 131 = true ∨ valuation q 22 = true ∨ valuation q 26 = true := by
  rw [value22, value26, value27, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (137 : Vertex) w → w ∈ region → w ≠ (393 : Vertex) → w ∈ [(129 : Vertex), (136 : Vertex)] := by decide
  have hg := other_cover q (137 : Vertex) (393 : Vertex) [(129 : Vertex), (136 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 25 = false ∨ valuation q 28 = false ∨ valuation q 37 = false := by
  rw [value25, value28, value29, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (143 : Vertex) (135 : Vertex) (142 : Vertex) (159 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 31 = false ∨ valuation q 33 = false ∨ valuation q 34 = false := by
  rw [value30, value31, value33, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (146 : Vertex) (148 : Vertex) (152 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 135 = true ∨ valuation q 32 = true := by
  rw [value31, value32, value135]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (146 : Vertex) w → w ∈ region → w ≠ (144 : Vertex) → w ∈ [(147 : Vertex)] := by decide
  have hg := other_cover q (146 : Vertex) (144 : Vertex) [(147 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 23 = false ∨ valuation q 31 = false ∨ valuation q 83 = false := by
  rw [value23, value31, value32, value83]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (147 : Vertex) (131 : Vertex) (146 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 137 = true ∨ valuation q 30 = true ∨ valuation q 35 = true := by
  rw [value30, value33, value35, value137]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (404 : Vertex) → w ∈ [(144 : Vertex), (156 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (404 : Vertex) [(144 : Vertex), (156 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 26 = true ∨ valuation q 30 = true ∨ valuation q 35 = true := by
  rw [value26, value30, value34, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ∈ [(136 : Vertex), (144 : Vertex), (156 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (152 : Vertex) [(136 : Vertex), (144 : Vertex), (156 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 138 = true ∨ valuation q 30 = true ∨ valuation q 35 = true := by
  rw [value30, value34, value35, value138]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ≠ (136 : Vertex) → w ∈ [(144 : Vertex), (156 : Vertex)] := by decide
  have hg := other_cover q (152 : Vertex) (136 : Vertex) [(144 : Vertex), (156 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 33 = false ∨ valuation q 34 = false ∨ valuation q 36 = false := by
  rw [value33, value34, value35, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (156 : Vertex) (148 : Vertex) (152 : Vertex) (157 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 140 = true ∨ valuation q 37 = true := by
  rw [value36, value37, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (157 : Vertex) w → w ∈ region → w ≠ (156 : Vertex) → w ∈ [(159 : Vertex)] := by decide
  have hg := other_cover q (157 : Vertex) (156 : Vertex) [(159 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 140 = true ∨ valuation q 35 = true := by
  rw [value35, value36, value140]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (157 : Vertex) w → w ∈ region → w ≠ (159 : Vertex) → w ∈ [(156 : Vertex)] := by decide
  have hg := other_cover q (157 : Vertex) (159 : Vertex) [(156 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 39 = false ∨ valuation q 38 = false ∨ valuation q 41 = false ∨ valuation q 48 = false := by
  rw [value38, value39, value41, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (227 : Vertex) (225 : Vertex) (231 : Vertex) (243 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 144 = true ∨ valuation q 44 = true ∨ valuation q 102 = true := by
  rw [value40, value44, value102, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (230 : Vertex) w → w ∈ region → w ≠ (231 : Vertex) → w ∈ [(238 : Vertex), (486 : Vertex)] := by decide
  have hg := other_cover q (230 : Vertex) (231 : Vertex) [(238 : Vertex), (486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 144 = true ∨ valuation q 41 = true ∨ valuation q 102 = true := by
  rw [value40, value41, value102, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (230 : Vertex) w → w ∈ region → w ≠ (238 : Vertex) → w ∈ [(231 : Vertex), (486 : Vertex)] := by decide
  have hg := other_cover q (230 : Vertex) (238 : Vertex) [(231 : Vertex), (486 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 41 = false ∨ valuation q 39 = false ∨ valuation q 40 = false ∨ valuation q 45 = false := by
  rw [value39, value40, value41, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (231 : Vertex) (227 : Vertex) (230 : Vertex) (239 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 42 = false ∨ valuation q 43 = false ∨ valuation q 50 = false ∨ valuation q 103 = false := by
  rw [value42, value43, value50, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (232 : Vertex) (233 : Vertex) (248 : Vertex) (488 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 147 = true ∨ valuation q 42 = true := by
  rw [value42, value43, value147]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (233 : Vertex) w → w ∈ region → w ≠ (225 : Vertex) → w ∈ [(232 : Vertex)] := by decide
  have hg := other_cover q (233 : Vertex) (225 : Vertex) [(232 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block0 (q : Snake 81) (h : Conditions q) : B112E225.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112225
