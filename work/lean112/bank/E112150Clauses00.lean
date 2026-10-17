import E112150Semantics
import B112E150Inputs
namespace Snake9.Regrowth.E112150
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 108 = true ∨ valuation q 9 = true := by
  rw [value2, value9, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (13 : Vertex) w → w ∈ region → w ≠ (12 : Vertex) → w ∈ [(29 : Vertex)] := by decide
  have hg := other_cover q (13 : Vertex) (12 : Vertex) [(29 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 109 = true ∨ valuation q 10 = true := by
  rw [value3, value10, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (14 : Vertex) w → w ∈ region → w ≠ (12 : Vertex) → w ∈ [(30 : Vertex)] := by decide
  have hg := other_cover q (14 : Vertex) (12 : Vertex) [(30 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 5 = false ∨ valuation q 21 = false ∨ valuation q 37 = false := by
  rw [value4, value5, value21, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (17 : Vertex) (21 : Vertex) (81 : Vertex) (145 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 2 = false ∨ valuation q 5 = false ∨ valuation q 7 = false := by
  rw [value2, value5, value7, value9]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (29 : Vertex) (13 : Vertex) (21 : Vertex) (25 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 2 = false ∨ valuation q 5 = false ∨ valuation q 11 = false := by
  rw [value2, value5, value9, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (29 : Vertex) (13 : Vertex) (21 : Vertex) (31 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 2 = false ∨ valuation q 7 = false ∨ valuation q 11 = false := by
  rw [value2, value7, value9, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (29 : Vertex) (13 : Vertex) (25 : Vertex) (31 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 3 = false ∨ valuation q 11 = false ∨ valuation q 26 = false := by
  rw [value3, value10, value11, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (30 : Vertex) (14 : Vertex) (31 : Vertex) (94 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 3 = false ∨ valuation q 11 = false ∨ valuation q 42 = false := by
  rw [value3, value10, value11, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (30 : Vertex) (14 : Vertex) (31 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 3 = false ∨ valuation q 26 = false ∨ valuation q 42 = false := by
  rw [value3, value10, value26, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (30 : Vertex) (14 : Vertex) (94 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 11 = false ∨ valuation q 26 = false ∨ valuation q 42 = false := by
  rw [value10, value11, value26, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (30 : Vertex) (31 : Vertex) (94 : Vertex) (158 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 118 = true ∨ valuation q 18 = true := by
  rw [value12, value18, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (67 : Vertex) w → w ∈ region → w ≠ (71 : Vertex) → w ∈ [(75 : Vertex)] := by decide
  have hg := other_cover q (67 : Vertex) (71 : Vertex) [(75 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 118 = true ∨ valuation q 15 = true := by
  rw [value12, value15, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (67 : Vertex) w → w ∈ region → w ≠ (75 : Vertex) → w ∈ [(71 : Vertex)] := by decide
  have hg := other_cover q (67 : Vertex) (75 : Vertex) [(71 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 120 = true ∨ valuation q 15 = true := by
  rw [value14, value15, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (69 : Vertex) w → w ∈ region → w ≠ (68 : Vertex) → w ∈ [(71 : Vertex)] := by decide
  have hg := other_cover q (69 : Vertex) (68 : Vertex) [(71 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 12 = false ∨ valuation q 14 = false ∨ valuation q 19 = false := by
  rw [value12, value14, value15, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (71 : Vertex) (67 : Vertex) (69 : Vertex) (79 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 123 = true ∨ valuation q 18 = true := by
  rw [value17, value18, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (74 : Vertex) w → w ∈ region → w ≠ (72 : Vertex) → w ∈ [(75 : Vertex)] := by decide
  have hg := other_cover q (74 : Vertex) (72 : Vertex) [(75 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 15 = false ∨ valuation q 18 = false ∨ valuation q 27 = false := by
  rw [value15, value18, value19, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (79 : Vertex) (71 : Vertex) (75 : Vertex) (95 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 24 = false := by
  rw [value20, value21, value22, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (80 : Vertex) (81 : Vertex) (84 : Vertex) (88 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 127 = true ∨ valuation q 20 = true ∨ valuation q 25 = true := by
  rw [value20, value21, value25, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (81 : Vertex) w → w ∈ region → w ≠ (17 : Vertex) → w ∈ [(80 : Vertex), (89 : Vertex)] := by decide
  have hg := other_cover q (81 : Vertex) (17 : Vertex) [(80 : Vertex), (89 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 7 = false ∨ valuation q 21 = false ∨ valuation q 24 = false := by
  rw [value7, value21, value24, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (89 : Vertex) (25 : Vertex) (81 : Vertex) (88 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 132 = true ∨ valuation q 10 = true ∨ valuation q 27 = true := by
  rw [value10, value26, value27, value132]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (94 : Vertex) w → w ∈ region → w ≠ (86 : Vertex) → w ∈ [(30 : Vertex), (95 : Vertex)] := by decide
  have hg := other_cover q (94 : Vertex) (86 : Vertex) [(30 : Vertex), (95 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 11 = false ∨ valuation q 19 = false ∨ valuation q 26 = false := by
  rw [value11, value19, value26, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (95 : Vertex) (31 : Vertex) (79 : Vertex) (94 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 38 = false ∨ valuation q 77 = false := by
  rw [value29, value30, value38, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (132 : Vertex) (133 : Vertex) (148 : Vertex) (388 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 136 = true ∨ valuation q 31 = true := by
  rw [value30, value31, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (133 : Vertex) w → w ∈ region → w ≠ (132 : Vertex) → w ∈ [(135 : Vertex)] := by decide
  have hg := other_cover q (133 : Vertex) (132 : Vertex) [(135 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 30 = false ∨ valuation q 136 = true ∨ valuation q 29 = true := by
  rw [value29, value30, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (133 : Vertex) w → w ∈ region → w ≠ (135 : Vertex) → w ∈ [(132 : Vertex)] := by decide
  have hg := other_cover q (133 : Vertex) (135 : Vertex) [(132 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 28 = false ∨ valuation q 30 = false ∨ valuation q 35 = false := by
  rw [value28, value30, value31, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (135 : Vertex) (131 : Vertex) (133 : Vertex) (143 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 139 = true ∨ valuation q 34 = true := by
  rw [value33, value34, value139]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (138 : Vertex) w → w ∈ region → w ≠ (136 : Vertex) → w ∈ [(139 : Vertex)] := by decide
  have hg := other_cover q (138 : Vertex) (136 : Vertex) [(139 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 28 = false ∨ valuation q 33 = false ∨ valuation q 35 = false := by
  rw [value28, value33, value34, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (139 : Vertex) (131 : Vertex) (138 : Vertex) (143 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 37 = false ∨ valuation q 40 = false ∨ valuation q 82 = false := by
  rw [value36, value37, value40, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (145 : Vertex) (152 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 38 = false ∨ valuation q 40 = false ∨ valuation q 82 = false := by
  rw [value36, value38, value40, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (144 : Vertex) (148 : Vertex) (152 : Vertex) (400 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 143 = true ∨ valuation q 4 = true ∨ valuation q 36 = true ∨ valuation q 83 = true := by
  rw [value4, value36, value37, value83, value143]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (145 : Vertex) w → w ∈ region → w ≠ (153 : Vertex) → w ∈ [(17 : Vertex), (144 : Vertex), (401 : Vertex)] := by decide
  have hg := other_cover q (145 : Vertex) (153 : Vertex) [(17 : Vertex), (144 : Vertex), (401 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 38 = false ∨ valuation q 144 = true ∨ valuation q 29 = true ∨ valuation q 36 = true := by
  rw [value29, value36, value38, value144]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (148 : Vertex) w → w ∈ region → w ≠ (150 : Vertex) → w ∈ [(132 : Vertex), (144 : Vertex)] := by decide
  have hg := other_cover q (148 : Vertex) (150 : Vertex) [(132 : Vertex), (144 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 40 = false ∨ valuation q 146 = true ∨ valuation q 36 = true ∨ valuation q 41 = true := by
  rw [value36, value40, value41, value146]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (152 : Vertex) w → w ∈ region → w ≠ (136 : Vertex) → w ∈ [(144 : Vertex), (153 : Vertex)] := by decide
  have hg := other_cover q (152 : Vertex) (136 : Vertex) [(144 : Vertex), (153 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block0 (q : Snake 81) (h : Conditions q) : B112E150.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112150
