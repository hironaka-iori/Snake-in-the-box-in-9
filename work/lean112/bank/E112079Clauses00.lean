import E112079Semantics
import B112E079Inputs
namespace Snake9.Regrowth.E112079
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 111 = true ∨ valuation q 7 = true := by
  rw [value1, value7, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (1 : Vertex) → w ∈ [(16 : Vertex)] := by decide
  have hg := other_cover q (0 : Vertex) (1 : Vertex) [(16 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 112 = true ∨ valuation q 3 = true ∨ valuation q 8 = true := by
  rw [value2, value3, value8, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (1 : Vertex) w → w ∈ region → w ≠ (0 : Vertex) → w ∈ [(5 : Vertex), (17 : Vertex)] := by decide
  have hg := other_cover q (1 : Vertex) (0 : Vertex) [(5 : Vertex), (17 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 112 = true ∨ valuation q 1 = true ∨ valuation q 3 = true := by
  rw [value1, value2, value3, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (1 : Vertex) w → w ∈ region → w ≠ (17 : Vertex) → w ∈ [(0 : Vertex), (5 : Vertex)] := by decide
  have hg := other_cover q (1 : Vertex) (17 : Vertex) [(0 : Vertex), (5 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 114 = true ∨ valuation q 6 = true := by
  rw [value4, value6, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (11 : Vertex) w → w ∈ region → w ≠ (267 : Vertex) → w ∈ [(15 : Vertex)] := by decide
  have hg := other_cover q (11 : Vertex) (267 : Vertex) [(15 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 3 = false ∨ valuation q 6 = false ∨ valuation q 13 = false := by
  rw [value3, value5, value6, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (13 : Vertex) (5 : Vertex) (15 : Vertex) (29 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 1 = false ∨ valuation q 8 = false ∨ valuation q 9 = false := by
  rw [value1, value7, value8, value9]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (16 : Vertex) (0 : Vertex) (17 : Vertex) (18 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 2 = false ∨ valuation q 7 = false ∨ valuation q 10 = false := by
  rw [value2, value7, value8, value10]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (17 : Vertex) (1 : Vertex) (16 : Vertex) (19 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 7 = false ∨ valuation q 10 = false ∨ valuation q 11 = false := by
  rw [value7, value9, value10, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (18 : Vertex) (16 : Vertex) (19 : Vertex) (22 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 8 = true ∨ valuation q 9 = true := by
  rw [value8, value9, value10]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (19 : Vertex) w → w ∈ region → w ∈ [(17 : Vertex), (18 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (19 : Vertex) [(17 : Vertex), (18 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 120 = true ∨ valuation q 8 = true := by
  rw [value8, value10, value120]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (19 : Vertex) w → w ∈ region → w ≠ (18 : Vertex) → w ∈ [(17 : Vertex)] := by decide
  have hg := other_cover q (19 : Vertex) (18 : Vertex) [(17 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 121 = true ∨ valuation q 14 = true := by
  rw [value11, value14, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (18 : Vertex) → w ∈ [(30 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (18 : Vertex) [(30 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 121 = true ∨ valuation q 9 = true := by
  rw [value9, value11, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (30 : Vertex) → w ∈ [(18 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (30 : Vertex) [(18 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 122 = true ∨ valuation q 13 = true := by
  rw [value12, value13, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (28 : Vertex) w → w ∈ region → w ≠ (30 : Vertex) → w ∈ [(29 : Vertex)] := by decide
  have hg := other_cover q (28 : Vertex) (30 : Vertex) [(29 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 124 = true ∨ valuation q 12 = true := by
  rw [value12, value14, value124]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (30 : Vertex) w → w ∈ region → w ≠ (22 : Vertex) → w ∈ [(28 : Vertex)] := by decide
  have hg := other_cover q (30 : Vertex) (22 : Vertex) [(28 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 24 = false := by
  rw [value15, value16, value17, value24]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (161 : Vertex) (162 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 126 = true ∨ valuation q 18 = true ∨ valuation q 19 = true ∨ valuation q 25 = true := by
  rw [value16, value18, value19, value25, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(163 : Vertex), (165 : Vertex), (177 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (160 : Vertex) [(163 : Vertex), (165 : Vertex), (177 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 126 = true ∨ valuation q 15 = true ∨ valuation q 18 = true ∨ valuation q 25 = true := by
  rw [value15, value16, value18, value25, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (165 : Vertex) → w ∈ [(160 : Vertex), (163 : Vertex), (177 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (165 : Vertex) [(160 : Vertex), (163 : Vertex), (177 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 126 = true ∨ valuation q 15 = true ∨ valuation q 18 = true ∨ valuation q 19 = true := by
  rw [value15, value16, value18, value19, value126]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (161 : Vertex) w → w ∈ region → w ≠ (177 : Vertex) → w ∈ [(160 : Vertex), (163 : Vertex), (165 : Vertex)] := by decide
  have hg := other_cover q (161 : Vertex) (177 : Vertex) [(160 : Vertex), (163 : Vertex), (165 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 15 = false ∨ valuation q 26 = false ∨ valuation q 34 = false := by
  rw [value15, value17, value26, value34]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (160 : Vertex) (178 : Vertex) (226 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 15 = false ∨ valuation q 26 = false ∨ valuation q 78 = false := by
  rw [value15, value17, value26, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (160 : Vertex) (178 : Vertex) (418 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 26 = false ∨ valuation q 34 = false ∨ valuation q 78 = false := by
  rw [value17, value26, value34, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (162 : Vertex) (178 : Vertex) (226 : Vertex) (418 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 127 = true ∨ valuation q 15 = true ∨ valuation q 18 = true ∨ valuation q 20 = true ∨ valuation q 26 = true ∨ valuation q 78 = true := by
  rw [value15, value17, value18, value20, value26, value78, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (162 : Vertex) w → w ∈ region → w ≠ (226 : Vertex) → w ∈ [(160 : Vertex), (163 : Vertex), (166 : Vertex), (178 : Vertex), (418 : Vertex)] := by decide
  have hg := other_cover q (162 : Vertex) (226 : Vertex) [(160 : Vertex), (163 : Vertex), (166 : Vertex), (178 : Vertex), (418 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 127 = true ∨ valuation q 15 = true ∨ valuation q 18 = true ∨ valuation q 20 = true ∨ valuation q 26 = true ∨ valuation q 34 = true := by
  rw [value15, value17, value18, value20, value26, value34, value127]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (162 : Vertex) w → w ∈ region → w ≠ (418 : Vertex) → w ∈ [(160 : Vertex), (163 : Vertex), (166 : Vertex), (178 : Vertex), (226 : Vertex)] := by decide
  have hg := other_cover q (162 : Vertex) (418 : Vertex) [(160 : Vertex), (163 : Vertex), (166 : Vertex), (178 : Vertex), (226 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 21 = false := by
  rw [value16, value17, value18, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (161 : Vertex) (162 : Vertex) (171 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 16 = false ∨ valuation q 17 = false ∨ valuation q 27 = false := by
  rw [value16, value17, value18, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (161 : Vertex) (162 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 16 = false ∨ valuation q 21 = false ∨ valuation q 27 = false := by
  rw [value16, value18, value21, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (161 : Vertex) (171 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 17 = false ∨ valuation q 21 = false ∨ valuation q 27 = false := by
  rw [value17, value18, value21, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (163 : Vertex) (162 : Vertex) (171 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 16 = false ∨ valuation q 22 = false ∨ valuation q 36 = false := by
  rw [value16, value19, value22, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (165 : Vertex) (161 : Vertex) (173 : Vertex) (229 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 16 = false ∨ valuation q 22 = false ∨ valuation q 81 = false := by
  rw [value16, value19, value22, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (165 : Vertex) (161 : Vertex) (173 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 22 = false ∨ valuation q 36 = false ∨ valuation q 81 = false := by
  rw [value19, value22, value36, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (165 : Vertex) (173 : Vertex) (229 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 17 = false ∨ valuation q 28 = false ∨ valuation q 37 = false := by
  rw [value17, value20, value28, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (166 : Vertex) (162 : Vertex) (182 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 130 = true ∨ valuation q 17 = true ∨ valuation q 37 = true := by
  rw [value17, value20, value37, value130]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (166 : Vertex) w → w ∈ region → w ≠ (182 : Vertex) → w ∈ [(162 : Vertex), (230 : Vertex)] := by decide
  have hg := other_cover q (166 : Vertex) (182 : Vertex) [(162 : Vertex), (230 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block0 (q : Snake 81) (h : Conditions q) : B112E079.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112079
