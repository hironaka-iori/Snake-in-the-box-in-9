import E112147Semantics
import B112E147Inputs
namespace Snake9.Regrowth.E112147
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 101 = true ∨ valuation q 42 = true := by
  rw [value1, value42, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (0 : Vertex) w → w ∈ region → w ≠ (4 : Vertex) → w ∈ [(256 : Vertex)] := by decide
  have hg := other_cover q (0 : Vertex) (4 : Vertex) [(256 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 102 = true ∨ valuation q 1 = true := by
  rw [value1, value2, value102]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (4 : Vertex) w → w ∈ region → w ≠ (6 : Vertex) → w ∈ [(0 : Vertex)] := by decide
  have hg := other_cover q (4 : Vertex) (6 : Vertex) [(0 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 103 = true ∨ valuation q 2 = true := by
  rw [value2, value3, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (6 : Vertex) w → w ∈ region → w ≠ (22 : Vertex) → w ∈ [(4 : Vertex)] := by decide
  have hg := other_cover q (6 : Vertex) (22 : Vertex) [(4 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 104 = true ∨ valuation q 6 = true := by
  rw [value4, value6, value104]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (19 : Vertex) w → w ∈ region → w ≠ (275 : Vertex) → w ∈ [(23 : Vertex)] := by decide
  have hg := other_cover q (19 : Vertex) (275 : Vertex) [(23 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 105 = true ∨ valuation q 3 = true := by
  rw [value3, value5, value105]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (22 : Vertex) w → w ∈ region → w ≠ (23 : Vertex) → w ∈ [(6 : Vertex)] := by decide
  have hg := other_cover q (22 : Vertex) (23 : Vertex) [(6 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 106 = true ∨ valuation q 5 = true := by
  rw [value5, value6, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (23 : Vertex) w → w ∈ region → w ≠ (19 : Vertex) → w ∈ [(22 : Vertex)] := by decide
  have hg := other_cover q (23 : Vertex) (19 : Vertex) [(22 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 107 = true := by
  rw [value7, value107]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (72 : Vertex) w → w ∈ region → w ≠ (104 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (72 : Vertex) (104 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 108 = true ∨ valuation q 7 = true ∨ valuation q 31 = true := by
  rw [value7, value8, value31, value108]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (104 : Vertex) w → w ∈ region → w ≠ (360 : Vertex) → w ∈ [(72 : Vertex), (232 : Vertex)] := by decide
  have hg := other_cover q (104 : Vertex) (360 : Vertex) [(72 : Vertex), (232 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 109 = true ∨ valuation q 10 = true ∨ valuation q 12 = true ∨ valuation q 27 = true := by
  rw [value9, value10, value12, value27, value109]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (160 : Vertex) w → w ∈ region → w ≠ (416 : Vertex) → w ∈ [(164 : Vertex), (168 : Vertex), (224 : Vertex)] := by decide
  have hg := other_cover q (160 : Vertex) (416 : Vertex) [(164 : Vertex), (168 : Vertex), (224 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 9 = false ∨ valuation q 11 = false ∨ valuation q 18 = false := by
  rw [value9, value10, value11, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (164 : Vertex) (160 : Vertex) (166 : Vertex) (180 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 111 = true ∨ valuation q 16 = true ∨ valuation q 20 = true := by
  rw [value11, value16, value20, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (166 : Vertex) w → w ∈ region → w ≠ (164 : Vertex) → w ∈ [(174 : Vertex), (182 : Vertex)] := by decide
  have hg := other_cover q (166 : Vertex) (164 : Vertex) [(174 : Vertex), (182 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 111 = true ∨ valuation q 10 = true ∨ valuation q 20 = true := by
  rw [value10, value11, value20, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (166 : Vertex) w → w ∈ region → w ≠ (174 : Vertex) → w ∈ [(164 : Vertex), (182 : Vertex)] := by decide
  have hg := other_cover q (166 : Vertex) (174 : Vertex) [(164 : Vertex), (182 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 111 = true ∨ valuation q 10 = true ∨ valuation q 16 = true := by
  rw [value10, value11, value16, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (166 : Vertex) w → w ∈ region → w ≠ (182 : Vertex) → w ∈ [(164 : Vertex), (174 : Vertex)] := by decide
  have hg := other_cover q (166 : Vertex) (182 : Vertex) [(164 : Vertex), (174 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 9 = false ∨ valuation q 13 = false ∨ valuation q 31 = false := by
  rw [value9, value12, value13, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (160 : Vertex) (169 : Vertex) (232 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 9 = false ∨ valuation q 13 = false ∨ valuation q 77 = false := by
  rw [value9, value12, value13, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (160 : Vertex) (169 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 9 = false ∨ valuation q 14 = false ∨ valuation q 77 = false := by
  rw [value9, value12, value14, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (160 : Vertex) (170 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 9 = false ∨ valuation q 22 = false ∨ valuation q 77 = false := by
  rw [value9, value12, value22, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (160 : Vertex) (184 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 22 = false := by
  rw [value12, value13, value14, value22]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (169 : Vertex) (170 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 14 = false ∨ valuation q 31 = false ∨ valuation q 77 = false := by
  rw [value12, value14, value31, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (168 : Vertex) (170 : Vertex) (232 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 12 = false ∨ valuation q 23 = false ∨ valuation q 32 = false := by
  rw [value12, value13, value23, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (168 : Vertex) (185 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 15 = false ∨ valuation q 23 = false ∨ valuation q 32 = false := by
  rw [value13, value15, value23, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (169 : Vertex) (171 : Vertex) (185 : Vertex) (233 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 114 = true ∨ valuation q 12 = true ∨ valuation q 16 = true ∨ valuation q 24 = true := by
  rw [value12, value14, value16, value24, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (170 : Vertex) w → w ∈ region → w ≠ (171 : Vertex) → w ∈ [(168 : Vertex), (174 : Vertex), (186 : Vertex)] := by decide
  have hg := other_cover q (170 : Vertex) (171 : Vertex) [(168 : Vertex), (174 : Vertex), (186 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 114 = true ∨ valuation q 12 = true ∨ valuation q 15 = true ∨ valuation q 24 = true := by
  rw [value12, value14, value15, value24, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (170 : Vertex) w → w ∈ region → w ≠ (174 : Vertex) → w ∈ [(168 : Vertex), (171 : Vertex), (186 : Vertex)] := by decide
  have hg := other_cover q (170 : Vertex) (174 : Vertex) [(168 : Vertex), (171 : Vertex), (186 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 114 = true ∨ valuation q 12 = true ∨ valuation q 15 = true ∨ valuation q 16 = true := by
  rw [value12, value14, value15, value16, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (170 : Vertex) w → w ∈ region → w ≠ (186 : Vertex) → w ∈ [(168 : Vertex), (171 : Vertex), (174 : Vertex)] := by decide
  have hg := other_cover q (170 : Vertex) (186 : Vertex) [(168 : Vertex), (171 : Vertex), (174 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 13 = false ∨ valuation q 14 = false ∨ valuation q 25 = false := by
  rw [value13, value14, value15, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (171 : Vertex) (169 : Vertex) (170 : Vertex) (187 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 11 = false ∨ valuation q 14 = false ∨ valuation q 78 = false := by
  rw [value11, value14, value16, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (174 : Vertex) (166 : Vertex) (170 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 11 = false ∨ valuation q 33 = false ∨ valuation q 78 = false := by
  rw [value11, value16, value33, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (174 : Vertex) (166 : Vertex) (238 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 14 = false ∨ valuation q 33 = false ∨ valuation q 78 = false := by
  rw [value14, value16, value33, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (174 : Vertex) (170 : Vertex) (238 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 21 = false ∨ valuation q 25 = false ∨ valuation q 37 = false := by
  rw [value17, value21, value25, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (179 : Vertex) (183 : Vertex) (187 : Vertex) (243 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 19 = false ∨ valuation q 38 = false ∨ valuation q 81 = false := by
  rw [value18, value19, value38, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (181 : Vertex) (244 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 20 = false ∨ valuation q 38 = false ∨ valuation q 81 = false := by
  rw [value18, value20, value38, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (180 : Vertex) (182 : Vertex) (244 : Vertex) (436 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 18 = false ∨ valuation q 21 = false ∨ valuation q 26 = false := by
  rw [value18, value19, value21, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (181 : Vertex) (180 : Vertex) (183 : Vertex) (189 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block0 (q : Snake 81) (h : Conditions q) : B112E147.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112147
