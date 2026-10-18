import E112154Semantics
import B112E154Inputs
namespace Snake9.Regrowth.E112154
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 103 = true ∨ valuation q 3 = true ∨ valuation q 9 = true := by
  rw [value2, value3, value9, value103]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (13 : Vertex) w → w ∈ region → w ≠ (12 : Vertex) → w ∈ [(15 : Vertex), (29 : Vertex)] := by decide
  have hg := other_cover q (13 : Vertex) (12 : Vertex) [(15 : Vertex), (29 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 2 = false ∨ valuation q 11 = false ∨ valuation q 18 = false := by
  rw [value2, value3, value11, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (15 : Vertex) (13 : Vertex) (31 : Vertex) (79 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 2 = false ∨ valuation q 8 = false ∨ valuation q 11 = false := by
  rw [value2, value8, value9, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (29 : Vertex) (13 : Vertex) (28 : Vertex) (31 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 119 = true ∨ valuation q 3 = true ∨ valuation q 17 = true := by
  rw [value3, value17, value18, value119]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (79 : Vertex) w → w ∈ region → w ≠ (71 : Vertex) → w ∈ [(15 : Vertex), (78 : Vertex)] := by decide
  have hg := other_cover q (79 : Vertex) (71 : Vertex) [(15 : Vertex), (78 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 121 = true ∨ valuation q 21 = true := by
  rw [value20, value21, value121]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (84 : Vertex) w → w ∈ region → w ≠ (86 : Vertex) → w ∈ [(85 : Vertex)] := by decide
  have hg := other_cover q (84 : Vertex) (86 : Vertex) [(85 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 6 = false ∨ valuation q 20 = false ∨ valuation q 26 = false := by
  rw [value6, value20, value21, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (85 : Vertex) (21 : Vertex) (84 : Vertex) (93 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 27 = false ∨ valuation q 28 = false ∨ valuation q 30 = false ∨ valuation q 35 = false := by
  rw [value27, value28, value30, value35]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (160 : Vertex) (162 : Vertex) (168 : Vertex) (176 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 129 = true ∨ valuation q 29 = true ∨ valuation q 37 = true := by
  rw [value28, value29, value37, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (162 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(166 : Vertex), (178 : Vertex)] := by decide
  have hg := other_cover q (162 : Vertex) (160 : Vertex) [(166 : Vertex), (178 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 129 = true ∨ valuation q 27 = true ∨ valuation q 37 = true := by
  rw [value27, value28, value37, value129]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (162 : Vertex) w → w ∈ region → w ≠ (166 : Vertex) → w ∈ [(160 : Vertex), (178 : Vertex)] := by decide
  have hg := other_cover q (162 : Vertex) (166 : Vertex) [(160 : Vertex), (178 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 28 = false ∨ valuation q 33 = false ∨ valuation q 50 = false := by
  rw [value28, value29, value33, value50]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (166 : Vertex) (162 : Vertex) (174 : Vertex) (230 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 28 = false ∨ valuation q 33 = false ∨ valuation q 73 = false := by
  rw [value28, value29, value33, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (166 : Vertex) (162 : Vertex) (174 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 29 = false ∨ valuation q 33 = false ∨ valuation q 50 = false ∨ valuation q 73 = false := by
  rw [value29, value33, value50, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (166 : Vertex) (174 : Vertex) (230 : Vertex) (422 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 30 = false ∨ valuation q 32 = false ∨ valuation q 33 = false := by
  rw [value30, value31, value32, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (172 : Vertex) (168 : Vertex) (173 : Vertex) (174 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 31 = false ∨ valuation q 30 = false ∨ valuation q 32 = false ∨ valuation q 41 = false := by
  rw [value30, value31, value32, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (172 : Vertex) (168 : Vertex) (173 : Vertex) (188 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 133 = true ∨ valuation q 34 = true ∨ valuation q 42 = true := by
  rw [value32, value34, value42, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (173 : Vertex) w → w ∈ region → w ≠ (172 : Vertex) → w ∈ [(175 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (173 : Vertex) (172 : Vertex) [(175 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 133 = true ∨ valuation q 31 = true ∨ valuation q 42 = true := by
  rw [value31, value32, value42, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (173 : Vertex) w → w ∈ region → w ≠ (175 : Vertex) → w ∈ [(172 : Vertex), (189 : Vertex)] := by decide
  have hg := other_cover q (173 : Vertex) (175 : Vertex) [(172 : Vertex), (189 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 133 = true ∨ valuation q 31 = true ∨ valuation q 34 = true := by
  rw [value31, value32, value34, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (173 : Vertex) w → w ∈ region → w ≠ (189 : Vertex) → w ∈ [(172 : Vertex), (175 : Vertex)] := by decide
  have hg := other_cover q (173 : Vertex) (189 : Vertex) [(172 : Vertex), (175 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 29 = false ∨ valuation q 31 = false ∨ valuation q 77 = false := by
  rw [value29, value31, value33, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (174 : Vertex) (166 : Vertex) (172 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 29 = false ∨ valuation q 34 = false ∨ valuation q 77 = false := by
  rw [value29, value33, value34, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (174 : Vertex) (166 : Vertex) (175 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 29 = false ∨ valuation q 43 = false ∨ valuation q 77 = false := by
  rw [value29, value33, value43, value77]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (174 : Vertex) (166 : Vertex) (190 : Vertex) (430 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 44 = false := by
  rw [value32, value33, value34, value44]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (175 : Vertex) (173 : Vertex) (174 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 78 = false := by
  rw [value32, value33, value34, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (175 : Vertex) (173 : Vertex) (174 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 32 = false ∨ valuation q 44 = false ∨ valuation q 78 = false := by
  rw [value32, value34, value44, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (175 : Vertex) (173 : Vertex) (191 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 33 = false ∨ valuation q 44 = false ∨ valuation q 78 = false := by
  rw [value33, value34, value44, value78]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (175 : Vertex) (174 : Vertex) (191 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 136 = true ∨ valuation q 36 = true ∨ valuation q 37 = true := by
  rw [value35, value36, value37, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (176 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(177 : Vertex), (178 : Vertex)] := by decide
  have hg := other_cover q (176 : Vertex) (160 : Vertex) [(177 : Vertex), (178 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 35 = false ∨ valuation q 136 = true ∨ valuation q 27 = true ∨ valuation q 37 = true := by
  rw [value27, value35, value37, value136]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (176 : Vertex) w → w ∈ region → w ≠ (177 : Vertex) → w ∈ [(160 : Vertex), (178 : Vertex)] := by decide
  have hg := other_cover q (176 : Vertex) (177 : Vertex) [(160 : Vertex), (178 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 36 = false ∨ valuation q 35 = false ∨ valuation q 38 = false ∨ valuation q 39 = false := by
  rw [value35, value36, value38, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (176 : Vertex) (179 : Vertex) (181 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 28 = false ∨ valuation q 35 = false ∨ valuation q 38 = false := by
  rw [value28, value35, value37, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (162 : Vertex) (176 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 28 = false ∨ valuation q 35 = false ∨ valuation q 53 = false := by
  rw [value28, value35, value37, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (162 : Vertex) (176 : Vertex) (242 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 28 = false ∨ valuation q 38 = false ∨ valuation q 53 = false := by
  rw [value28, value37, value38, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (162 : Vertex) (179 : Vertex) (242 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 28 = false ∨ valuation q 38 = false ∨ valuation q 79 = false := by
  rw [value28, value37, value38, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (162 : Vertex) (179 : Vertex) (434 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 37 = false ∨ valuation q 28 = false ∨ valuation q 53 = false ∨ valuation q 79 = false := by
  rw [value28, value37, value53, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (178 : Vertex) (162 : Vertex) (242 : Vertex) (434 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block0 (q : Snake 81) (h : Conditions q) : B112E154.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112154
