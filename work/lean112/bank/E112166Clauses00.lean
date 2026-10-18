import E112166Semantics
import B112E166Inputs
namespace Snake9.Regrowth.E112166
noncomputable section
local instance blockDec0 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 3 = false ∨ valuation q 5 = false ∨ valuation q 45 = false := by
  rw [value1, value3, value5, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (5 : Vertex) (13 : Vertex) (21 : Vertex) (261 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause2 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 110 = true ∨ valuation q 3 = true ∨ valuation q 45 = true := by
  rw [value1, value3, value45, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (5 : Vertex) w → w ∈ region → w ≠ (21 : Vertex) → w ∈ [(13 : Vertex), (261 : Vertex)] := by decide
  have hg := other_cover q (5 : Vertex) (21 : Vertex) [(13 : Vertex), (261 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause3 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 110 = true ∨ valuation q 3 = true ∨ valuation q 5 = true := by
  rw [value1, value3, value5, value110]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (5 : Vertex) w → w ∈ region → w ≠ (261 : Vertex) → w ∈ [(13 : Vertex), (21 : Vertex)] := by decide
  have hg := other_cover q (5 : Vertex) (261 : Vertex) [(13 : Vertex), (21 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause4 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 111 = true ∨ valuation q 46 = true := by
  rw [value2, value46, value111]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (11 : Vertex) w → w ∈ region → w ≠ (27 : Vertex) → w ∈ [(267 : Vertex)] := by decide
  have hg := other_cover q (11 : Vertex) (27 : Vertex) [(267 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause5 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 112 = true ∨ valuation q 1 = true ∨ valuation q 48 = true := by
  rw [value1, value3, value48, value112]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (13 : Vertex) w → w ∈ region → w ≠ (45 : Vertex) → w ∈ [(5 : Vertex), (269 : Vertex)] := by decide
  have hg := other_cover q (13 : Vertex) (45 : Vertex) [(5 : Vertex), (269 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause6 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 5 = false ∨ valuation q 7 = false ∨ valuation q 52 = false := by
  rw [value4, value5, value7, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (17 : Vertex) (21 : Vertex) (25 : Vertex) (273 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause7 (q : Snake 81) (h : Conditions q) : valuation q 4 = false ∨ valuation q 113 = true ∨ valuation q 7 = true ∨ valuation q 52 = true := by
  rw [value4, value7, value52, value113]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (17 : Vertex) w → w ∈ region → w ≠ (21 : Vertex) → w ∈ [(25 : Vertex), (273 : Vertex)] := by decide
  have hg := other_cover q (17 : Vertex) (21 : Vertex) [(25 : Vertex), (273 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause8 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 114 = true ∨ valuation q 4 = true ∨ valuation q 6 = true := by
  rw [value4, value5, value6, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (21 : Vertex) w → w ∈ region → w ≠ (5 : Vertex) → w ∈ [(17 : Vertex), (23 : Vertex)] := by decide
  have hg := other_cover q (21 : Vertex) (5 : Vertex) [(17 : Vertex), (23 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause9 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 114 = true ∨ valuation q 1 = true ∨ valuation q 6 = true := by
  rw [value1, value5, value6, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (21 : Vertex) w → w ∈ region → w ≠ (17 : Vertex) → w ∈ [(5 : Vertex), (23 : Vertex)] := by decide
  have hg := other_cover q (21 : Vertex) (17 : Vertex) [(5 : Vertex), (23 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause10 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 114 = true ∨ valuation q 1 = true ∨ valuation q 4 = true := by
  rw [value1, value4, value5, value114]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (21 : Vertex) w → w ∈ region → w ≠ (23 : Vertex) → w ∈ [(5 : Vertex), (17 : Vertex)] := by decide
  have hg := other_cover q (21 : Vertex) (23 : Vertex) [(5 : Vertex), (17 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause11 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 115 = true := by
  rw [value6, value115]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (23 : Vertex) w → w ∈ region → w ≠ (21 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (23 : Vertex) (21 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause12 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 116 = true ∨ valuation q 9 = true := by
  rw [value7, value9, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (25 : Vertex) w → w ∈ region → w ≠ (17 : Vertex) → w ∈ [(27 : Vertex)] := by decide
  have hg := other_cover q (25 : Vertex) (17 : Vertex) [(27 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause13 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 116 = true ∨ valuation q 4 = true := by
  rw [value4, value7, value116]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (25 : Vertex) w → w ∈ region → w ≠ (27 : Vertex) → w ∈ [(17 : Vertex)] := by decide
  have hg := other_cover q (25 : Vertex) (27 : Vertex) [(17 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause14 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 117 = true := by
  rw [value8, value117]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (26 : Vertex) w → w ∈ region → w ≠ (27 : Vertex) → w ∈ [] := by decide
  have hg := other_cover q (26 : Vertex) (27 : Vertex) [] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause15 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 118 = true ∨ valuation q 2 = true ∨ valuation q 8 = true := by
  rw [value2, value8, value9, value118]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (27 : Vertex) w → w ∈ region → w ≠ (25 : Vertex) → w ∈ [(11 : Vertex), (26 : Vertex)] := by decide
  have hg := other_cover q (27 : Vertex) (25 : Vertex) [(11 : Vertex), (26 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause16 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 3 = false ∨ valuation q 11 = false ∨ valuation q 19 = false := by
  rw [value3, value10, value11, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (45 : Vertex) (13 : Vertex) (109 : Vertex) (173 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause17 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 10 = true := by
  rw [value10, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (109 : Vertex) w → w ∈ region → w ∈ [(45 : Vertex)] := by decide
  have hg := neighbor_cover q (by decide) (109 : Vertex) [(45 : Vertex)] (fun w hw ha => hc w ha (h.covered w hw))
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause18 (q : Snake 81) (h : Conditions q) : valuation q 11 = true := by
  rw [value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  change InPath q head
  rw [← h.head_fixed]
  exact ⟨0,rfl⟩

theorem clause19 (q : Snake 81) (h : Conditions q) : valuation q 13 = false ∨ valuation q 122 = true ∨ valuation q 16 = true := by
  rw [value13, value16, value122]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (162 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(170 : Vertex)] := by decide
  have hg := other_cover q (162 : Vertex) (160 : Vertex) [(170 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause20 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 123 = true ∨ valuation q 15 = true ∨ valuation q 18 = true := by
  rw [value14, value15, value18, value123]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (164 : Vertex) w → w ∈ region → w ≠ (160 : Vertex) → w ∈ [(165 : Vertex), (172 : Vertex)] := by decide
  have hg := other_cover q (164 : Vertex) (160 : Vertex) [(165 : Vertex), (172 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause21 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 14 = false ∨ valuation q 19 = false ∨ valuation q 79 = false := by
  rw [value14, value15, value19, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (165 : Vertex) (164 : Vertex) (173 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause22 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 14 = false ∨ valuation q 21 = false ∨ valuation q 79 = false := by
  rw [value14, value15, value21, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (165 : Vertex) (164 : Vertex) (181 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause23 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 19 = false ∨ valuation q 21 = false ∨ valuation q 79 = false := by
  rw [value15, value19, value21, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (165 : Vertex) (173 : Vertex) (181 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause24 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 13 = false ∨ valuation q 17 = false ∨ valuation q 25 = false := by
  rw [value13, value16, value17, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (170 : Vertex) (162 : Vertex) (171 : Vertex) (186 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause25 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 16 = false ∨ valuation q 26 = false ∨ valuation q 80 = false := by
  rw [value16, value17, value26, value80]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (171 : Vertex) (170 : Vertex) (187 : Vertex) (427 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause26 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 14 = false ∨ valuation q 19 = false ∨ valuation q 81 = false := by
  rw [value14, value18, value19, value81]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (172 : Vertex) (164 : Vertex) (173 : Vertex) (428 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause27 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 10 = false ∨ valuation q 18 = false ∨ valuation q 82 = false := by
  rw [value10, value18, value19, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (173 : Vertex) (45 : Vertex) (172 : Vertex) (429 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause28 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 128 = true ∨ valuation q 15 = true ∨ valuation q 18 = true ∨ valuation q 82 = true := by
  rw [value15, value18, value19, value82, value128]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (173 : Vertex) w → w ∈ region → w ≠ (45 : Vertex) → w ∈ [(165 : Vertex), (172 : Vertex), (429 : Vertex)] := by decide
  have hg := other_cover q (173 : Vertex) (45 : Vertex) [(165 : Vertex), (172 : Vertex), (429 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause29 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 21 = false ∨ valuation q 24 = false ∨ valuation q 86 = false := by
  rw [value20, value21, value24, value86]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact BallClauseLogic.degree_clause q (177 : Vertex) (181 : Vertex) (185 : Vertex) (433 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause30 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 131 = true ∨ valuation q 89 = true := by
  rw [value22, value89, value131]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (182 : Vertex) w → w ∈ region → w ≠ (183 : Vertex) → w ∈ [(438 : Vertex)] := by decide
  have hg := other_cover q (182 : Vertex) (183 : Vertex) [(438 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause31 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 133 = true ∨ valuation q 26 = true := by
  rw [value24, value26, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (185 : Vertex) w → w ∈ region → w ≠ (177 : Vertex) → w ∈ [(187 : Vertex)] := by decide
  have hg := other_cover q (185 : Vertex) (177 : Vertex) [(187 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem clause32 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 133 = true ∨ valuation q 20 = true := by
  rw [value20, value24, value133]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have hc : ∀ w : Vertex, Adj (185 : Vertex) w → w ∈ region → w ≠ (187 : Vertex) → w ∈ [(177 : Vertex)] := by decide
  have hg := other_cover q (185 : Vertex) (187 : Vertex) [(177 : Vertex)] (fun w hw ha he => hc w ha (h.covered w hw) he)
  simpa only [List.mem_cons, List.mem_nil_iff, or_false, or_and_right, exists_or, exists_eq_left, false_and, exists_false] using hg

theorem block0 (q : Snake 81) (h : Conditions q) : B112E166.Block0 (valuation q) :=
  ⟨clause1 q h, clause2 q h, clause3 q h, clause4 q h, clause5 q h, clause6 q h, clause7 q h, clause8 q h, clause9 q h, clause10 q h, clause11 q h, clause12 q h, clause13 q h, clause14 q h, clause15 q h, clause16 q h, clause17 q h, clause18 q h, clause19 q h, clause20 q h, clause21 q h, clause22 q h, clause23 q h, clause24 q h, clause25 q h, clause26 q h, clause27 q h, clause28 q h, clause29 q h, clause30 q h, clause31 q h, clause32 q h⟩

end
end Snake9.Regrowth.E112166
